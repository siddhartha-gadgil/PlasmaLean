"""Run the two ribbon proof producers and their physical assembly under one workstation budget."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import ExitStack
import fcntl
import json
import os
from pathlib import Path
import time

from ribbon_central_data import LENGTH, WITNESS_SHA, load
import run_ribbon_central_campaign as central
import run_ribbon_physical_campaign as physical
from verify_native_action_campaign import cpus
from verify_physical_trace_slabs import ROOT, digest, save
from verify_sparse_reference_slabs import GIB, available_ram


def central_key(job):
    _, (tile,), a, b = job
    return a,tile,b


def done(job, args, context, checked):
    if job[0] == "central":
        return central.complete_group(central_key(job),context.root,checked["central"])
    return physical.complete(job,args,checked["physical"])


def run(job, args, context):
    if job[0] == "central":
        central.check(central_key(job),context)
    else:
        physical.run(job,args)


def fronts(jobs, kind):
    covered = [set() for _ in range(4)]
    for stage,tiles,a,b in jobs:
        if stage == kind:
            for tile in tiles:
                covered[tile].update(range(a,b))
    return [next((i for i in range(LENGTH) if i not in row),LENGTH) for row in covered]


def select_job(remaining, running, finished, args, capacity):
    """First close ready IVPs, then feed the slower side of the same four physical chains."""
    held = set(running)
    local = sorted((j for j in remaining if j[0] == "physical" and physical.ready(j,args)),
                   key=lambda j:(j[2],j[1]))
    if local and (sum(j[0]=="physical" for j in held) < max(1,capacity//4) or len(local)==len(remaining)):
        return local[0]
    jets = sorted((j for j in remaining if j[0]=="spatial"),key=lambda j:(j[2],j[1]))
    defects = sorted((j for j in remaining if j[0]=="central"),key=lambda j:(j[2],j[1]))
    # Include active claims when allocating another worker. An in-flight jet never admits an IVP.
    reserved = finished | held
    fc,fs = fronts(reserved,"central"),fronts(reserved,"spatial")
    if jets and defects:
        first = jets[0]
        lead = min(fs[k]-fc[k] for k in first[1])
        if lead <= args.spatial_lead:
            return first
        return defects[0]
    return next(iter(defects or jets or local),None)


def campaign(args):
    load(args.ribbon)
    context = argparse.Namespace(root=args.central,plan=args.central_plan,ribbon=args.ribbon)
    cplan = central.planned(context)
    pplan = physical.work(json.loads(args.plan.read_text()))
    jobs = set(pplan) | {("central",(k,),a,b) for a,k,b in cplan}
    checked = {"central": {}, "physical": {}}
    finished = {j for j in jobs if done(j,args,context,checked)}
    failed,running = {},{}
    ticks,now = cpus(),time.monotonic()
    target = min(args.initial_workers,args.workers)
    spare = busy = 0
    idle = None
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while True:
            elapsed = time.monotonic()-now
            if elapsed >= 20:
                t = cpus()
                idle = len(os.sched_getaffinity(0))*(t[1]-ticks[1])/max(1,t[0]-ticks[0])
                ticks,now = t,time.monotonic()
                spare = (spare+1) if idle>=args.reserve_cores+1 else 0
                busy = (busy+1) if idle<args.reserve_cores else 0
                if spare>=2:
                    target,spare = min(args.workers,target+1),0
                elif busy>=2:
                    target,busy = max(1,target-1),0
            available = available_ram()/GIB
            slots = min(max(0,target-len(running)),max(0,int((available-args.reserve_gib)//8)))
            active = {j for j,_ in running.values()}
            for _ in range(slots):
                other = jobs-finished-active-failed.keys()
                j = select_job(other,active,finished,args,target)
                if j is None:
                    break
                if done(j,args,context,checked):
                    finished.add(j)
                else:
                    active.add(j)
                    running[pool.submit(run,j,args,context)] = j,time.monotonic()
            errors = {str(j):msg for j,msg in failed.items()}
            sums = {kind:sum(len(tiles)*(b-a) for m,tiles,a,b in finished if m==kind)
                    for kind in ("central","spatial","physical")}
            complete = len(finished)==len(jobs)
            state = dict(witness=WITNESS_SHA,length=LENGTH,signed_steps=2*sums["physical"],
                         shared_spatial_rows=sums["spatial"],accepted_central_pairs=sums["central"],
                         active=sorted(active),errors=errors,target_workers=target,
                         idle_cores=None if idle is None else round(idle,2),available_gib=round(available,2),
                         complete=complete)
            save(args.output,state)
            save(args.root/"status.json",state | {"active":[j for j in sorted(active) if j[0]!="central"]})
            cs = {k:sum(b-a for st,ks,a,b in finished if st=="central" and k in ks) for k in range(4)}
            save(args.central_status,dict(witness=WITNESS_SHA,length=LENGTH,groups=len(cplan),
                accepted_groups=sum(j[0]=="central" for j in finished),accepted_row_pairs=cs,
                active=[central_key(j) for j in sorted(active) if j[0]=="central"],
                warm_tiles=[],errors={str(j):s for j,s in failed.items() if j[0]=="central"},
                worker_target=target,idle_cores=state["idle_cores"],available_gib=state["available_gib"],
                complete=sums["central"]==4*LENGTH))
            if complete:
                return
            if not running:
                if failed:
                    raise RuntimeError(f"unresolved original ribbon certificates: {errors}")
                time.sleep(5)
                continue
            results,_ = wait(running,timeout=5,return_when=FIRST_COMPLETED)
            for future in results:
                job,start = running.pop(future)
                try:
                    future.result()
                    if not done(job,args,context,checked):
                        raise ValueError("missing original signed physical declarations")
                    finished.add(job)
                    log = {"stage":job[0],"tiles":job[1],"span":job[2:],"completed":time.time(),
                           "wall_seconds":round(time.monotonic()-start,3)}
                    with (args.output.parent/"balanced-receipts.jsonl").open("a") as out:
                        print(json.dumps(log),file=out)
                except Exception as exc:
                    failed[job]=str(exc)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ribbon",required=True,type=Path)
    parser.add_argument("--packets",required=True,type=Path)
    parser.add_argument("--plan",required=True,type=Path,help="authenticated spatial group plan")
    parser.add_argument("--central-plan",required=True,type=Path)
    parser.add_argument("--central",type=Path,default=ROOT/".lake/ribbon-central-campaign")
    parser.add_argument("--central-status",type=Path,required=True)
    parser.add_argument("--root",type=Path,default=ROOT/".lake/ribbon-through-campaign")
    parser.add_argument("--spatial",type=Path,default=ROOT/".lake/ribbon-spatial-campaign")
    parser.add_argument("--physical",type=Path,default=ROOT/".lake/ribbon-physical-campaign")
    parser.add_argument("--output",type=Path,default=ROOT/".lake/ribbon-balanced-campaign/status.json")
    parser.add_argument("--workers",type=int,default=8)
    parser.add_argument("--initial-workers",type=int,default=6)
    parser.add_argument("--reserve-cores",type=float,default=2)
    parser.add_argument("--reserve-gib",type=int,default=40)
    parser.add_argument("--spatial-lead",type=int,default=12)
    parser.add_argument("--dyadic-from",type=int,default=22)
    parser.add_argument("--integer-frame-from",type=int,default=56)
    args = parser.parse_args()
    if (not 1<=args.initial_workers<=args.workers or
            min(args.reserve_cores,args.reserve_gib,args.spatial_lead) < 0 or digest(args.ribbon)!=WITNESS_SHA):
        parser.error("expected positive worker counts, nonnegative reserves and the original ribbon")
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with ExitStack() as stack:
        for directory in sorted([args.central,args.root]):
            directory.mkdir(parents=True,exist_ok=True)
            lock = stack.enter_context((directory/"manager.lock").open("a"))
            fcntl.flock(lock,fcntl.LOCK_EX)
        campaign(args)


if __name__=="__main__":
    main()
