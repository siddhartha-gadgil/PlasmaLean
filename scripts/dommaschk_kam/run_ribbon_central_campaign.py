"""Resume signed central proofs for all four radial ribbons, sharing spare workstation workers."""
import argparse
from concurrent.futures import FIRST_COMPLETED,ThreadPoolExecutor,wait
import fcntl
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from ribbon_central_data import LENGTH,WITNESS_SHA,load
from verify_native_action_campaign import cpus
from verify_physical_trace_slabs import HERE,ROOT,save
from verify_ribbon_central_group import authenticate
from verify_sparse_reference_slabs import GIB,available_ram


def planned(a):
    plan=json.loads(a.plan.read_text())
    if plan['witness']!=WITNESS_SHA or plan['length']!=LENGTH or set(plan['tiles'])!=set(map(str,range(4))):
        raise ValueError('the signed central plan covers a different witness or length')
    groups=[]
    for k in range(4):
        at=0
        for span in plan['tiles'][str(k)]:
            end=span['stop']
            if span['start']!=at or not at<end<=LENGTH or not 0<Fraction(span['ratio'])<=1:
                raise ValueError(f'incomplete central plan for ribbon {k}')
            groups.append((at,k,end))
            at=end
        if at!=LENGTH:
            raise ValueError(f'missing exterior continuation on radial ribbon {k}')
    return sorted(groups)


def row_path(root,k,i):
    return root/f'tile{k}'/'references'/f'{i:03}.json'


def complete_group(item,root,cache):
    a,k,b=item
    for i in range(a,b):
        path=row_path(root,k,i)
        if not path.exists():
            return False
        authenticate(json.loads(path.read_text()),k,i,cache)
    return True


def check(item,args):
    start,k,end=item
    work=args.root/f'tile{k}'/'groups'
    work.mkdir(parents=True,exist_ok=True)
    missing=[i for i in range(start,end) if not row_path(args.root,k,i).exists()]
    def run(indices):
        if not indices:
            return
        name=f'{start:03}-{end:03}-{indices[0]:03}-{indices[-1]+1:03}'
        log=work/(name+'.log')
        cmd=[sys.executable,HERE/'verify_ribbon_central_group.py','--ribbon',args.ribbon,'--tile',str(k),
            '--span',str(start),str(end),'--rows',*map(str,indices),'--handoff',args.root,
            '--output',work/(name+'.json')]
        with log.open('a') as f:
            rc=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,
                env={**os.environ,'LEAN_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}).returncode
        if rc and len(indices)>1:
            # A smaller source still uses the already checked physical fields on the full original group.
            mid=len(indices)//2
            run(indices[:mid])
            run(indices[mid:])
        elif rc:
            raise RuntimeError(f'tile {k} row {indices[0]} failed, see {log}')
    run(missing)


def campaign(args):
    load(args.ribbon)
    groups=planned(args)
    verified={}
    done={g for g in groups if complete_group(g,args.root,verified)}
    running,errors={},{}
    sample=cpus()
    then=time.monotonic()
    idle=None
    target=min(2,args.workers)
    windows=0
    output=args.output or args.root/'status.json'
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while True:
            now=time.monotonic()
            if now-then>=8:
                after=cpus()
                idle=(os.cpu_count() or 1)*(after[1]-sample[1])/max(1,after[0]-sample[0])
                sample,then=after,now
                windows=windows+1 if idle>=args.reserve_cores+1 else 0
                if windows>=3:
                    target=min(args.workers,target+1)
                    windows=0
                elif idle<args.reserve_cores:
                    target=max(1,target-1)
            warm={k for k in args.wait_ground if subprocess.run(
                ['systemctl','--user','is-active','--quiet',f'plasmalean-n173-ground-tile{k}.service']).returncode==0}
            slots=min(max(0,target-len(warm)-len(running)),max(0,int((available_ram()/GIB-args.reserve_gib)//7)))
            for g in groups:
                if g in done or g in running.values() or g in errors:
                    continue
                start,k,end=g
                if start==0 and k in warm:
                    continue
                if complete_group(g,args.root,verified):
                    done.add(g)
                elif slots>0:
                    running[pool.submit(check,g,args)]=g
                    slots-=1
            pairs={k:sum(b-a for a,t,b in done if t==k) for k in range(4)}
            status=dict(witness=WITNESS_SHA,length=LENGTH,groups=len(groups),accepted_groups=len(done),
                accepted_row_pairs=pairs,active=list(running.values()),warm_tiles=sorted(warm),
                errors={str(k):v for k,v in errors.items()},complete=len(done)==len(groups),
                worker_target=target,idle_cores=None if idle is None else round(idle,2),
                available_gib=round(available_ram()/GIB,1))
            save(output,status)
            if len(done)==len(groups):
                return
            if not running and not warm and len(done)+len(errors)==len(groups):
                raise RuntimeError('some ribbon proofs failed; see the recorded group and row logs')
            if running:
                finished,_=wait(running,timeout=9,return_when=FIRST_COMPLETED)
                for f in finished:
                    g=running.pop(f)
                    try:
                        f.result()
                        if not complete_group(g,args.root,verified):
                            raise ValueError('group completed without both original signed claims')
                        done.add(g)
                    except Exception as exc:
                        errors[g]=str(exc)
            else:
                time.sleep(8)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--plan',type=Path,required=True)
    p.add_argument('--root',type=Path,default=ROOT/'.lake/ribbon-central-campaign')
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--reserve-cores',type=int,default=3)
    p.add_argument('--reserve-gib',type=int,default=40)
    p.add_argument('--wait-ground',type=int,choices=range(4),nargs='*',default=[])
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    if a.workers<1 or a.reserve_cores<0 or a.reserve_gib<0:
        p.error('choose a positive worker limit and nonnegative system reserves')
    a.root=a.root.resolve()
    a.ribbon=a.ribbon.resolve()
    a.root.mkdir(parents=True,exist_ok=True)
    with (a.root/'manager.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        campaign(a)


if __name__=='__main__':
    main()
