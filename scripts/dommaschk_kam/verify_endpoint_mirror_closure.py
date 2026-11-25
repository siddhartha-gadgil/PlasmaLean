"""Join the original two-clock endpoint trace directly to its certified first-mirror band."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from plan_endpoint_continuations import checked_plan
from run_endpoint_continuations import accepted_prefix
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import HERE, ROOT, save


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--endpoint",choices=("q0r523","q0r531"),required=True)
    p.add_argument("--plan",required=True,type=Path)
    p.add_argument("--campaign",type=Path,default=ROOT/".lake/secondary-trace-campaign")
    p.add_argument("--work",type=Path,default=ROOT/".lake/continuations-through-caps")
    p.add_argument("--forward-launches",type=Path,required=True)
    p.add_argument("--backward-launches",type=Path,required=True)
    p.add_argument("--caps",required=True,type=Path)
    p.add_argument("--exclusion",required=True,type=Path)
    p.add_argument("--slopes",required=True,type=Path)
    p.add_argument("--workers",type=int,default=2)
    p.add_argument("--wait",action="store_true")
    p.add_argument("--output",required=True,type=Path)
    args=p.parse_args()
    if args.workers<1:
        p.error("use at least one worker")
    endpoint=args.endpoint
    spec,_=checked_plan(json.loads(args.plan.read_text()),endpoint)
    cap=spec["target"]
    campaign=args.campaign/endpoint
    work=args.work/endpoint/"terminal"
    work.mkdir(exist_ok=True,parents=True)
    env={**os.environ,"OPENBLAS_NUM_THREADS":"1","OMP_NUM_THREADS":"1","LEAN_NUM_THREADS":"1"}
    def run(script,arguments,log):
        with log.open("a") as stream:
            subprocess.run([sys.executable,HERE/script,*map(str,arguments)],cwd=ROOT,env=env,
                           stdout=stream,stderr=subprocess.STDOUT,check=True)
    def paths(stage,indices):
        return [campaign/stage/f"{i:03}.json" for i in indices]
    rows=range(1,cap)
    required=paths("references",rows)+paths("jacobians",rows)
    while not all(path.is_file() for path in required):
        if not args.wait:
            p.error("both original spatial and central signed receipts are needed on every row")
        time.sleep(15)
    prefix=campaign/"prefixes"/f"{cap:03}.json"
    if not prefix.exists():
        earlier=max([1,*[int(f.stem) for f in (campaign/"prefixes").glob("[0-9]*.json")
                          if int(f.stem)<cap]])
        if earlier>1:
            accepted_prefix(campaign/"prefixes"/f"{earlier:03}.json",endpoint,earlier,spec["packet_sha256"])
        def warm(i):
            output=work/f"steps{i:03}.json"
            run("verify_endpoint_signed_prefix.py",["--endpoint",endpoint,"--row",i,"--references",
                *paths("references",[i]),"--jacobians",*paths("jacobians",[i]),"--output",output],
                work/f"steps{i:03}.log")
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            # The normal ongoing prefix reaches the near end first. Independent workers start at the far end.
            list(pool.map(warm,reversed(range(earlier,cap))))
        with (args.work/"long-prefix.lock").open("a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            if not prefix.exists():
                run("verify_endpoint_signed_prefix.py",["--endpoint",endpoint,"--length",cap,
                    "--forward-launches",args.forward_launches,"--backward-launches",args.backward_launches,
                    "--references",*paths("references",rows),"--jacobians",*paths("jacobians",rows),
                    "--output",prefix],work/"cap-prefix.log")
    key=accepted_prefix(prefix,endpoint,cap,spec["packet_sha256"])
    band=work/"physical-band.json"
    run("verify_secondary_mirror_band.py",["--launch",int(endpoint[3:]),"--caps",args.caps,
        "--exclusion",args.exclusion,"--slopes",args.slopes,"--signed",prefix,"--output",band],
        work/"physical-band.log")
    result=json.loads(band.read_text())
    birth=result["physical_birth"]
    if (birth["parents"]!=[result["key"],key] or birth["signed_length"]!=cap or
            result["packet_sha256"]!=spec["packet_sha256"]):
        raise ValueError("the physical mirror birth differs from its signed endpoint trace")
    proof=admitted(Path(birth["import_paths"][0]),birth["module"],birth["key"])
    if not any(t.endswith(".from_birth") for t in proof["theorems"]):
        raise ValueError("the certified signed first-mirror branches lack a physical birth")
    save(args.output,result)
    print(endpoint,cap,key,birth["key"],flush=True)


if __name__=="__main__":
    main()
