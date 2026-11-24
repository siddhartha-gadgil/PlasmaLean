"""Run the two-radius native profile certificates in a bounded, resumable workstation pool."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from verify_backward_physical_prefix import key_of
from verify_mirror_physical_hit import admitted
from verify_native_action_campaign import cpus
from verify_native_paired_profiles import THEORY
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import load
from verify_sparse_reference_slabs import GIB, available_ram


HERE = Path(__file__).resolve().parent
VERIFY = HERE/'verify_native_paired_profiles.py'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--range',type=int,nargs=2,default=(0,324),metavar=('FIRST','LAST'))
    p.add_argument('--workers',type=int,choices=range(1,13),default=2)
    p.add_argument('--baseline-workers',type=int,default=1,
                   help='minimum worker target, still subject to the available memory reserve')
    p.add_argument('--reserve-gib',type=int,default=32)
    p.add_argument('--reserve-cpus',type=int,default=2)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/native-paired-profiles')
    p.add_argument('--output',type=Path,required=True)
    a = p.parse_args()
    first,last = a.range
    if (not 0 <= first <= last <= 324 or a.reserve_gib < 0 or a.reserve_cpus < 0
            or not 1<=a.baseline_workers<=a.workers):
        p.error('invalid resource reserve or row interval')
    a.cache = a.cache.resolve()
    packets = [digest(load(r)[1]) for r in (470,478)]
    version = subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT,text=True).strip()
    inputs = [VERIFY,HERE/'verify_paired_action_profiles.py',HERE/'verify_native_action_models.py',
              HERE/'verify_centered_strength.py',DESIGN/(THEORY+'.trace')]
    key = key_of([packets,version,[digest(p) for p in inputs]])
    work = a.cache/'campaign'/key
    work.mkdir(parents=True,exist_ok=True)
    cases = list(range(first,last+1))
    # Pick up the lower-action producer's existing outer models first. Both programs use
    # the same locked, content-addressed model builder if they reach a row together.
    def ready(i):
        model = ROOT/'.lake/paired-action-profiles'/f'DommaschkNativeActionQ0R478Paired{i:03}'
        return any(model.glob('*/accepted.json'))
    pending = set(cases)
    records, errors, active = {}, {}, {}
    def validated(path,i):
        d = json.loads(path.read_text())
        if d['packets'] != packets or d['row'] != i or d['module'] != f'DommaschkNativePairedProfile{i:03}':
            raise ValueError(f'wrong native paired receipt {path}')
        admitted(Path(d['import_paths'][0]),d['module'],d['key'])
        return {'key':d['key'],'direct':d['direct'],'receipt':str(path)}
    for i in tuple(pending):
        path = work/f'{i:03}.json'
        if path.exists():
            records[i] = validated(path,i)
            pending.remove(i)
    def run(i):
        path = work/f'{i:03}.json'
        with (work/f'{i:03}.lock').open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            if not path.exists():
                with (work/f'{i:03}.log').open('w') as log:
                    subprocess.run([sys.executable,str(VERIFY),'--row',str(i),'--cache',str(a.cache),
                                    '--output',str(path)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
            return validated(path,i)
    idle, target, quiet = None, a.baseline_workers, 0
    previous, sampled = cpus(), time.monotonic()
    def report():
        save(a.output,dict(key=key,range=[first,last],packets=packets,complete=len(records)==len(cases),
                           accepted=len(records),direct=sum(r['direct'] for r in records.values()),
                           active=sorted(active.values()),target=target,idle_cpus=idle,
                           available_gib=round(available_ram()/GIB,1),errors=errors,
                           rows={i:records[i] for i in sorted(records)}))
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        while active or (pending and not errors):
            now = time.monotonic()
            if now-sampled >= 10:
                current = cpus()
                idle = round((os.cpu_count() or 1)*(current[1]-previous[1])/max(1,current[0]-previous[0]),2)
                previous,sampled = current,now
                quiet = quiet+1 if idle >= a.reserve_cpus+1 else 0
                if quiet >= 3:
                    target,quiet = min(a.workers,target+1),0
                elif idle < a.reserve_cpus:
                    target = max(a.baseline_workers,target-1)
            slots = max(0,min(target-len(active),int((available_ram()/GIB-a.reserve_gib)//6)))
            if slots and pending and not errors:
                # Action integration can finish a new outer model while this pool is running.
                # Prefer the now-cheap rows at each refill, and keep ascending order on ties.
                chosen = sorted(pending,key=lambda i:(not ready(i),i))[:slots]
                for i in chosen:
                    pending.remove(i)
                    active[pool.submit(run,i)] = i
            report()
            if not active:
                time.sleep(5)
                continue
            done,_ = wait(active,timeout=5,return_when=FIRST_COMPLETED)
            for job in done:
                i = active.pop(job)
                try:
                    records[i] = job.result()
                    print(i,records[i]['key'],flush=True)
                except (ValueError,OSError,subprocess.CalledProcessError) as exc:
                    errors[i] = f'{exc} (see {work}/{i:03}.log)'
    report()
    if errors:
        raise SystemExit('a native paired row failed')


if __name__=='__main__':
    main()
