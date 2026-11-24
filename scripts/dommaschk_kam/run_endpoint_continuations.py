"""Resume six signed physical traces after the second radial trace, sharing one worker budget."""
import argparse
from contextlib import ExitStack
import fcntl
import os
from pathlib import Path
import subprocess
import sys
import time

from plan_endpoint_continuations import LABELS, checked_plan
from verify_endpoint_trace_campaign import read
from verify_mirror_physical_hit import admitted
from verify_native_action_campaign import cpus
from verify_physical_trace_slabs import HERE, RECORD, ROOT, digest, save
from verify_sparse_reference_slabs import GIB, available_ram


def accepted_prefix(path,label,length,checksum):
    report=read(path)
    if (report['endpoint'],report['length_each_direction'],report['packet_sha256'])!=(label,length,checksum):
        raise ValueError(f'wrong physical continuation at {path}')
    name=report['module']
    evidence=admitted(Path(report['proof_root']),name,report['key'])
    if 'PlasmaLean.Design.'+name+'.from_birth' not in evidence['theorems']:
        raise ValueError(f'missing signed birth at {path}')
    return report['key']


def occupied(campaign):
    campaign.mkdir(parents=True,exist_ok=True)
    with (campaign/'campaign.lock').open('a') as f:
        try:
            fcntl.flock(f,fcntl.LOCK_SH|fcntl.LOCK_NB)
        except BlockingIOError:
            return True
    return False


def allocation(labels,limit,epoch):
    quotas={e:0 for e in labels}
    if not labels:
        return quotas
    primaries=[e for e in labels if e.startswith('q0')]
    others=[e for e in labels if e.startswith('q1')]
    if others:
        k=epoch%len(others)
        others=others[k:]+others[:k]
    floors=primaries+others
    for e in floors[:limit]:
        quotas[e]+=1
    extra=limit-min(len(floors),limit)
    weighted=primaries*3+others
    for j in range(extra):
        quotas[weighted[j%len(weighted)]]+=1
    return quotas


def start(label,e,a,log):
    cmd=[sys.executable,HERE/'verify_endpoint_trace_campaign.py','--endpoint',label,'--length',str(e['target']),
        '--group-plan',a.plan,'--forward-launches',a.forward_launches,'--backward-launches',a.backward_launches,
        '--baseline','1','--workers',str(a.workers),'--workers-during-cells',str(a.workers),
        '--worker-leases',a.work/'leases.json','--prefix-lock',a.work/'long-prefix.lock',
        '--cache',a.campaign,'--reserve-gib',str(a.reserve_gib),'--reserve-cores',str(a.reserve_cores),
        '--output',a.work/(label+'.json')]
    if label.startswith('q0'):
        cmd.append('--native-residuals')
    return subprocess.Popen(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,
        env={**os.environ,'LEAN_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'})


def supervise(a,logs):
    data=read(a.plan)
    plan={e:checked_plan(data,e)[0] for e in a.endpoints}
    primary_packet=digest(RECORD.with_name('bounce_frame_q0_u478.json.gz'))
    while not a.primary_prefix.is_file():
        save(a.output,dict(state='waiting for 328 signed q0r478 slabs',primary=str(a.primary_prefix)))
        time.sleep(12)
    primary=accepted_prefix(a.primary_prefix,'q0r478',328,primary_packet)
    complete,running,attempts,errors={},{},{},{}
    ready=set(a.endpoints)
    previous=cpus()
    target=a.baseline
    windows=0
    epoch=0
    save(a.work/'leases.json',{})
    try:
        while len(complete)+len(errors)<len(a.endpoints):
            for e,child in list(running.items()):
                rc=child.poll()
                if rc is None:
                    continue
                del running[e]
                if rc and not occupied(a.campaign/e):
                    attempts[e]=attempts.get(e,0)+1
                    if attempts[e]>=2:
                        errors[e]=f'worker returned {rc}; inspect {a.work/(e+".log")}'
                        continue
                ready.add(e)
            for e in a.endpoints:
                if e not in ready:
                    continue
                spec=plan[e]
                path=a.campaign/e/'prefixes'/f'{spec["target"]:03}.json'
                if path.exists():
                    complete[e]=accepted_prefix(path,e,spec['target'],spec['packet_sha256'])
                    ready.remove(e)
                elif not occupied(a.campaign/e):
                    running[e]=start(e,spec,a,logs[e])
                    ready.remove(e)
            now=cpus()
            idle=(os.cpu_count() or 1)*(now[1]-previous[1])/max(1,now[0]-previous[0])
            previous=now
            windows=windows+1 if idle>=a.reserve_cores+1 else 0
            if windows>=3:
                target=min(a.workers,target+1)
                windows=0
            elif idle<a.reserve_cores:
                target=max(a.baseline,target-1)
            mem=available_ram()/GIB
            reports={e:read(a.work/(e+'.json')) for e in running if (a.work/(e+'.json')).exists()}
            busy=sum(len(d.get('active_jobs',[])) for d in reports.values())
            limit=min(target,busy+max(0,int((mem-a.reserve_gib)//7)))
            shares=allocation([e for e in a.endpoints if e in running],limit,epoch//20)
            save(a.work/'leases.json',shares)
            save(a.output,dict(state='complete' if len(complete)==len(a.endpoints) else 'running',
                 primary_key=primary,complete=complete,errors=errors,leases=shares,
                 targets={e:plan[e]['target'] for e in a.endpoints},existing_campaigns=sorted(ready),
                 active_workers=busy,idle_cores=round(idle,2),available_gib=round(mem,1),
                 prefixes={e:r.get('largest_signed_prefix',1) for e,r in reports.items()}))
            epoch+=1
            if len(complete)+len(errors)<len(a.endpoints):
                time.sleep(12)
    finally:
        save(a.work/'leases.json',{})
        for child in running.values():
            child.terminate()
        for child in running.values():
            child.wait()
    if errors:
        raise SystemExit(f'incomplete continuations: {errors}')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--plan',type=Path,required=True)
    p.add_argument('--endpoints',nargs='+',choices=LABELS,default=LABELS)
    p.add_argument('--primary-prefix',type=Path,
        default=ROOT/'.lake/secondary-trace-campaign/q0r478/prefixes/328.json')
    p.add_argument('--forward-launches',type=Path,required=True)
    p.add_argument('--backward-launches',type=Path,required=True)
    p.add_argument('--baseline',type=int,default=6)
    p.add_argument('--workers',type=int,default=10)
    p.add_argument('--reserve-cores',type=int,default=3)
    p.add_argument('--reserve-gib',type=int,default=36)
    p.add_argument('--campaign',type=Path,default=ROOT/'.lake/secondary-trace-campaign')
    p.add_argument('--work',type=Path,default=ROOT/'.lake/continuations-through-caps')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 1<=a.baseline<=a.workers or len(set(a.endpoints))!=len(a.endpoints) or min(a.reserve_cores,a.reserve_gib)<0:
        p.error('choose unique endpoints, a positive worker limit and nonnegative reserves')
    a.work=a.work.resolve()
    a.work.mkdir(parents=True,exist_ok=True)
    with ExitStack() as stack:
        lock=stack.enter_context((a.work/'campaign.lock').open('a'))
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        logs={e:stack.enter_context((a.work/(e+'.log')).open('a')) for e in a.endpoints}
        supervise(a,logs)


if __name__=='__main__':
    main()
