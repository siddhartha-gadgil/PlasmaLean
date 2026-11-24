"""Check independent physical ODE steps as soon as their two analytic parents are ready."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
import os
from pathlib import Path
import subprocess
import sys
import time

from verify_endpoint_reference_slabs import ENDPOINTS
from verify_endpoint_trace_campaign import read, records_for, row_path
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import HERE, RECORD, ROOT, digest, save
from verify_sparse_reference_slabs import GIB, available_ram


def authenticate(path, i, label, checksum, references, jacobians):
    report = read(path)
    if len(report) != 2 or {r['direction'] for r in report} != {-1,1}:
        raise ValueError(f'missing a physical time direction on row {i}')
    for row in report:
        sign = row['direction']
        name = f'DommaschkPhysical{label.upper()}{"Forward" if sign==1 else "Back"}{i:03}'
        if (row['index'],row['endpoint'],row['packet_sha256'],row['module']) != (i,label,checksum,name):
            raise ValueError(f'incorrect physical endpoint, packet, or index on row {i}')
        jac = next(r for r in jacobians if r.get('matrix_direction',sign)==sign)
        ref = next(r for r in references if r['direction']==sign)
        if (row['jacobian_key'],row['residual_key']) != (jac['key'],ref['key']):
            raise ValueError(f'physical step used different analytic parents on row {i}')
        witness = admitted(Path(row['import_paths'][0]),name,row['key'])
        claims = ['PlasmaLean.Design.'+name+'.'+p for p in ('checked','field_bounds','physical_step')]
        if witness['theorems'] != claims or row['theorems'] != claims:
            raise ValueError(f'incomplete physical ODE proof for row {i}')
    return [r['key'] for r in report]


def check(i, a):
    ref,jac = [row_path(a.campaign,k,i) for k in ('references','jacobians')]
    refs = records_for(ref,'references',a.endpoint,a.checksum)[i]
    jacs = records_for(jac,'jacobians',a.endpoint,a.checksum)[i]
    path = a.cache/f'{i:03}.json'
    current = {(j['key'],r['key']) for j in jacs for r in refs
               if j.get('matrix_direction',r['direction'])==r['direction']}
    if (not path.exists() or
            {(w['jacobian_key'],w['residual_key']) for w in read(path)} != current):
        cmd = [sys.executable,HERE/'verify_endpoint_signed_prefix.py','--endpoint',a.endpoint,
               '--row',str(i),'--references',ref,'--jacobians',jac,'--output',path]
        with path.with_suffix('.log').open('a') as log:
            subprocess.run(cmd,cwd=ROOT,check=True,stdout=log,stderr=subprocess.STDOUT,
                env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','LEAN_NUM_THREADS':'1'})
    return authenticate(path,i,a.endpoint,a.checksum,refs,jacs)


def campaign(a):
    first,stop = a.range
    remaining = set(range(first,stop))
    pending, accepted = {}, {}
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        while remaining or pending:
            slots = min(a.workers-len(pending),max(0,int((available_ram()/GIB-a.reserve_gib)//6)))
            ready = sorted(i for i in remaining if all(row_path(a.campaign,k,i).is_file()
                                                       for k in ('jacobians','references')))
            for i in ready[:slots]:
                remaining.remove(i)
                pending[pool.submit(check,i,a)] = i
            if pending:
                done,_ = wait(pending,timeout=10,return_when=FIRST_COMPLETED)
                for task in done:
                    i = pending.pop(task)
                    accepted[i]=task.result()
                    print(f'{a.endpoint} {i} both physical steps accepted ({len(accepted)}/{stop-first})',
                          flush=True)
                    save(a.output,dict(endpoint=a.endpoint,packet_sha256=a.checksum,start=first,
                         stop=stop,accepted=len(accepted),complete=len(accepted)==stop-first,
                         rows={str(j):accepted[j] for j in sorted(accepted)}))
            elif remaining:
                if not a.wait and not ready:
                    break
                time.sleep(10)
    return len(accepted)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=ENDPOINTS[1:],required=True)
    p.add_argument('--range',nargs=2,type=int,required=True,metavar=('FIRST','STOP'))
    p.add_argument('--workers',type=int,default=1)
    p.add_argument('--reserve-gib',type=int,default=32)
    p.add_argument('--campaign',type=Path,default=ROOT/'.lake/secondary-trace-campaign')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-physical-step-receipts')
    p.add_argument('--wait',action='store_true',help='wait for both analytic parents on every original row')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not (1<=a.range[0]<a.range[1]<=391 and a.workers>=1 and a.reserve_gib>=0):
        p.error('choose original rows in [1,391) and positive worker count')
    a.cache=a.cache.resolve()/a.endpoint
    a.cache.mkdir(parents=True,exist_ok=True)
    a.campaign=a.campaign.resolve()/a.endpoint
    a.checksum=digest(RECORD.with_name(f'bounce_frame_{a.endpoint[:2]}_u{a.endpoint[3:]}.json.gz'))
    status=read(a.campaign/'status.json')
    if status['endpoint']!=a.endpoint or status['packet_sha256']!=a.checksum:
        p.error('the physical trace campaign uses a different endpoint or packet')
    with (a.cache/f'{a.range[0]:03}-{a.range[1]:03}.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        count=campaign(a)
    if count!=a.range[1]-a.range[0]:
        raise SystemExit(f'{count} complete; remaining rows still require analytic parents')


if __name__=='__main__':
    main()
