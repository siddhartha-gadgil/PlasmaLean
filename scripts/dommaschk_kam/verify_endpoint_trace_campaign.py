"""Resume a whole secondary endpoint trace, checking signed birth passages at selected lengths."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import ExitStack
import fcntl
import glob
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from verify_endpoint_reference_slabs import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_native_action_campaign import cpus
from verify_physical_trace_slabs import RECORD, ROOT, digest, save
from verify_sparse_reference_slabs import GIB, available_ram


HERE = Path(__file__).resolve().parent
STAGES = ('jacobians','references')
CHECKPOINTS = (2,4,5,6,8,12,16,24,32,48,64,96,128,160,192,224,256,288,317,318,325,327,328,391)


def read(path):
    return json.loads(path.read_text())


def active_unit(unit):
    return subprocess.run(['systemctl','--user','is-active','--quiet',unit]).returncode == 0


def row_path(cache, stage, i):
    return cache/stage/f'{i:03}.json'


def records_for(path, stage, label, checksum):
    obj = read(path)
    if not isinstance(obj,list):
        obj = [obj]
    by_index = {}
    seen = set()
    for row in obj:
        if row['endpoint'] != label:
            continue
        i, direction = row['index'],row['direction']
        matrix = row.get('matrix_direction') if stage == 'jacobians' else direction
        if (row['packet_sha256'] != checksum or not 0 <= i <= 390 or direction not in (-1,1)
                or matrix not in (None, 1, -1) or (i,matrix) in seen):
            raise ValueError(f'wrong or repeated packet row in {path}')
        seen.add((i,matrix))
        if stage == 'jacobians':
            tag = {None: 'PairedForward', 1: 'IndependentForward', -1: 'IndependentBack'}[matrix]
            name = f'DommaschkJacobian{label.upper()}{tag}{i:03}'
            if direction != 1 or not row.get('paired_trials'):
                raise ValueError(f'missing two-clock spatial data in {path}')
        else:
            tag = 'Forward' if direction == 1 else 'Back'
            name = f'DommaschkTraceResidual{label.upper()}{tag}{i:03}'
        root, = map(Path,row['import_paths'])
        if name != row['module'] or admitted(root,name,row['key'])['theorems'] != row['theorems']:
            raise ValueError(f'wrong proof for {label} in {path}')
        by_index.setdefault(i,[]).append(row)
    if stage == 'jacobians':
        return {i: rows for i, rows in by_index.items()
                if {r.get('matrix_direction') for r in rows} in ({None}, {-1, 1})}
    return {i: rows for i, rows in by_index.items() if {r['direction'] for r in rows} == {-1, 1}}


def residual_method(args):
    if args.native_residuals or (args.cache/'use-native-residuals').exists():
        return 'native-horner'
    if args.reflected_residuals or (args.cache/'use-reflected-residuals').exists():
        return 'reflected'
    return 'both-signed'


def produce(args, stage, i):
    path = row_path(args.cache,stage,i)
    py = sys.executable
    if stage=='grouped-jacobians':
        start,stop=args.groups[i]
        missing=[j for j in range(max(1,start),min(stop,args.length))
                 if not row_path(args.cache,'jacobians',j).exists()]
        if not missing:
            return None
        cmd=[py,HERE/'verify_grouped_endpoint_jacobians.py','--endpoint',args.endpoint,
             '--span',str(start),str(stop),'--rows',*map(str,missing),'--handoff',args.cache,'--output',path]
    elif stage=='references':
        method = residual_method(args)
        if method in ('native-horner','reflected'):
            script = ('verify_native_endpoint_residuals.py' if method == 'native-horner'
                      else 'verify_reflected_endpoint_residuals.py')
            cmd = [py, HERE/script, '--endpoint', args.endpoint, '--row', str(i), '--output', path]
        else:
            cmd=[py,HERE/'verify_endpoint_reference_slabs.py','--endpoints',args.endpoint,
                 '--range',str(i),str(i),'--workers','1','--shared','--output',path]
    elif stage=='jacobians':
        cmd=[py,HERE/'verify_horner_endpoint_jacobian.py','--endpoints',args.endpoint,
             '--row',str(i),'--output',path]
        if args.endpoint.startswith('q1'):
            cmd.append('--independent-frames')
    else:
        cmd=[py,HERE/'verify_endpoint_signed_prefix.py','--endpoint',args.endpoint,'--length',str(i),
             '--forward-launches',args.forward_launches,'--backward-launches',args.backward_launches,
             '--references',*[row_path(args.cache,'references',j) for j in range(1,i)],
             '--jacobians',*[row_path(args.cache,'jacobians',j) for j in range(1,i)],'--output',path]
    log = path.with_suffix('.log')
    with ExitStack() as stack:
        if stage=='prefixes' and i>=128 and args.prefix_lock:
            gate=stack.enter_context(args.prefix_lock.open('a'))
            fcntl.flock(gate,fcntl.LOCK_EX)
        out=stack.enter_context(log.open('a'))
        result=subprocess.run(cmd,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,
                              env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','LEAN_NUM_THREADS':'1'})
    if result.returncode:
        raise RuntimeError(f'{log}: {log.read_text()[-850:]}')
    if stage=='grouped-jacobians':
        spatial=records_for(path,'jacobians',args.endpoint,args.checksum)
        if set(spatial)!=set(missing) or any(
                j not in records_for(row_path(args.cache,'jacobians',j),'jacobians',args.endpoint,args.checksum)
                for j in missing):
            raise ValueError(f'incomplete on-disk handoff of grouped interval {i} at {path}')
    elif stage=='prefixes':
        receipt=read(path)
        if receipt['endpoint'] != args.endpoint or receipt['length_each_direction'] != i:
            raise ValueError(f'wrong physical checkpoint at {path}')
        admitted(Path(receipt['proof_root']),receipt['module'],receipt['key'])
    elif i not in records_for(path,stage,args.endpoint,args.checksum):
        raise ValueError(f'missing {stage} on {args.endpoint} row {i}')
    return path


def campaign(a):
    stages={s:set() for s in STAGES}
    prefixes={}
    checked_files={}
    checkpoints=sorted({n for n in a.checkpoint if 2<=n<=a.length}|{a.length})
    running,errors,attempts={}, {}, {}
    fallback_groups={}
    for stage in [*STAGES,'prefixes',*(['grouped-jacobians'] if a.groups else [])]:
        (a.cache/stage).mkdir(parents=True,exist_ok=True)
    for path in sorted((a.cache/'prefixes').glob('*.json')):
        r=read(path)
        if r['endpoint']!=a.endpoint or r['packet_sha256']!=a.checksum:
            raise ValueError(f'wrong endpoint checkpoint: {path}')
        admitted(Path(r['proof_root']),r['module'],r['key'])
        prefixes[r['length_each_direction']]=r['key']
    patterns={s:[str(a.cache/s/'*.json'),*getattr(a,s+'_input')] for s in STAGES}
    def ingest():
        for stage in STAGES:
            for pattern in patterns[stage]:
                for filename in glob.iglob(pattern):
                    path=Path(filename)
                    stamp=path.stat().st_mtime_ns
                    if checked_files.get((stage,path))==stamp:
                        continue
                    for i,rows in records_for(path,stage,a.endpoint,a.checksum).items():
                        if i==0 or i>=a.length or i in stages[stage]:
                            continue
                        target=row_path(a.cache,stage,i)
                        if target != path and not target.is_file():
                            save(target,rows)
                        stages[stage].add(i)
                    checked_files[stage,path]=stamp
    now=time.monotonic()
    last_sample, last_raise, last_ingest=now,now,0
    before=cpus()
    target=a.baseline
    idle=None
    external=0
    deferred=False
    idle_windows=0
    def status():
        data={'endpoint':a.endpoint,'packet_sha256':a.checksum,'target_length_each_way':a.length,
              'complete':a.length in prefixes,'largest_signed_prefix':max(prefixes,default=1),
              'residual_method':residual_method(a),
              'checkpoints':prefixes,'rows_with_both_residuals':len(stages['references']),
              'rows_with_both_spatial_bounds':len(stages['jacobians']),
              'active_jobs':sorted(running.values()),'other_endpoint_workers':external,
              'idle_cores':idle,'available_gib':round(available_ram()/GIB,1),
              'worker_target':target,'errors':{f'{s}{i:03}':v for (s,i),v in errors.items()}}
        if a.groups:
            data['grouped_spatial_fallbacks']=fallback_groups
        save(a.cache/'status.json',data)
        save(a.output,data)
    def next_job():
        busy=set(running.values())
        joint=stages['references']&stages['jacobians']
        for n in checkpoints:
            job=('prefixes',n)
            if n not in prefixes and job not in busy and job not in errors and all(i in joint for i in range(1,n)):
                if not any(s=='prefixes' for s,_ in busy):
                    return job
        for i in range(1,a.length):
            if deferred and i<a.defer_before:
                continue
            for s in STAGES:
                job=(s,i)
                if s=='references' and a.defer_reference==i and a.reference_unit and active_unit(a.reference_unit):
                    continue
                if s=='jacobians' and i in a.groups and a.groups[i][0] not in fallback_groups:
                    job=('grouped-jacobians',a.groups[i][0])
                if i not in stages[s] and job not in busy and job not in errors:
                    return job
        return None
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        if a.groups:
            status()
        while a.length not in prefixes:
            now=time.monotonic()
            if now-last_ingest>=20:
                ingest()
                last_ingest=now
                external=sum(active_unit(u) for u in a.other_worker_unit)
                deferred=bool(a.defer_unit and active_unit(a.defer_unit))
            if now-last_sample>=12:
                after=cpus()
                idle=round((os.cpu_count() or 1)*(after[1]-before[1])/max(1,after[0]-before[0]),2)
                before,last_sample=after,now
                idle_windows=idle_windows+1 if idle>=a.reserve_cores+1 else 0
                cap=a.workers
                if a.cells_progress:
                    cells=read(a.cells_progress) if a.cells_progress.exists() else {}
                    if not cells.get('complete') or cells.get('accepted_pairs',0)<325:
                        cap=min(cap,a.workers_during_cells)
                if idle_windows>=3 and now-last_raise>=36:
                    target=min(cap,target+1)
                    last_raise=now
                elif idle<a.reserve_cores:
                    target=max(a.baseline,target-1)
                target=min(target,cap)
            allowance=max(1,target-external)
            if a.worker_leases:
                target=max(0,min(a.workers,read(a.worker_leases).get(a.endpoint,0)))
                allowance=max(0,target-external)
            slots=max(0,min(allowance-len(running),
                            int((available_ram()/GIB-a.reserve_gib)//6)))
            if (a.cache/'drain').exists():
                slots=0
                if not running:
                    status()
                    print('Drained active certificate checks.',flush=True)
                    return
            for _ in range(slots):
                job=next_job()
                if not job:
                    break
                running[pool.submit(produce,a,*job)]=job
            status()
            if not running:
                if errors and next_job() is None and not deferred:
                    break
                time.sleep(5)
                continue
            done,_=wait(running,timeout=5,return_when=FIRST_COMPLETED)
            for task in done:
                s,i=job=running.pop(task)
                try:
                    path=task.result()
                    if s=='prefixes':
                        prefixes[i]=read(path)['key']
                        print(f'{a.endpoint} {i} signed slabs each way: {prefixes[i]}',flush=True)
                    elif s=='grouped-jacobians':
                        if path is not None:
                            stages['jacobians'].update(records_for(path,'jacobians',a.endpoint,a.checksum))
                        ingest()
                    else:
                        stages[s].add(i)
                except Exception as exc:
                    attempts[job]=attempts.get(job,0)+1
                    if attempts[job]>=2:
                        if s=='grouped-jacobians':
                            fallback_groups[i]=str(exc)
                        else:
                            errors[job]=str(exc)
                    print(f'{s} {i} attempt {attempts[job]}: {exc}',flush=True)
            if len(errors)>=3:
                break
    status()
    if a.length not in prefixes:
        raise SystemExit('incomplete: see campaign status and the per-stage logs')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=ENDPOINTS[1:],required=True)
    p.add_argument('--length',type=int,default=328)
    p.add_argument('--checkpoint',type=int,nargs='*',default=CHECKPOINTS)
    p.add_argument('--forward-launches',type=Path,required=True)
    p.add_argument('--backward-launches',type=Path,required=True)
    p.add_argument('--references-input',nargs='*',default=[])
    method = p.add_mutually_exclusive_group()
    method.add_argument('--reflected-residuals',action='store_true')
    method.add_argument('--native-residuals',action='store_true',
                        help='use the seven-harmonic central jet on the phase-zero reference')
    p.add_argument('--jacobians-input',nargs='*',default=[])
    p.add_argument('--group-plan',type=Path,help='adaptive projected trial rectangles from plan_endpoint_continuations.py')
    p.add_argument('--baseline',type=int,default=2)
    p.add_argument('--workers',type=int,default=8)
    p.add_argument('--worker-leases',type=Path,help='external shared worker allocation by endpoint')
    p.add_argument('--prefix-lock',type=Path,help='serialize long chain joins across independent endpoints')
    p.add_argument('--workers-during-cells',type=int,default=4)
    p.add_argument('--cells-progress',type=Path)
    p.add_argument('--reserve-cores',type=int,default=2)
    p.add_argument('--reserve-gib',type=int,default=32)
    p.add_argument('--other-worker-unit',action='append',default=[])
    p.add_argument('--defer-before',type=int,default=0)
    p.add_argument('--defer-unit')
    p.add_argument('--defer-reference',type=int)
    p.add_argument('--reference-unit')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-trace-campaign')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 2<=a.length<=391 or not 1<=a.baseline<=a.workers_during_cells<=a.workers:
        p.error('require length 2–391 and baseline ≤ during-cells limit ≤ workers')
    if (a.reflected_residuals or a.native_residuals) and not a.endpoint.startswith('q0'):
        p.error('shared signed central residuals require a phase-zero endpoint')
    a.cache=a.cache.resolve()/a.endpoint
    a.cache.mkdir(parents=True,exist_ok=True)
    a.checksum=digest(RECORD.with_name(f'bounce_frame_{a.endpoint[:2]}_u{a.endpoint[3:]}.json.gz'))
    a.groups={}
    if a.group_plan:
        from plan_endpoint_continuations import checked_plan
        target,a.groups=checked_plan(read(a.group_plan),a.endpoint)
        if target['target']<a.length:
            p.error('requested length exceeds the planned trace')
    with (a.cache/'campaign.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        campaign(a)


if __name__=='__main__':
    main()
