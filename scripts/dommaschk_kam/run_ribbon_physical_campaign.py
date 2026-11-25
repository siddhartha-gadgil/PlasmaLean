"""Run the four-radius spatial and signed IVP checks with a bounded, restartable worker pool."""
import argparse
from concurrent.futures import FIRST_COMPLETED,ThreadPoolExecutor,wait
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from ribbon_central_data import LENGTH,WITNESS_SHA,label
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import HERE,ROOT,digest,save
from verify_sparse_reference_slabs import GIB,available_ram


def work(plan):
    if plan['ribbon']!=WITNESS_SHA or plan['span']!=[0,LENGTH]:
        raise ValueError('expected the authenticated four-ribbon plan through its exterior row')
    spatial=[('spatial',tuple(g['tiles']),*g['span']) for g in plan['groups']]
    coverage=sorted((k,i) for _,ks,a,b in spatial for k in ks for i in range(a,b))
    if coverage!=[(k,i) for k in range(4) for i in range(LENGTH)]:
        raise ValueError('plan does not cover every signed row exactly once')
    physical=[('physical',(k,),a,min(a+8,LENGTH)) for a in range(0,LENGTH,8) for k in range(4)]
    return physical+spatial


def complete(job,args,cache):
    kind,tiles,a,b=job
    for k in tiles:
        for i in range(a,b):
            base,folder=(args.spatial,'jacobians') if kind=='spatial' else (args.physical,'steps')
            path=base/f'tile{k}'/folder/f'{i:03}.json'
            if not path.exists():
                return False
            row=json.loads(path.read_text())
            if row['tile']!=k or row['packet_sha256']!=WITNESS_SHA:
                raise ValueError(f'wrong ribbon cache at {path}')
            actual=row.get('import_module',row['module'])
            uid=(row['import_paths'][0],actual,row['key'])
            if uid not in cache:
                cache[uid]=set(admitted(Path(uid[0]),uid[1],uid[2])['theorems'])
            if kind=='spatial':
                claims=[f'DommaschkJacobian{label(k).upper()}PairedForward{i:03}.physical_clock_log_norm']
            else:
                claims=[f'DommaschkPhysical{label(k).upper()}{d}{i:03}.physical_step' for d in ('Forward','Back')]
            if not all('PlasmaLean.Design.'+c in cache[uid] for c in claims):
                raise ValueError(f'missing expected physical claims at {path}')
    return True


def ready(job,args):
    kind,tiles,a,b=job
    if kind=='spatial':
        return True
    k,=tiles
    return all((base/f'tile{k}'/folder/f'{i:03}.json').exists() for i in range(a,b)
        for base,folder in [(args.spatial,'jacobians'),(args.central,'references')])


def run(job,args):
    kind,tiles,a,b=job
    name=kind+''.join(map(str,tiles))+f'-{a:03}-{b:03}'
    cmd=[sys.executable,HERE/f'verify_ribbon_{kind}_group.py','--ribbon',args.ribbon,
         '--span',str(a),str(b),'--output',args.root/(name+'.json')]
    if kind=='spatial':
        cmd.extend(['--tiles',*map(str,tiles),'--handoff',args.spatial])
        if args.dyadic_from is not None and a>=args.dyadic_from:
            cmd.append('--dyadic')
    else:
        cmd.extend(['--tile',str(tiles[0]),'--packets',args.packets,'--handoff',args.physical,
                    '--central',args.central,'--spatial',args.spatial])
    with (args.root/(name+'.log')).open('a') as out:
        subprocess.run(cmd,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,check=True,
            env={**os.environ,'LEAN_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'})


def campaign(args):
    jobs=work(json.loads(args.plan.read_text()))
    verified={}
    done={g for g in jobs if complete(g,args,verified)}
    failed,running={},{}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while len(done)<len(jobs):
            slots=min(args.workers-len(running),max(0,int((available_ram()/GIB-args.reserve_gib)//8)))
            for job in jobs:
                if job in done or job in running.values() or job in failed or not ready(job,args):
                    continue
                if complete(job,args,verified):
                    done.add(job)
                elif slots:
                    running[pool.submit(run,job,args)]=job
                    slots-=1
            status=dict(witness=WITNESS_SHA,length=LENGTH,
                signed_steps=sum(2*len(ks)*(b-a) for t,ks,a,b in done if t=='physical'),
                shared_spatial_rows=sum(len(ks)*(b-a) for t,ks,a,b in done if t=='spatial'),
                active=list(running.values()),errors={str(k):v for k,v in failed.items()},
                complete=len(done)==len(jobs),available_gib=round(available_ram()/GIB,1))
            save(args.root/'status.json',status)
            if len(done)==len(jobs):
                break
            if not running:
                if failed:
                    raise RuntimeError(f'ribbon campaign has real errors: {failed}')
                time.sleep(12)
                continue
            finished,_=wait(running,timeout=10,return_when=FIRST_COMPLETED)
            for f in finished:
                job=running.pop(f)
                try:
                    f.result()
                    if not complete(job,args,verified):
                        raise ValueError('missing original physical theorem')
                    done.add(job)
                except Exception as exc:
                    failed[job]=str(exc)
    save(args.root/'status.json',dict(witness=WITNESS_SHA,length=LENGTH,signed_steps=8*LENGTH,
        shared_spatial_rows=4*LENGTH,complete=True,active=[],errors={}))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--plan',type=Path,required=True)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--packets',type=Path,required=True)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--dyadic-from',type=int,help='check later physical field jets with integer Horner arithmetic')
    p.add_argument('--reserve-gib',type=int,default=40)
    p.add_argument('--spatial',type=Path,default=ROOT/'.lake/ribbon-spatial-campaign')
    p.add_argument('--physical',type=Path,default=ROOT/'.lake/ribbon-physical-campaign')
    p.add_argument('--central',type=Path,default=ROOT/'.lake/ribbon-central-campaign')
    p.add_argument('--root',type=Path,default=ROOT/'.lake/ribbon-through-campaign')
    args=p.parse_args()
    if (args.workers<1 or args.reserve_gib<0 or digest(args.ribbon)!=WITNESS_SHA or
            args.dyadic_from is not None and not 0<=args.dyadic_from<LENGTH):
        p.error('expected the original wide-radius witness and valid worker and RAM limits')
    args.root.mkdir(parents=True,exist_ok=True)
    with (args.root/'manager.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        campaign(args)


if __name__=='__main__':
    main()
