"""Resume the signed opposite inner-face physical and action panel proofs in bounded workers."""
import argparse
from collections import deque
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from verify_mirror_physical_hit import admitted
from verify_native_action_campaign import cpus
from verify_opposite_action_subwell import CUT, NAME, PACKAGE
from verify_opposite_inner_ode_group import CHECKSUM
from verify_physical_trace_slabs import ROOT, digest, save
from verify_sparse_reference_slabs import GIB, available_ram
from ribbon_central_data import WITNESS_SHA


HERE=Path(__file__).resolve().parent


def entries(path,stage,a,b,core):
    if not path.exists():
        return None
    raw=json.loads(path.read_text())
    if raw['packet_sha256']!=CHECKSUM or (stage=='panels' and raw['core']!=core):
        raise ValueError(f'different packet or mass receipt in {path}')
    rows=raw['rows' if stage=='ode' else 'signed_rows']
    found={}
    for row in rows:
        i,s=row['index'],row['direction']
        expected=(f'DommaschkPhysicalQ1R470{"Back" if s<0 else "Forward"}{i:03}' if stage=='ode' else
                  f'DommaschkCoarsePhysicalQ1R470{"Back" if s<0 else "Fwd"}{i:03}N24')
        if not a<=i<b or s not in (-1,1) or (i,s) in found or row['module']!=expected:
            raise ValueError(f'wrong physical group at {i},{s} in {path}')
        r=admitted(Path(row['import_paths'][0]),expected,row['key'])
        theorem='physical_step' if stage=='ode' else 'cells'
        if f'PlasmaLean.Design.{expected}.{theorem}' not in r['theorems']:
            raise ValueError(f'wrong proof type in {path}')
        found[i,s]=row
    return rows if len(found)==2*(b-a) else None


def run(args):
    if digest(args.packet)!=CHECKSUM:
        raise ValueError('the opposite singleton packet hash differs from the original')
    core=json.loads(args.core.read_text())
    if (core['packet_sha256'],core['package'],core['module'],core['counts'])!=(CHECKSUM,PACKAGE,NAME,[CUT,CUT]):
        raise ValueError('expected the positive lower mass archive for the original 320 signed pairs')
    admitted(Path(core['import_paths'][0]),NAME,core['key'])
    first,last=args.span
    cuts=sorted({first,last,*range(((first+args.group-1)//args.group)*args.group,last,args.group)})
    if first==0 and last>1:
        cuts=sorted({1,*cuts})
    todo=deque()
    accepted={k:[] for k in ('ode','panels')}
    for a,b in zip(cuts,cuts[1:]):
        for stage in args.stages:
            path=args.work/stage/f'{a:03}-{b:03}.json'
            path.parent.mkdir(exist_ok=True,parents=True)
            if entries(path,stage,a,b,core['key']) is None:
                todo.append((stage,a,b,path))
            else:
                accepted[stage].append([a,b,str(path)])
    active={}
    errors=[]
    prev=cpus()
    primary_ready=args.after_receipt is None
    def status():
        save(args.output,dict(packet_sha256=CHECKSUM,core=core['key'],span=args.span,
             completed={k:sum(2*(b-a) for a,b,_ in v) for k,v in accepted.items()},
             receipts=accepted,primary_ready=primary_ready,active=[list(t[:3]) for _,t,_ in active.values()],errors=errors))
    try:
        while todo or active:
            status()
            for pid,(p,t,log) in list(active.items()):
                if p.poll() is None:
                    continue
                del active[pid]
                log.close()
                stage,a,b,path=t
                if p.returncode or entries(path,stage,a,b,core['key']) is None:
                    errors.append([stage,a,b,p.returncode,str(path.with_suffix('.log'))])
                else:
                    accepted[stage].append([a,b,str(path)])
            if not todo and not active:
                break
            if not primary_ready and args.after_receipt.is_file():
                primary=json.loads(args.after_receipt.read_text())
                if (primary['packet_sha256'],primary['module'],primary['outer_rows'])!=(
                        WITNESS_SHA,'DommaschkRadialRibbonThrough',332):
                    raise ValueError('the primary prerequisite is not the original four-tile through332 theorem')
                accepted_primary=admitted(Path(primary['import_paths'][0]),primary['module'],primary['key'])
                if 'PlasmaLean.Design.DommaschkRadialRibbonThrough.from_seed' not in accepted_primary['theorems']:
                    raise ValueError('the primary receipt lacks the full through-going theorem')
                primary_ready=True
            now=cpus()
            dt=now[0]-prev[0]
            idle=(os.cpu_count() or 1)*(now[1]-prev[1])/dt if dt else 0
            prev=now
            ram_slots=max(0,int((available_ram()/GIB-args.reserve_gib)//6))
            slots=min(args.workers-len(active),max(0,int(idle-args.reserve_cores)),ram_slots)
            if not primary_ready:
                slots=0
            for _ in range(min(len(todo),slots)):
                t=todo.popleft()
                stage,a,b,path=t
                cmd=[sys.executable,str(HERE/('verify_opposite_inner_ode_group.py' if stage=='ode' else
                                              'verify_opposite_inner_action_rows.py')),
                     '--packet',str(args.packet),'--output',str(path)]
                if stage=='ode':
                    cmd+=['--span',str(a),str(b)]
                else:
                    cmd+=['--core',str(args.core),'--rows',*map(str,range(a,b))]
                log=path.with_suffix('.log').open('a')
                p=subprocess.Popen(cmd,stdout=log,stderr=log,cwd=ROOT,env={**os.environ,
                    'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','LEAN_NUM_THREADS':'1'})
                active[p.pid]=p,t,log
                print(stage,a,b,p.pid,flush=True)
            status()
            time.sleep(args.poll)
    finally:
        for p,_,log in active.values():
            if p.poll() is None:
                p.terminate()
            log.close()
        status()
    if errors:
        raise SystemExit('incomplete signed groups; see error records in '+str(args.output))
    if args.through_output:
        subprocess.run([sys.executable,str(HERE/'verify_opposite_inner_trajectory.py'),
            '--packet',str(args.packet),'--core',str(args.core),'--campaign',str(args.output),
            '--length',str(last),'--output',str(args.through_output)],cwd=ROOT,check=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',type=Path,required=True)
    p.add_argument('--core',type=Path,required=True)
    p.add_argument('--span',type=int,nargs=2,default=[0,CUT],metavar=('FIRST','STOP'))
    p.add_argument('--group',type=int,default=8)
    p.add_argument('--stages',choices=['ode','panels'],nargs='+',default=['ode','panels'])
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--reserve-cores',type=int,default=2)
    p.add_argument('--reserve-gib',type=int,default=40)
    p.add_argument('--poll',type=int,default=8)
    p.add_argument('--after-receipt',type=Path,help='start computing only after this primary receipt exists')
    p.add_argument('--through-output',type=Path,help='join all verified ODE steps and panels on one physical field line')
    p.add_argument('--work',type=Path,default=ROOT/'.lake/opposite-inner-campaign')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 0<=a.span[0]<a.span[1]<=CUT or not 1<=a.group<=16 or a.workers<1 or a.poll<1:
        p.error('choose a nonempty central span, group size 1–16 and positive worker and poll limits')
    if len(set(a.stages))!=len(a.stages) or a.reserve_cores<0 or a.reserve_gib<0:
        p.error('stages must be distinct and both reserves nonnegative')
    if a.through_output and (a.span[0]!=0 or set(a.stages)!={'ode','panels'}):
        p.error('joining an original birth requires both complete stages starting from row zero')
    a.work.mkdir(parents=True,exist_ok=True)
    with (a.work/'campaign.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        run(a)


if __name__=='__main__':
    main()
