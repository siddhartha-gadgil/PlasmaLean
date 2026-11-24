"""Kernel-check explicit rectangular Jacobians or replay the original square time-panel backend.

Example: --range 69 71 --workers 3. Use --range 68 68 --square-panels to
reproduce the original full-square eight-panel certificate.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import fcntl
import json
import os
from pathlib import Path
import re
from shutil import disk_usage
import subprocess
import time

from emit_rectangular_jacobian import emit as rectangular
from emit_sparse_forward_jacobian import emit as square
from verify_physical_trace_slabs import (ALLOWED, JACOBIAN_PACKAGE, RECORD, ROOT, accepted,
                                        digest, run_lean, save, upstream)
from verify_sparse_forward_jacobians import matches
from verify_sparse_reference_slabs import GIB, available_ram


THEOREMS = ('physical_clock_log_norm','denominator_pos','fits_record')


def explicit_package(index, square_panels, cache, packet_hash, version):
    modules = square(index,panels=True,shared=True) if square_panels else rectangular(index)
    info = upstream(cache,list(modules.items()),'verify_sparse_forward_jacobians.py',
                    packet_hash,version,JACOBIAN_PACKAGE)
    return modules,info


def verify(job):
    index,square_panels,cache,packet_hash,version,lean,paths = job
    modules,info = explicit_package(index,square_panels,cache,packet_hash,version)
    work,key,name,package = info
    tree = work/package
    tree.mkdir(parents=True,exist_ok=True)
    with (work/'lock').open('w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        marker = work/'accepted.json'
        if marker.exists():
            _, cached = accepted(info,index,time.monotonic())
            return index,cached['key'],True
        env = {**os.environ,'LEAN_NUM_THREADS':'1','LEAN_PATH':str(work)+os.pathsep+paths}
        cmd = [lean,'-j1','-R',str(work)]
        artifacts = {}
        seconds,peak = 0,0
        for mod,body in modules.items():
            src,obj = tree/(mod+'.lean'),tree/(mod+'.olean')
            status = work/(mod+'.json')
            if not matches(work,status):
                def local_import(m):
                    return 'public import '+package+'.'+m[1] if m[1] in modules else m[0]
                body = re.sub(r'^public import PlasmaLean\.Design\.(\w+)$',local_import,body,flags=re.M)
                src.write_text(body)
                wall,rss = run_lean([*cmd,'-o',str(obj),str(src)],env,work/'peak.txt',work/(mod+'.log'))
                files = {str(p.relative_to(work)):digest(p) for p in [src,*tree.glob(mod+'.olean*')]}
                save(status,{'artifacts':files,'seconds':wall,'peak_rss_kib':rss})
            check = json.loads(status.read_text())
            artifacts.update(check['artifacts'])
            seconds += check['seconds']
            peak = max(peak,check['peak_rss_kib'])
        audit,log = work/'Audit.lean',work/'audit.log'
        audit.write_text('import '+package+'.'+name+'\n'+''.join(
            f'#print axioms PlasmaLean.Design.{name}.{t}\n' for t in THEOREMS))
        elapsed,rss = run_lean([*cmd,str(audit)],env,work/'peak.txt',log)
        checked = log.read_text()
        for t in THEOREMS:
            match = re.search(re.escape(f"PlasmaLean.Design.{name}.{t}'")+
                              r' depends on axioms:\s*\[([^]]*)\]',checked)
            if not match or set(map(str.strip,match[1].split(','))) != ALLOWED:
                raise ValueError(f'axiom audit failed for {name}.{t}')
        artifacts.update({p.name:digest(p) for p in (audit,log)})
        save(marker,{'index':index,'module':name,'key':key,'theorems':list(THEOREMS),
                     'axioms':sorted(ALLOWED),'wall_seconds':round(seconds+elapsed,3),
                     'peak_rss_kib':max(peak,rss),'artifacts':artifacts})
    return index,key,False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--range',nargs=2,type=int,metavar=('FIRST','LAST'))
    group.add_argument('--indices',nargs='+',type=int,
                       help='explicit row indices in scheduling priority order')
    parser.add_argument('--square-panels',action='store_true')
    parser.add_argument('--workers',type=int,choices=range(1,4),default=1)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/jacobian-checks')
    args = parser.parse_args()
    indices = args.indices if args.range is None else list(range(args.range[0],args.range[1]+1))
    if not indices or any(not 0 <= i < 391 for i in indices) or len(set(indices)) != len(indices):
        parser.error('indices must lie in 0..390')
    args.cache.mkdir(parents=True,exist_ok=True)
    if disk_usage(args.cache).free < 2*GIB or available_ram() < (8+3*args.workers)*GIB:
        raise SystemExit('insufficient disk or RAM headroom for the requested workers')
    deps = ['DommaschkJacobianFrames','DommaschkJacobianPanels','DommaschkStoredPowers',
            *(f'DommaschkHarmonicBlock{b:02}' for b in sorted({i//8 for i in indices}))]
    subprocess.run(['lake','build','--no-build',*['PlasmaLean.Design.'+m for m in deps]],
                   cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    common = (args.square_panels,args.cache.resolve(),digest(RECORD),lake('lean','--version'),
              str(Path(lake('lean','--print-prefix'))/'bin/lean'),lake('printenv','LEAN_PATH'))
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for i,key,resumed in pool.map(verify,[(i,*common) for i in indices]):
            print(json.dumps({'index':i,'key':key,'resumed':resumed}),flush=True)


if __name__ == '__main__':
    main()
