"""Verify reflected backward theorems using existing forward Lean proof artifacts.

Consumes JSONL written by verify_sparse_reference_slabs.py. Each row imports
only its corresponding forward package and the shared physical symmetry theorem.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess

from emit_reflected_reference import render
from emit_sparse_taylor_slab import RECORD, ROOT
from verify_sparse_reference_slabs import ALLOWED, GIB, available_ram, digest, run_lean


def compile_row(args):
    row,cache,lean,lean_path = args
    i = row['index']
    f = f'DommaschkTraceResidualForward{i:03}'
    b = f'DommaschkReflectedBack{i:03}'
    if row['direction'] != 1 or row['theorem'] != f+'.physical_defect':
        raise ValueError('expected a section-zero forward proof')
    key = row['key']
    if not re.fullmatch('[0-9a-f]{64}',key):
        raise ValueError('invalid forward fingerprint')
    origin = cache/f/key
    proof = json.loads((origin/'accepted.json').read_text())
    if (proof['theorem'] != row['theorem'] or set(proof['axioms']) != ALLOWED
            or proof['key'] != key or proof['index'] != i):
        raise ValueError('inconsistent forward manifest')
    for suffix in ('Inputs','D','R','Z','Bounds',''):
        for ext in ('.olean','.olean.private','.olean.server'):
            path = 'TraceCache/'+f+suffix+ext
            if digest(origin/path) != proof['artifacts'][path]:
                raise ValueError(f'forward artifact changed: {path}')
    work = cache/'reflected'/b/key
    package = work/'ReflectedCache'
    package.mkdir(parents=True,exist_ok=True)
    src,out = package/(b+'.lean'),package/(b+'.olean')
    src.write_text(render(RECORD,i,'TraceCache'))
    env = {**os.environ,'LEAN_PATH':os.pathsep.join((str(work),str(origin),lean_path)),
           'LEAN_NUM_THREADS':'1'}
    sec,rss = run_lean([lean,'-j1','-R',str(work),'-o',str(out),str(src)],
                       env,work/'peak.txt',work/'build.log')
    audit = work/'Audit.lean'
    audit.write_text(f'import ReflectedCache.{b}\n#print axioms PlasmaLean.Design.{b}.physical_defect\n')
    audit_sec,audit_rss = run_lean([lean,'-j1','-R',str(work),str(audit)],env,work/'peak.txt',work/'audit.log')
    match = re.search(r'depends on axioms:\s*\[([^]]*)\]', (work/'audit.log').read_text())
    if not match or set(map(str.strip,match[1].split(','))) != ALLOWED:
        raise ValueError(f'{b}: unaudited axiom')
    return {'direction':-1,'index':i,'forward_key':key,'theorem':b+'.physical_defect',
            'axioms':sorted(ALLOWED),'olean_sha256':digest(out),'source_sha256':digest(src),
            'wall_seconds':round(sec+audit_sec,3),'peak_rss_kib':max(rss,audit_rss)}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('forward_results',type=Path,nargs='+')
    p.add_argument('--workers',type=int,choices=range(1,5),default=1)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/trace-residual')
    p.add_argument('--range',nargs=2,type=int,metavar=('LO','HI'),required=True)
    a = p.parse_args()
    lo,hi = a.range
    if not 0 <= lo <= hi < 391 or available_ram() < (12+4*a.workers)*GIB:
        p.error('invalid slab range or insufficient memory headroom')
    selected = sorted((r for path in a.forward_results for r in map(json.loads,path.read_text().splitlines())
                       if r['direction'] == 1 and lo <= r['index'] <= hi),key=lambda r:r['index'])
    if [r['index'] for r in selected] != list(range(lo,hi+1)):
        p.error('requested range needs one forward proof per slab')
    subprocess.run(['lake','build','--no-build','PlasmaLean.Design.DommaschkSectionReflection'],
                   cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    lean_path = lake('printenv','LEAN_PATH')
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        for result in pool.map(compile_row,[(r,a.cache.resolve(),lean,lean_path) for r in selected]):
            print(json.dumps(result),flush=True)
