"""Kernel-check forward whole-slab QA2R Jacobians in isolated, resumable directories.

Run the tracked generator to promote a selected index to an ordinary repository
module. This driver retains every generated source, leaf olean and axiom audit
under the supplied cache directory.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path
import re
from shutil import disk_usage
import subprocess
from tempfile import NamedTemporaryFile

from emit_sparse_forward_jacobian import emit
from emit_sparse_taylor_slab import RECORD, ROOT
from verify_sparse_reference_slabs import ALLOWED, DESIGN, GIB, available_ram, digest, run_lean


PACKAGE = 'JacobianTraceCache'


def save(path, data):
    with NamedTemporaryFile('w',dir=path.parent,delete=False) as tmp:
        json.dump(data,tmp,indent=2)
        tmp.write('\n')
    Path(tmp.name).replace(path)


def matches(directory, marker):
    return marker.is_file() and all((directory / file).is_file() and digest(directory / file) == key
                                    for file,key in json.loads(marker.read_text())['artifacts'].items())


def verify(item):
    index, cache, common, lean, upstream = item
    modules = emit(index)
    name = next(reversed(modules))
    imports = sorted({imp for source in modules.values() for imp in re.findall(
        r'^public import PlasmaLean.Design.(\w+)$',source,re.MULTILINE) if imp not in modules})
    dependencies = [(dep, digest(DESIGN/(dep+'.trace'))) for dep in imports]
    key = sha256(json.dumps([common,list(modules.items()),dependencies]).encode()).hexdigest()
    work = cache/name/key
    work.mkdir(parents=True,exist_ok=True)
    with (work/'lock').open('w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        marker = work/'accepted.json'
        if matches(work,marker):
            return {**json.loads(marker.read_text()),'resumed':True}
        stack = work/PACKAGE
        stack.mkdir(exist_ok=True)
        env = {**os.environ,'LEAN_NUM_THREADS':'1','LEAN_PATH':str(work)+os.pathsep+upstream}
        args = [lean,'-j1','-R',str(work)]
        metrics = work/'peak.txt'
        artifacts = {}
        wall, peak = 0, 0
        for mod, source in modules.items():
            src, obj = stack/(mod+'.lean'),stack/(mod+'.olean')
            status = work/(mod+'.json')
            for local in modules:
                source = source.replace('public import PlasmaLean.Design.'+local+'\n',
                                        'public import '+PACKAGE+'.'+local+'\n')
            if not matches(work,status):
                src.write_text(source)
                seconds,rss = run_lean([*args,'-o',str(obj),str(src)],env,metrics,work/(mod+'.log'))
                outputs = {str(f.relative_to(work)):digest(f) for f in [src,*stack.glob(mod+'.olean*')]}
                save(status,{'artifacts':outputs,'seconds':seconds,'peak_rss_kib':rss})
            info = json.loads(status.read_text())
            artifacts.update(info['artifacts'])
            wall += info['seconds']
            peak = max(peak,info['peak_rss_kib'])
        theorems = ['physical_clock_log_norm','denominator_pos','fits_record']
        audit = work/'Audit.lean'
        audit.write_text('import '+PACKAGE+'.'+name+'\n' + ''.join(
            '#print axioms PlasmaLean.Design.'+name+'.'+t+'\n' for t in theorems))
        seconds,rss = run_lean([*args,str(audit)],env,metrics,work/'audit.log')
        output = (work/'audit.log').read_text()
        for theorem in theorems:
            found = re.search(re.escape("PlasmaLean.Design."+name+'.'+theorem) +
                              r"' depends on axioms:\s*\[([^]]*)\]",output)
            if not found or set(map(str.strip,found[1].split(','))) != ALLOWED:
                raise ValueError(f'{name}.{theorem} has an unexpected axiom audit\n{output}')
        for f in (audit,work/'audit.log'):
            artifacts[str(f.relative_to(work))] = digest(f)
        result = {'index':index,'key':key,'module':name,'theorems':theorems,'axioms':sorted(ALLOWED),
                  'wall_seconds':round(wall+seconds,3),'peak_rss_kib':max(peak,rss),
                  'artifacts':artifacts}
        save(marker,result)
        return {**result,'resumed':False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--range',nargs=2,type=int,default=(2,7),metavar=('LOW','HIGH'))
    parser.add_argument('--workers',type=int,choices=range(1,6),default=3)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/jacobian-checks')
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    lo,hi = args.range
    if not 0 <= lo <= hi < 391:
        parser.error('slabs must lie in 0..390')
    cache = args.cache.resolve()
    cache.mkdir(parents=True,exist_ok=True)
    if disk_usage(cache).free < 2*GIB or available_ram() < (8+3*args.workers)*GIB:
        raise SystemExit('insufficient disk or RAM headroom for requested worker count')
    deps = ['DommaschkJacobianFrames',*(f'DommaschkHarmonicBlock{n:02}' for n in range(lo//8,hi//8+1))]
    subprocess.run(['lake','build','--no-build',*['PlasmaLean.Design.'+d for d in deps]],
                   cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
    def lake(*args):
        return subprocess.check_output(['lake','env',*args],cwd=ROOT,text=True).strip()
    compiler = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    upstream = lake('printenv','LEAN_PATH')
    common = [digest(RECORD),digest(Path(__file__)),lake('lean','--version')]
    items = [(n,cache,common,compiler,upstream) for n in range(lo,hi+1)]
    summary = []
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for row in pool.map(verify,items,chunksize=1):
            row = {k:v for k,v in row.items() if k != 'artifacts'}
            summary.append(row)
            print(json.dumps(row),flush=True)
    if args.output:
        save(args.output,{'packet_sha256':common[0],'lean_version':common[2],'results':summary})


if __name__ == '__main__':
    main()
