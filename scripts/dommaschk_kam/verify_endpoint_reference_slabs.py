"""Verify the physical central-reference defect at any of the eight N-60 endpoints."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import gzip
import json
from pathlib import Path
import re
import subprocess
import sys
from types import SimpleNamespace

from emit_sparse_trace_defect_samples import emit_selected, reference_columns
from screen_sparse_reference_defects import jobs
from shared_sparse_powers import add_shared_powers
from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import RECORD, ROOT, digest, external_dependencies, save


ENDPOINTS = ('q0r470','q0r478','q0r523','q0r531','q1r456','q1r464','q1r509','q1r517')
PACKAGE = 'EndpointTraceCache'
NATIVE_OPPOSITE_MARKER = 'use-independent-native-residuals.json'


def use_campaign_backend(a):
    """Route a single scheduled original row to its endpoint's selected backend."""
    if (not a.output or len(a.endpoints)!=1 or a.endpoints[0] not in ENDPOINTS[4:] or
            a.range[0]!=a.range[1] or a.output.parent.name!='references'):
        return False
    label=a.endpoints[0]
    i=a.range[0]
    base=a.output.parent.parent
    marker=base/NATIVE_OPPOSITE_MARKER
    if base.name!=label or a.output.name!=f'{i:03}.json' or not marker.is_file():
        return False
    selected=json.loads(marker.read_text())
    checksum=digest(RECORD.with_name(f'bounce_frame_q1_u{label[3:]}.json.gz'))
    if selected!={'endpoint':label,'packet_sha256':checksum,'backend':'independent-harmonic'}:
        raise ValueError(f'invalid signed residual backend for the original packet at {base}')
    cmd=[sys.executable,Path(__file__).with_name('verify_opposite_native_defects.py'),
         '--endpoint',label,'--row',str(i),'--output',a.output]
    if a.direction is not None:
        cmd+=['--direction',str(a.direction)]
    if subprocess.run(cmd,cwd=ROOT).returncode==0:
        return True
    print(f'Native central proof did not complete at {label} {i}; continuing with sparse original polynomials.',
          flush=True)
    return False


def run_one(task):
    label, launch, job, packet_hash, version, env, cache, shared = task
    code = list(emit_selected([job],label=label.upper(),launch=launch))
    if shared:
        columns = reference_columns(*job[:4])
        code = list(add_shared_powers(dict(code),code[0][0],code[-1][0],columns,'reference').items())
    names = {name for name,_ in code}
    def relocate(m):
        return 'public import '+PACKAGE+'.'+m[1] if m[1] in names else m[0]
    top = code[-1][0]
    declarations = [(name,re.sub(r'^public import PlasmaLean\.Design\.(\w+)$',relocate,src,flags=re.M),
                     ['physical_defect'] if name == top else []) for name,src in code]
    root, manifest = compile_modules(cache/top,declarations,[],
                                     [packet_hash,version,external_dependencies(code)],env,PACKAGE)
    result = {k:v for k,v in manifest.items() if k != 'artifacts'}
    result.update(endpoint=label, section_in_half_pi=job[0], launch_u=str(launch),
                  index=job[2], direction=job[1], packet_sha256=packet_hash, import_paths=[str(root)])
    print(f"{label} sign {job[1]:+} row {job[2]}: {manifest['key']}",flush=True)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',choices=ENDPOINTS,nargs='+',default=ENDPOINTS)
    p.add_argument('--range',nargs=2,type=int,default=(0,0),metavar=('FIRST','LAST'))
    p.add_argument('--direction',type=int,choices=(-1,1))
    p.add_argument('--workers',type=int,choices=range(1,7),default=2)
    p.add_argument('--shared',action='store_true',help='reuse checked polynomial powers across all three fields')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-residuals')
    p.add_argument('--output',type=Path)
    a = p.parse_args()
    lo,hi = a.range
    if not 0 <= lo <= hi < 391 or len(set(a.endpoints)) != len(a.endpoints):
        p.error('choose distinct endpoints and a row range within 0..390')
    if use_campaign_backend(a):
        return
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version = lake('lean','--version')
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    phases = {int(e[1]) for e in a.endpoints}
    static = ['DommaschkBounceTaylor','DommaschkFramedTaylorResidual']
    if a.shared:
        static.append('DommaschkStoredPowers')
    if 1 in phases:
        static.append('DommaschkOppositeHarmonic')
    static.extend(f'DommaschkHarmonicBlock{b:02}' for b in range(lo//8,hi//8+1))
    subprocess.run(['lake','build','--no-build',*['PlasmaLean.Design.'+s for s in static]],
                   cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
    tasks = []
    for label in a.endpoints:
        section = int(label[1])
        radius = int(label[3:])
        launch = Fraction(radius,1000)
        path = RECORD.with_name(f'bounce_frame_q{section}_u{radius}.json.gz')
        with gzip.open(path,'rt') as src:
            packet = json.load(src)
        if (packet['section_in_half_pi'],Fraction(packet['launch_u'])) != (section,launch):
            raise ValueError(f'wrong endpoint in {path}')
        packet_hash = digest(path)
        tasks.extend((label,launch,job,packet_hash,version,env,a.cache.resolve(),a.shared)
                     for job in jobs(path,8,False) if lo <= job[2] <= hi and a.direction in (None,job[1]))
    with ProcessPoolExecutor(max_workers=a.workers) as executor:
        records = list(executor.map(run_one,tasks,chunksize=1))
    if a.output:
        save(a.output,records)


if __name__ == '__main__':
    main()
