"""Assemble forward physical ODE theorems from accepted q=0, u=0.470 row certificates.

Run the central-defect and forward-Jacobian verifiers for the same range first.
Their exact emitted sources, compiler, witness and current dependency hashes
identify the upstream packages. Every recorded artifact is rehashed before use.
The output includes a single LEAN_PATH entry for importing every selected row.
Use --shared-from 16 with the shared-power forward Jacobian campaign.
"""

import argparse
import fcntl
import gzip
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
from string import Template
import time

from emit_sparse_forward_jacobian import emit as emit_jacobian
from emit_sparse_taylor_slab import RECORD, ROOT
from emit_sparse_trace_defect_samples import emit_selected
from screen_sparse_reference_defects import jobs
from verify_sparse_forward_jacobians import PACKAGE as JACOBIAN_PACKAGE, save
from verify_sparse_reference_slabs import ALLOWED, DESIGN, digest, run_lean


HERE = Path(__file__).resolve().parent
TEMPLATE = HERE / 'templates/physical_forward_step.lean.tpl'
PACKAGE = 'PhysicalTraceCache'
THEOREMS = ('checked', 'field_bounds', 'physical_step')
LIBRARIES = ('DommaschkPositionFramesFwd', 'DommaschkPhysicalTraceStep')
# Version one used the verifier's source digest as the physical artifact schema
# identifier. Keep it stable for CLI and scheduling changes. The generated Lean
# proof, both upstream manifests, compiler, witness and imported .trace files
# are hashed independently. Change the schema when the artifact contract changes.
ROW_SCHEMA_V1 = 'ce95f46c0f823732d95a3e8971b353bdae28fc78801036007af9bf727d0c2114'


def key_of(data):
    return sha256(json.dumps(data).encode()).hexdigest()


def external_dependencies(modules):
    defined = {name for name, _ in modules}
    external = {name for _, source in modules for name in re.findall(
        r'^public import PlasmaLean\.Design\.(\w+)$', source, re.MULTILINE) if name not in defined}
    return [(name, digest(DESIGN / (name + '.trace'))) for name in sorted(external)]


def artifact_hashes(directory, record):
    for relative, checksum in record['artifacts'].items():
        path = directory / relative
        if not path.is_file() or digest(path) != checksum:
            raise ValueError(f'certificate artifact hash mismatch: {path}')


def upstream(cache, modules, provider, packet_hash, version, package):
    name = modules[-1][0]
    dependency_key = [packet_hash, digest(HERE / provider), version]
    key = key_of([dependency_key, modules, external_dependencies(modules)])
    directory = cache / name / key
    return directory, key, name, package


def accepted(info, index, deadline):
    directory, key, name, package = info
    marker = directory / 'accepted.json'
    announced = False
    while not marker.is_file():
        if time.monotonic() >= deadline:
            raise FileNotFoundError(f'current upstream certificate is unavailable: {marker}')
        if not announced:
            print(f'Waiting for {name} ({key[:12]})', flush=True)
            announced = True
        time.sleep(min(5, max(0,deadline-time.monotonic())))
    record = json.loads(marker.read_text())
    if (record['key'] != key or record['index'] != index or set(record['axioms']) != ALLOWED
            or f'{package}/{name}.olean' not in record['artifacts']):
        raise ValueError(f'inconsistent upstream record: {marker}')
    if package == JACOBIAN_PACKAGE:
        if record['module'] != name or not {'physical_clock_log_norm', 'denominator_pos',
                                            'fits_record'} <= set(record['theorems']):
            raise ValueError(f'incorrect spatial theorem manifest: {name}')
    elif record['direction'] != 1 or record['theorem'] != name + '.physical_defect':
        raise ValueError(f'incorrect central residual manifest: {name}')
    artifact_hashes(directory, record)
    return directory, record


def stored(index):
    block, offset = divmod(index, 16)
    return f'DommaschkPositionFramesFwd.block{block}[{offset}]'


def source_for(index, error, spatial, central):
    name = f'DommaschkPhysicalForward{index:03}'
    prior = 'next ' + stored(index-1) if index else 'DommaschkPositionFramesFwd.start'
    return name, Template(TEMPLATE.read_text()).substitute(
        name=name, jac=spatial, central=central, index=index, end=index+1,
        offset=2*index+1, stored=stored(index), previous=prior, error=error)


def verify_row(index, error, packages, args, common):
    (jacdir, jac), (resdir, res) = packages
    name, source = source_for(index, error, jac['module'], res['theorem'].split('.')[0])
    key = key_of([common, source, jac['key'], res['key'], jac['artifacts'], res['artifacts']])
    directory = args.cache / name / key
    tree = directory / PACKAGE
    tree.mkdir(parents=True, exist_ok=True)
    marker = directory / 'accepted.json'
    with (directory / 'lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if marker.is_file():
            record = json.loads(marker.read_text())
            if (record['key'] != key or record['module'] != name or record['index'] != index
                    or set(record['theorems']) != set(THEOREMS) or set(record['axioms']) != ALLOWED):
                raise ValueError(f'inconsistent physical row record: {marker}')
            artifact_hashes(directory, record)
            return directory, record, True
        src, obj = tree / (name + '.lean'), tree / (name + '.olean')
        src.write_text(source)
        env = {**os.environ, 'LEAN_NUM_THREADS':'1', 'LEAN_PATH':os.pathsep.join(
            [str(directory), str(jacdir), str(resdir), args.lean_path])}
        cmd = [args.lean, '-j1', '-DwarningAsError=true', '-R', str(directory)]
        metric = directory / 'peak.txt'
        duration, rss = run_lean([*cmd, '-o', str(obj), str(src)], env, metric, directory/'row.log')
        audit = directory / 'Audit.lean'
        audit.write_text(f'import {PACKAGE}.{name}\n' + ''.join(
            f'#print axioms PlasmaLean.Design.{name}.{t}\n' for t in THEOREMS))
        audit_log = directory / 'audit.log'
        seconds, peak = run_lean([*cmd, str(audit)], env, metric, audit_log)
        output = audit_log.read_text()
        for t in THEOREMS:
            pattern = re.escape(f"PlasmaLean.Design.{name}.{t}'") + r' depends on axioms:\s*\[([^]]*)\]'
            match = re.search(pattern, output)
            if not match or set(map(str.strip, match[1].split(','))) != ALLOWED:
                raise ValueError(f'axiom audit failed for {name}.{t}')
        files = [src, audit, audit_log, *tree.glob(name+'.olean*')]
        record = {'module':name, 'key':key, 'index':index, 'direction':1,
                  'jacobian_key':jac['key'], 'residual_key':res['key'],
                  'theorems':list(THEOREMS), 'axioms':sorted(ALLOWED),
                  'wall_seconds':round(duration+seconds,3), 'peak_rss_kib':max(rss,peak),
                  'artifacts':{str(f.relative_to(directory)):digest(f) for f in files}}
        save(marker, record)
        return directory, record, False


def overlay(cache, rows, artifacts, lean, lean_path):
    key = key_of([row['key'] for row in rows])
    root = cache / 'imports' / key
    root.mkdir(parents=True, exist_ok=True)
    with (root/'lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for directory, record in artifacts:
            for relative in record['artifacts']:
                path = Path(relative)
                if (path.parts[0] not in (JACOBIAN_PACKAGE, 'TraceCache', PACKAGE)
                        or '.olean' not in path.suffixes):
                    continue
                link = root / path
                link.parent.mkdir(exist_ok=True)
                target = directory / path
                if link.is_symlink():
                    if link.resolve(strict=True) != target:
                        raise ValueError(f'conflicting package overlays: {link}')
                else:
                    link.symlink_to(target)
        audit = root / 'ImportsAudit.lean'
        audit.write_text(''.join(f"import {PACKAGE}.{r['module']}\n" for r in rows)
                         + ''.join(f"#check PlasmaLean.Design.{r['module']}.field_bounds\n" for r in rows))
        env = {**os.environ, 'LEAN_NUM_THREADS':'1', 'LEAN_PATH':str(root)+os.pathsep+lean_path}
        run_lean([lean, '-j1', '-DwarningAsError=true', '-R', str(root), str(audit)],
                 env, root/'peak.txt', root/'imports.log')
    return root


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--range', nargs=2, type=int, default=(2,7), metavar=('LOW','HIGH'))
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/physical-frame-checks')
    parser.add_argument('--residual-cache', type=Path, default=ROOT/'.lake/trace-residual')
    parser.add_argument('--jacobian-cache', type=Path, default=ROOT/'.lake/jacobian-checks')
    parser.add_argument('--wait-seconds', type=int, default=0, help='per-row wait for upstream jobs')
    parser.add_argument('--output', type=Path, help='write a compact verified row and imports manifest')
    parser.add_argument('--shared-from',type=int,metavar='INDEX',
                        help='use shared-power Jacobian certificates at and above this row')
    args = parser.parse_args()
    lo,hi = args.range
    if not 0 <= lo <= hi < 391 or args.wait_seconds < 0:
        parser.error('expected an inclusive range in 0..390 and a nonnegative wait')
    if args.shared_from is not None and not 0 <= args.shared_from < 391:
        parser.error('--shared-from must lie in 0..390')
    args.cache = args.cache.resolve()
    jac_cache, res_cache = args.jacobian_cache.resolve(), args.residual_cache.resolve()
    static = [*LIBRARIES, 'DommaschkJacobianFrames', 'DommaschkFramedTaylorResidual',
              'DommaschkBounceTaylor', *(f'DommaschkHarmonicBlock{i:02}'
                                        for i in range(lo//8,hi//8+1))]
    if args.shared_from is not None and hi >= args.shared_from:
        static.append('DommaschkStoredPowers')
    subprocess.run(['lake','build','--no-build',*['PlasmaLean.Design.'+m for m in static]],
                   check=True,cwd=ROOT,stdout=subprocess.DEVNULL)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version = lake('lean','--version')
    args.lean = str(Path(lake('lean','--print-prefix')) / 'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    packet_hash = digest(RECORD)
    packet = json.loads(gzip.decompress(RECORD.read_bytes()))
    if (packet['launch_u'] != '47/100' or packet['section_in_half_pi'] != 0
            or packet['format'] != 'DommaschkN60Frame/v1'):
        raise ValueError('expected the archived pilot endpoint')
    forward, = [t for t in packet['traces'] if t['direction'] == 1]
    common = [packet_hash,version,ROW_SCHEMA_V1,
              [(m,digest(DESIGN/(m+'.trace'))) for m in LIBRARIES]]
    artifacts, rows = [], []
    for job in jobs(RECORD,8,False):
        _,direction,index,*_ = job
        if direction != 1 or not lo <= index <= hi:
            continue
        shared = args.shared_from is not None and index >= args.shared_from
        emitted = emit_jacobian(index,shared=True) if shared else emit_jacobian(index)
        jac = upstream(jac_cache,list(emitted.items()),'verify_sparse_forward_jacobians.py',
                       packet_hash,version,JACOBIAN_PACKAGE)
        res = upstream(res_cache,list(emit_selected([job])),'verify_sparse_reference_slabs.py',
                       packet_hash,version,'TraceCache')
        deadline = time.monotonic()+args.wait_seconds
        packages = [accepted(p,index,deadline) for p in (jac,res)]
        work,record,resumed = verify_row(index,forward['steps'][index]['physical_trial_radius'],
                                          packages,args,common)
        artifacts.extend([*packages,(work,record)])
        row = {k:v for k,v in record.items() if k != 'artifacts'}
        rows.append(row)
        print(json.dumps({**row,'resumed':resumed}),flush=True)
    if len(rows) != hi-lo+1:
        raise ValueError('trace omitted requested rows')
    root = overlay(args.cache,rows,artifacts,args.lean,args.lean_path)
    summary = {'packet_sha256':packet_hash,'lean_version':version,'imports':str(root),'rows':rows}
    if args.output:
        save(args.output,summary)
    print('Import verified modules with LEAN_PATH prefix '+str(root),flush=True)


if __name__ == '__main__':
    main()
