"""Certify the moving-frame Jacobian on the forward trial of an archived N-60 endpoint."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import gzip
import json
from pathlib import Path
import re
import subprocess
from types import SimpleNamespace

from emit_rectangular_jacobian import emit_rectangle
from screen_projected_jacobians import projected_radii
from screen_sparse_jacobians import jobs
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_physical_trace_slabs import RECORD, ROOT, digest, external_dependencies, save


PACKAGE = 'EndpointJacobianCache'
THEOREMS = ['clock_inputs', 'denominator_pos', 'physical_clock_log_norm', 'fits_record']


def endpoint_tasks(label, lo, hi):
    section = int(label[1])
    radius = int(label[3:])
    launch = Fraction(radius, 1000)
    path = RECORD.with_name(f'bounce_frame_q{section}_u{radius}.json.gz')
    with gzip.open(path, 'rt') as src:
        packet = json.load(src)
    if (packet['section_in_half_pi'], Fraction(packet['launch_u'])) != (section, launch):
        raise ValueError(f'wrong launch archive for {label}')
    checksum = digest(path)
    for sec, sign, index, start, step, _, _ in jobs(path, 8, False, 1):
        if sign == 1 and lo <= index <= hi:
            yield label, launch, checksum, sec, index, start, step


def run_one(task):
    (label, launch, checksum, section, index, start, step), pair, cache, version, env = task
    radii = projected_radii(start, step['frame_end'], step['frame_trial_radius'])
    suffix = 'PairedForward' if pair else 'Forward'
    top = f'DommaschkJacobian{label.upper()}{suffix}{index:03}'
    forward_rate = step['log_norm_upper']
    if pair:
        if start != pair.forward_left or step != pair.forward:
            raise ValueError('reflected data uses a different forward row')
        radii = pair.common_radii
        step = {**step, 'log_norm_upper': str(pair.common_rate)}
    sources = emit_rectangle(index, section, start, step, radii, top, forward_rate)
    labels = list(THEOREMS)
    if pair:
        ending = f'end PlasmaLean.Design.{top}\n'
        if not sources[top].endswith(ending):
            raise ValueError('unexpected closing namespace in generated Jacobian')
        rate = pair.backward['log_norm_upper']
        sources[top] = sources[top].removesuffix(ending) + (
            f'theorem fits_backward_record : logNorm ≤ {rate} := by norm_num [logNorm]\n\n' + ending)
        labels.append('fits_backward_record')
    def move(match):
        name = match[1]
        return 'public import '+PACKAGE+'.'+name if name in sources else match[0]
    rows = [(name, re.sub(r'^public import PlasmaLean\.Design\.(\w+)$', move, code, flags=re.M),
             labels if name == top else []) for name, code in sources.items()]
    root, marker = compile_modules(cache/top, rows, [],
        [checksum, version, external_dependencies(list(sources.items()))], env, PACKAGE)
    report = {k: v for k, v in marker.items() if k != 'artifacts'}
    report.update(endpoint=label, launch_u=str(launch), section_in_half_pi=section, direction=1,
                  index=index, projected_radii=list(radii), packet_sha256=checksum,
                  lean_version=version, import_paths=[str(root)])
    if pair:
        report.update(paired_trials=True, center_gap=list(pair.center_gap),
                      forward_radii=list(pair.forward_radii), backward_radii=list(pair.backward_radii),
                      common_rate=str(pair.common_rate))
    save(root/'row.json', report)
    print(f'{label} forward {index} accepted {marker["key"]}', flush=True)
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints', nargs='+', choices=ENDPOINTS, default=[*ENDPOINTS[1:]])
    p.add_argument('--range', type=int, nargs=2, default=(0, 0), metavar=('FIRST','LAST'))
    p.add_argument('--workers', type=int, choices=(1, 2, 3), default=1)
    p.add_argument('--paired-trials', action='store_true',
                   help='also cover the reflected backward tube using its archived growth rate')
    p.add_argument('--output', type=Path)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/endpoint-jacobians')
    a = p.parse_args()
    lo, hi = a.range
    if not 0 <= lo <= hi < 391 or len(a.endpoints) != len(set(a.endpoints)):
        p.error('choose distinct endpoints and a range within 0–390')
    deps = ['DommaschkJacobianFrames', 'DommaschkJacobianPanels', 'DommaschkStoredPowers']
    if any(label.startswith('q1') for label in a.endpoints):
        deps.append('DommaschkOppositeHarmonic')
    deps.extend(f'DommaschkHarmonicBlock{i:02}' for i in range(lo//8, hi//8+1))
    subprocess.run(['lake', 'build', '--no-build', *['PlasmaLean.Design.'+dep for dep in deps]],
                   cwd=ROOT, stdout=subprocess.DEVNULL, check=True)
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    version = lake('lean','--version')
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    tasks = []
    for label in a.endpoints:
        pairs = {}
        if a.paired_trials:
            from endpoint_reflected_trials import paired_rows
            packet = RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz')
            pairs = {pair.index: pair for pair in paired_rows(packet, lo, hi)}
        for job in endpoint_tasks(label, lo, hi):
            tasks.append((job, pairs.get(job[4]), a.cache.resolve(), version, env))
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        reports = list(pool.map(run_one, tasks, chunksize=1))
    if a.output:
        save(a.output, reports)


if __name__ == '__main__':
    main()
