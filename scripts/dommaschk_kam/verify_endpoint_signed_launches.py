"""Join the two accepted first-row physical branches on one field line per birth.

The tracked pilot is always included. Supply any subset of the other endpoints
for which both physical first-step reports have already passed.
"""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def read_rows(path):
    records = json.loads(path.read_text())['rows']
    rows = {r['endpoint']: r for r in records}
    if len(rows) != len(records) or not set(rows) <= set(ENDPOINTS[1:]):
        raise ValueError(f'expected distinct non-pilot endpoints in {path}')
    return rows


def verify_dependencies(label, direction, row):
    tag = 'Forward' if direction == 1 else 'Back'
    module = f'DommaschkPhysical{label.upper()}{tag}000'
    packet = RECORD.with_name(f'bounce_frame_q{label[1]}_u{label[3:]}.json.gz')
    if (row['module'], row['direction'], row['index'], row['packet_sha256']) != (
            module, direction, 0, digest(packet)):
        raise ValueError(f'wrong physical first slab for {label}, {tag}')
    root, jac, reference = map(Path, row['import_paths'])
    admitted(root, module, row['key'])
    jac_names = [f'DommaschkJacobian{label.upper()}Forward000',
                 f'DommaschkJacobian{label.upper()}PairedForward000']
    if jac.parent.name not in jac_names:
        raise ValueError(f'wrong spatial tube for {label}')
    admitted(jac, jac.parent.name, row['jacobian_key'])
    admitted(reference, f'DommaschkTraceResidual{label.upper()}{tag}000', row['residual_key'])
    return [root, jac, reference]


def generate(labels, forward, backward):
    all_eight = tuple(labels) == ENDPOINTS
    name = 'DommaschkSignedLaunches' + ('All' if all_eight else ''.join(x.upper() for x in labels))
    src = ['module', 'public import PlasmaLean.Design.DommaschkEndpointSignedTrace',
           'public import PlasmaLean.Design.DommaschkPhysicalFirstStep',
           'public import PlasmaLean.Design.DommaschkPhysicalBackwardFirstStep']
    src += ['public import EndpointPhysicalCache.'+forward[e]['module'] for e in labels[1:]]
    src += ['public import EndpointBackwardCache.'+backward[e]['module'] for e in labels[1:]]
    src += ['', '/-! # Actual signed field lines on a common pair of Q-16 flux surfaces -/',
            '@[expose] public section', 'noncomputable section', 'namespace PlasmaLean.Design.'+name,
            'open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointSignedTrace',
            'set_option linter.style.longLine false', '']
    if all_eight:
        domain = 'MirrorEndpoint'
        src += ['abbrev endpoint (e : MirrorEndpoint) := e']
    else:
        domain = 'Launch'
        src += ['inductive Launch where', *['  | '+e for e in labels],
                'def endpoint : Launch → MirrorEndpoint', *[f'  | .{e} => .{e}' for e in labels]]
    for tag, records, tracked in [('fw', forward, 'DommaschkPhysicalFirstStep.row'),
                                  ('bw', backward, 'DommaschkJacobianBackward000.row')]:
        src += ['', f'def {tag} : {domain} → Step', f'  | .q0r470 => {tracked}',
                *[f'  | .{e} => {records[e]["module"]}.row' for e in labels[1:]]]
    src += ['', '/-- The same physical tori, the same section entry on both sides, and a single',
            'differentiable physical field line through the entire signed interval. -/',
            'theorem launches : Common endpoint (1/64) (fun e => stateSet (next (fw e)))',
            '    (fun e => stateSet (next (bw e))) (fun e => physicalSlabs (endpoint e).start 0 [fw e])',
            '    (fun e => physicalSlabs (endpoint e).start 0 [bw e]) := by',
            '  apply common_of_chains']
    for tag, records in [('fw', forward), ('bw', backward)]:
        src += ['  · intro e', '    cases e']
        for e in labels:
            if e == 'q0r470':
                mod = 'DommaschkPhysicalFirstStep' if tag == 'fw' else 'DommaschkPhysicalBackwardFirstStep'
                field = 'ball_field_bounds' if tag == 'fw' else 'field_bounds'
                seed = (', MirrorEndpoint.pilot_starts.1, DommaschkPhysicalFirstStep.seed' if tag == 'fw'
                        else ', MirrorEndpoint.pilot_starts.2, DommaschkJacobianBackward000.seed')
            else:
                mod = records[e]['module']
                field = 'launch_field_bounds' if tag == 'fw' else 'field_bounds'
                seed = ''
            src += [f'    · apply first_chain (lim := {"pilotLimits" if e == "q0r470" else "allLimits"})',
                    f'      · with_unfolding_all exact {mod}.checked',
                    f'      · simpa [{tag}, endpoint, azimuth, MirrorEndpoint.opposite{seed}] using {mod}.{field}']
    return name, '\n'.join([*src, '', 'end PlasmaLean.Design.'+name, ''])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--forward', required=True, type=Path)
    parser.add_argument('--backward', required=True, type=Path)
    parser.add_argument('--endpoints', nargs='+', choices=ENDPOINTS[1:])
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/signed-endpoint-launches')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    fw, bw = read_rows(args.forward), read_rows(args.backward)
    available = fw.keys() & bw.keys()
    chosen = set(args.endpoints) if args.endpoints else available
    if not chosen or not chosen <= available:
        parser.error('each selected endpoint needs both physical first steps')
    labels = ['q0r470', *[e for e in ENDPOINTS[1:] if e in chosen]]
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    version = lake('lean', '--version')
    args.lean = str(Path(lake('lean', '--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    keys = [version, *[digest(DESIGN/(m+'.trace')) for m in (
        'DommaschkEndpointSignedTrace', 'DommaschkPhysicalFirstStep', 'DommaschkPhysicalBackwardFirstStep')]]
    roots = []
    for e in labels[1:]:
        for d, row in [(1, fw[e]), (-1, bw[e])]:
            roots.extend(verify_dependencies(e, d, row))
            keys.append(row['key'])
    deps = merge_import_roots(args.cache, roots, keys)
    name, source = generate(labels, fw, bw)
    root, marker = compile_modules(args.cache/name, [(name, source, ['launches'])],
                                   [deps], keys, args, 'SignedEndpointCache')
    report = {k:v for k,v in marker.items() if k != 'artifacts'}
    report.update(endpoints=labels, import_paths=list(map(str, (root, deps))))
    save(args.output, report)
    print(name, marker['key'], flush=True)


if __name__ == '__main__':
    main()
