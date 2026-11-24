"""Assemble the first physical forward steps at the other seven N-60 launches.

Supply the signed reference and forward Jacobian verifier reports. With all
seven Jacobians, also bind the tracked pilot and prove the eight birth
statements with a single common pair of Q-16 tori.
"""
import argparse
from fractions import Fraction
import gzip
import json
from pathlib import Path
import subprocess

from emit_position_slabs import step as step_literal
from screen_projected_jacobians import projected_radii
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_reference_slabs import ENDPOINTS, PACKAGE as REFERENCE_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save, source_for
from verify_signed_mirror_passage import merge_import_roots


PACKAGE = 'EndpointPhysicalCache'
JACOBIAN_PACKAGE = 'EndpointJacobianCache'


def reports(files):
    for path in files:
        obj = json.loads(path.read_text())
        yield from obj if isinstance(obj, list) else [obj]


def checked_input(row, label, module, checksum, version):
    if (row['endpoint'] != label or row['direction'] != 1 or row['index'] != 0
            or row['packet_sha256'] != checksum or row.get('lean_version', version) != version
            or row['section_in_half_pi'] != int(label[1])
            or Fraction(row['launch_u']) != Fraction(int(label[3:]), 1000)):
        raise ValueError(f'certificate is for a different physical launch: {label}')
    root, = map(Path, row['import_paths'])
    marker = admitted(root, module, row['key'])
    if row['module'] != module or marker['theorems'] != row['theorems']:
        raise ValueError(f'wrong theorem report for {module}')
    return root


def first_slab(label, jac, ref, args, version):
    section, radius = int(label[1]), int(label[3:])
    archive = RECORD.with_name(f'bounce_frame_q{section}_u{radius}.json.gz')
    checksum = digest(archive)
    jac_module = f'DommaschkJacobian{label.upper()}Forward000'
    ref_module = f'DommaschkTraceResidual{label.upper()}Forward000'
    jac_root = checked_input(jac, label, jac_module, checksum, version)
    ref_root = checked_input(ref, label, ref_module, checksum, version)
    with gzip.open(archive, 'rt') as file:
        packet = json.load(file)
    if (packet['section_in_half_pi'], Fraction(packet['launch_u'])) != (section, Fraction(radius, 1000)):
        raise ValueError(f'wrong packet for {label}')
    forward, = (trace for trace in packet['traces'] if trace['direction'] == 1)
    row = forward['steps'][0]
    scale = packet['frame_denominator']
    radii = projected_radii([[scale, 0], [0, scale]], row['frame_end'], row['frame_trial_radius'])
    if row['index'] != 0 or tuple(jac['projected_radii']) != radii:
        raise ValueError(f'wrong spatial projection for {label}')
    name, source = source_for(0, row['physical_trial_radius'], jac_module, ref_module,
                              JACOBIAN_PACKAGE, radii, endpoint=label,
                              position_row=step_literal(row), opposite=bool(section),
                              central_package=REFERENCE_PACKAGE)
    before_end = f'end PlasmaLean.Design.{name}\n'
    entry = f'''
/-- The exact section clock and launch state used by the nested-torus theorem. -/
theorem launch_field_bounds :
    FieldBounds previous row 0
      (euclideanFlow (DommaschkMirrorLaunch.azimuth (DommaschkMirrorLaunch.MirrorEndpoint.{label}).opposite) 1)
      (velocityJacobian (DommaschkMirrorLaunch.azimuth (DommaschkMirrorLaunch.MirrorEndpoint.{label}).opposite) 1)
      ballDomain := by
  simpa [DommaschkMirrorLaunch.azimuth, DommaschkMirrorLaunch.MirrorEndpoint.opposite] using field_bounds

/-- The actual physical approach to the section and the enclosed first row have the same state. -/
theorem from_entry {{uC zC uA zA : Theory.KAM.FA}} {{φ : ℝ}}
    (entry : DommaschkMirrorLaunch.SectionEntry .{label} uC zC uA zA φ) :
    DommaschkMirrorLaunch.FollowsFrames .{label} uC zC uA zA φ 1 1 (next row) [row] :=
  DommaschkEndpointFirstSlab.from_entry entry checked launch_field_bounds

'''
    source = source.removesuffix(before_end) + entry + before_end
    static = ['DommaschkEndpointFirstSlab', 'DommaschkPhysicalTraceStep', 'DommaschkProjectedTrial']
    keys = [checksum, version, jac['key'], ref['key'], *[digest(DESIGN/(s+'.trace')) for s in static]]
    names = ['checked', 'field_bounds', 'physical_step', 'launch_field_bounds', 'from_entry']
    root, marker = compile_modules(args.cache/name, [(name, source, names)],
                                   [jac_root, ref_root], keys, args, PACKAGE)
    report = {k: v for k, v in marker.items() if k != 'artifacts'}
    report.update(endpoint=label, index=0, direction=1, packet_sha256=checksum,
                  jacobian_key=jac['key'], residual_key=ref['key'],
                  import_paths=list(map(str, (root, jac_root, ref_root))))
    return report


def family(rows, args, version):
    names = {'q0r470': 'DommaschkPhysicalFirstStep', **{r['endpoint']: r['module'] for r in rows}}
    name = 'DommaschkAllForwardLaunches'
    lines = ['module', 'public import PlasmaLean.Design.DommaschkPhysicalFirstStep',
             'public import PlasmaLean.Design.DommaschkEndpointFirstSlab',
             *[f'public import {PACKAGE}.{names[e]}' for e in ENDPOINTS[1:]], '',
             '/-! # First physical forward slab from all eight Q-16 launch sectors -/',
             '@[expose] public section', 'noncomputable section', 'namespace PlasmaLean.Design.'+name,
             'open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointFirstSlab', '',
             'def row : MirrorEndpoint → Step',
             *[f'  | .{e} => {names[e]}.row' for e in ENDPOINTS], '',
             'def limits : MirrorEndpoint → Limits', '  | .q0r470 => pilotLimits', '  | _ => allLimits', '',
             '/-- The same physical tori furnish all eight certified forward launches. -/',
             'theorem launches : CommonBirths row 1 := by', '  apply common_births row limits 1',
             '  · intro e', '    cases e',
             *[f'    · with_unfolding_all exact {names[e]}.checked' for e in ENDPOINTS],
             '  · intro e', '    cases e',
             '    · simpa [row, azimuth, MirrorEndpoint.opposite, MirrorEndpoint.pilot_starts.1,',
             '        DommaschkPhysicalFirstStep.seed] using DommaschkPhysicalFirstStep.ball_field_bounds',
             *[f'    · exact {names[e]}.launch_field_bounds' for e in ENDPOINTS[1:]], '',
             'end PlasmaLean.Design.'+name, '']
    package = 'EndpointForwardFamilyCache'
    keys = [version, package, digest(DESIGN/'DommaschkPhysicalFirstStep.trace'),
            digest(DESIGN/'DommaschkEndpointFirstSlab.trace'), *[r['key'] for r in rows]]
    deps = merge_import_roots(args.cache, [Path(p) for r in rows for p in r['import_paths']], keys)
    root, marker = compile_modules(args.cache/name, [(name, '\n'.join(lines), ['launches'])],
                                   [deps], keys, args, package)
    return {'module': name, 'key': marker['key'], 'theorems': marker['theorems'],
            'axioms': marker['axioms'], 'import_paths': list(map(str, (root, deps)))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--references', nargs='+', type=Path, required=True)
    parser.add_argument('--jacobians', nargs='+', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/endpoint-physical')
    args = parser.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    version = lake('lean', '--version')
    args.lean = str(Path(lake('lean', '--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    refs = {r['endpoint']: r for r in reports(args.references) if r['direction'] == 1 and r['index'] == 0}
    jac = {r['endpoint']: r for r in reports(args.jacobians) if r['direction'] == 1 and r['index'] == 0}
    if not jac or not set(jac) <= set(ENDPOINTS[1:]) or not set(jac) <= set(refs):
        parser.error('the selected non-pilot forward Jacobians require matching first-slab references')
    rows = [first_slab(e, jac[e], refs[e], args, version) for e in ENDPOINTS[1:] if e in jac]
    result = {'rows': rows}
    if len(rows) == len(ENDPOINTS)-1:
        result['common_births'] = family(rows, args, version)
    save(args.output, result)
    for r in [*rows, *([result['common_births']] if 'common_births' in result else [])]:
        print(r['module'], r['key'], flush=True)


if __name__ == '__main__':
    main()
