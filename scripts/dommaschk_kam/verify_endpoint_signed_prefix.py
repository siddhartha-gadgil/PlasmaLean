"""Extend the signed physical launch at a non-pilot endpoint using its own archived steps."""

import argparse
from fractions import Fraction
from pathlib import Path
import subprocess

from emit_position_slabs import step as step_literal
from screen_independent_endpoint_frames import trial_frames
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_backward_launches import PACKAGE as BACKWARD
from verify_endpoint_forward_jacobians import PACKAGE as JACOBIAN
from verify_endpoint_physical_launches import PACKAGE as FORWARD, reports
from verify_endpoint_reference_slabs import ENDPOINTS, PACKAGE as REFERENCE
from verify_endpoint_signed_launches import read_rows, verify_dependencies
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


PACKAGE = 'EndpointPrefixCache'
SIGNED_PACKAGE = 'EndpointSignedPrefixCache'
DEPENDENCY = 'DommaschkEndpointContinuation'


def input_root(row, label, direction, index, module, checksum, version):
    if (row['endpoint'], row['direction'], row['index'], row['module'], row['packet_sha256'],
        row['section_in_half_pi'], Fraction(row['launch_u']), row.get('lean_version', version)) != (
            label, direction, index, module, checksum, int(label[1]), Fraction(int(label[3:]), 1000), version):
        raise ValueError(f'incorrect endpoint, direction, clock, or packet in {module}')
    root, = map(Path, row['import_paths'])
    if admitted(root, module, row['key'])['theorems'] != row['theorems']:
        raise ValueError(f'wrong theorem list for {module}')
    return root


def physical_source(label, sign, pair, previous, jac, ref, reference_package=REFERENCE):
    i = pair.index
    tag = 'Forward' if sign == 1 else 'Back'
    angle = '0' if label[1] == '0' else '(Real.pi / 2)'
    axis = 'zero_axis' if label[1] == '0' else 'half_pi_axis'
    rate = '1' if sign == 1 else '(-1)'
    row = pair.forward if sign == 1 else pair.backward
    radial, vertical = pair.common_radii if sign == 1 else pair.backward_radii
    name = f'DommaschkPhysical{label.upper()}{tag}{i:03}'
    if sign == 1:
        prepare = f'''  have hm : CenterMatches row {jac}.trial := by constructor <;> with_unfolding_all rfl
  have hu : ({jac}.trial.u.radius : ℝ) = ({radial} : ℝ) / 2^80 := by
    change (({radial} / 2^80 : ℚ) : ℝ) = _
    norm_num
  have hz : ({jac}.trial.z.radius : ℝ) = ({vertical} : ℝ) / 2^80 := by
    change (({vertical} / 2^80 : ℚ) : ℝ) = _
    norm_num
  apply DommaschkEndpointContinuation.forward_rectangle checked rectangle hm hu hz'''
    else:
        prepare = f'''  have fits : DommaschkShiftedTrial.Fits row {jac}.trial {radial} {vertical} := by
    constructor <;> kernel_fact
  apply DommaschkBackwardRectangle.field_bounds DommaschkSymmetricSections.{axis}
    checked rectangle fits'''
    return name, f'''module
public import PlasmaLean.Design.{DEPENDENCY}
public import {JACOBIAN}.{jac}
public import {reference_package}.{ref}

/-! # Physical {tag.lower()} continuation at {label}, slab {i} -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates PositionFrameSlabs DommaschkPhysicalTraceStep DommaschkBounceField DommaschkJacobian Set

def previous : PositionFrameSlabs.State := next ({step_literal(previous)})
def row : Step := {step_literal(row)}

theorem checked : test allLimits previous row = true := by with_unfolding_all rfl

private theorem clock (t : ℝ) : coord ({i}/64) t = 128*t-{2*i+1} := by unfold coord; ring
private theorem stop : ({i}/64 : ℝ) + 1/64 = {i+1}/64 := by norm_num

theorem field_bounds : FieldBounds previous row ({i}/64) (euclideanFlow {angle} {rate})
    (velocityJacobian {angle} {rate}) ballDomain := by
  have rectangle : PositionFrameProjection.Rectangle previous.frame row.frame row.trial
      {radial} {vertical} := by
    constructor <;> unfold PositionFrameProjection.rowFits <;>
      apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl
{prepare}
    (by kernel_fact) (left := {jac}.leftFrame) (right := {jac}.rightFrame) rfl rfl
  · intro t ht R z hu hz
    rw [clock] at hu hz
    simpa only [zero_add, atPoint] using {jac}.denominator_pos (stop ▸ ht) hu hz
  · intro t ht R z hu hz w
    rw [clock] at hu hz ⊢
    have q := {jac}.physical_clock_log_norm (stop ▸ ht) hu hz w
    have rate : ({jac}.logNorm : ℝ) ≤ (row.mu : ℝ) := Rat.cast_le.mpr (by kernel_fact)
    simpa only [zero_add] using q.trans (mul_le_mul_of_nonneg_right rate (sq_nonneg _))
  · intro t ht
    have h := Ico_subset_Icc_self ht
    have center : CenterMatches row {ref}.reference := by constructor <;> with_unfolding_all rfl
    apply residual_of_pulled ((Bool.and_eq_true_iff.mp checked).1) center h
    have f : residualFrame previous row = {ref}.frame := by with_unfolding_all rfl
    have b : row.defect = {ref}.budget := rfl
    simpa only [clock, f, b] using {ref}.physical_defect (stop ▸ h)

theorem physical_step : Fields.TrajectorySlabs.Step (euclideanFlow {angle} {rate})
    (physicalSlab previous row ({i}/64)) (stateSet previous) (stateSet (next row)) :=
  physical_step_ball checked field_bounds

end PlasmaLean.Design.{name}
'''


def prefix_source(label, branches):
    n = len(branches[1])
    name = f'DommaschkSignedPrefix{label.upper()}{n:03}'
    lines = ['module', 'public import PlasmaLean.Design.' + DEPENDENCY]
    for sign, launch_package in [(1, FORWARD), (-1, BACKWARD)]:
        for i, row in enumerate(branches[sign]):
            lines.append(f'public import {PACKAGE if i else launch_package}.{row["module"]}')
    lines += ['', '/-! # Two physical chains through one admissible Q-16 section entry -/',
              '@[expose] public section', 'noncomputable section', 'namespace PlasmaLean.Design.' + name,
              'open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointSignedTrace',
              'open DommaschkEndpointContinuation DommaschkJacobian', 'set_option maxRecDepth 8192',
              f'abbrev endpoint := MirrorEndpoint.{label}']
    for sign, branch, rate in [(1, 'forward', '1'), (-1, 'backward', '(-1)')]:
        modules = [r['module'] for r in branches[sign]]
        rows = ', '.join(module+'.row' for module in modules)
        lines += ['', f'def {branch}Rows : List Step := [{rows}]',
                  f'abbrev {branch}Exit := next {modules[-1]}.row',
                  f'theorem {branch}_chain : Fields.TrajectorySlabs.Chain',
                  f'    (euclideanFlow (azimuth endpoint.opposite) {rate}) 0 (stateSet endpoint.start)',
                  f'    ({n}/64) (stateSet {branch}Exit) (physicalSlabs endpoint.start 0 {branch}Rows) := by',
                  f'  unfold {branch}Rows', '  rw [show (0 : ℝ) = ((0:ℕ):ℝ)/64 by norm_num]']
        for i, module in enumerate(modules):
            lines += [f'  apply cons_step {i}', f'  · rw [show (({i}:ℕ):ℝ)/64 = {i}/64 by norm_num]']
            if i:
                lines += [f'    have link : {module}.previous = next {modules[i-1]}.row := by',
                          '      with_unfolding_all rfl']
            simplify = 'endpoint, azimuth, MirrorEndpoint.opposite' + (', link' if i else '')
            lines += [f'    with_unfolding_all simpa [{simplify}]',
                      f'      using {module}.physical_step']
        lines += [f'  rw [show ((({n-1}+1:ℕ):ℝ)/64) = {n}/64 by norm_num]',
                  f'  exact Fields.TrajectorySlabs.Chain.nil (F := euclideanFlow (azimuth endpoint.opposite) {rate}) _ _']
    lines += ['', 'theorem from_entry {uC zC uA zA : Theory.KAM.FA} {φ : ℝ}',
              '    (entry : SectionEntry endpoint uC zC uA zA φ) :',
              f'    FromBirth endpoint uC zC uA zA φ ({n}/64) (stateSet forwardExit) (stateSet backwardExit)',
              '      (physicalSlabs endpoint.start 0 forwardRows) (physicalSlabs endpoint.start 0 backwardRows) :=',
              '  DommaschkEndpointSignedTrace.from_entry entry forward_chain backward_chain',
              '', f'theorem from_birth : Common (fun _ : Unit => endpoint) ({n}/64)',
              '    (fun _ => stateSet forwardExit) (fun _ => stateSet backwardExit)',
              '    (fun _ => physicalSlabs endpoint.start 0 forwardRows)',
              '    (fun _ => physicalSlabs endpoint.start 0 backwardRows) :=',
              '  common_of_chains _ (fun _ => forward_chain) (fun _ => backward_chain)',
              '', f'theorem common_with_pilot : WithPilot endpoint ({n}/64)',
              '    (stateSet forwardExit) (stateSet backwardExit)',
              '    (physicalSlabs endpoint.start 0 forwardRows) (physicalSlabs endpoint.start 0 backwardRows) :=',
              '  with_pilot_of_entry from_entry',
              '', 'end PlasmaLean.Design.' + name, '']
    return name, '\n'.join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint', choices=ENDPOINTS[1:], required=True)
    p.add_argument('--length', type=int, required=True)
    p.add_argument('--forward-launches', type=Path, required=True)
    p.add_argument('--backward-launches', type=Path, required=True)
    p.add_argument('--references', type=Path, nargs='+', required=True)
    p.add_argument('--jacobians', type=Path, nargs='+', required=True)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/endpoint-prefixes')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    label, n = args.endpoint, args.length
    if not 2 <= n <= 391:
        p.error('length must be between 2 and 391')
    args.cache = args.cache.resolve()
    packet = RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz')
    checksum = digest(packet)
    subprocess.run(['lake', 'build', '--no-build', 'PlasmaLean.Design.' + DEPENDENCY], cwd=ROOT,
                   check=True, stdout=subprocess.DEVNULL)
    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()
    version = lake('lean','--version')
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    base = [checksum, version, digest(DESIGN/(DEPENDENCY+'.trace'))]
    references = {(r['direction'],r['index']): r for r in reports(args.references) if r['endpoint'] == label}
    jacobians = {(r['index'],r.get('matrix_direction')): r for r in reports(args.jacobians)
                 if r['endpoint'] == label}
    roots, keys, branches = [], [], {1: [], -1: []}
    for sign, launch in [(1, args.forward_launches), (-1, args.backward_launches)]:
        first = read_rows(launch)[label]
        roots.extend(verify_dependencies(label, sign, first))
        keys.append(first['key'])
        branches[sign].append(first)
    frames = list(trial_frames(packet, 0, n-1))
    for i in range(1,n):
        pair, reflected = frames[i]
        prev = frames[i-1][0]
        loaded = {}
        for sign, tag in [(1, 'Forward'), (-1, 'Back')]:
            jac = jacobians.get((i,sign),jacobians.get((i,None)))
            if jac is None:
                raise ValueError(f'missing signed spatial matrix for {label} row {i} direction {sign}')
            joint = 'matrix_direction' not in jac
            if joint and (pair.forward_left != reflected.forward_left or
                          pair.forward['frame_end'] != reflected.forward['frame_end']):
                raise ValueError(f'{label} row {i} requires a separately verified backward frame')
            suffix = 'PairedForward' if joint else 'Independent'+tag
            jm = f'DommaschkJacobian{label.upper()}{suffix}{i:03}'
            target = min(pair.common_rate,reflected.common_rate) if joint else (
                pair.common_rate if sign==1 else reflected.common_rate)
            if (not jac.get('paired_trials') or tuple(jac['projected_radii']) != pair.common_radii
                    or Fraction(jac['common_rate']) != target):
                raise ValueError(f'incorrect rectangle or frame budget for {label} row {i}')
            if jm not in loaded:
                jacdir = input_root(jac,label,1,i,jm,checksum,version)
                jac_roots = [jacdir]
                jac_import = jacdir
                if 'shared_parents' in jac:
                    from verify_horner_endpoint_jacobian import checked_shared_roots
                    jac_roots.extend(checked_shared_roots(jac,jacdir,version))
                    jac_import = merge_import_roots(args.cache,jac_roots,[jac['key'],'physical-field-imports'])
                loaded[jm] = jac_import,jac_roots
            jac_import,jac_roots = loaded[jm]
            ref = references[sign,i]
            fm = f'DommaschkTraceResidual{label.upper()}{tag}{i:03}'
            refdir = input_root(ref,label,sign,i,fm,checksum,version)
            ref_roots = [refdir]
            reference_package = REFERENCE
            if 'reflected_forward' in ref:
                from verify_reflected_endpoint_residuals import PACKAGE as reflected_package, checked_reflected_parent
                if sign != -1 or ref['package'] != reflected_package:
                    raise ValueError('incorrect direction or package for a reflected central defect')
                ref_roots.append(checked_reflected_parent(ref,refdir,version))
                reference_package = reflected_package
            elif 'native_parents' in ref:
                from verify_native_endpoint_residuals import PACKAGE as native_package, checked_parents
                if ref['package'] != native_package or not label.startswith('q0'):
                    raise ValueError('incorrect section or package for a native central defect')
                native = [refdir, *checked_parents(ref,refdir,version)]
                ref_roots = [merge_import_roots(args.cache,native,[ref['key'],'native-central-imports'])]
                reference_package = native_package
            source = physical_source(label, sign, pair, prev.forward if sign == 1 else prev.backward,
                                     jm, fm, reference_package)
            name, code = source
            root, row = compile_modules(args.cache/name, [(name, code, ['checked','field_bounds','physical_step'])],
                [jac_import, *ref_roots], [*base,jac['key'],ref['key']], args, PACKAGE)
            roots.extend([*jac_roots, *ref_roots, root])
            keys.append(row['key'])
            branches[sign].append({k: v for k, v in row.items() if k != 'artifacts'} |
                {'index': i, 'direction': sign, 'endpoint': label, 'packet_sha256': checksum,
                 'jacobian_key': jac['key'], 'residual_key': ref['key'],
                 'import_paths': list(map(str, [root, jac_import, *ref_roots]))})
            print(f'{label} {tag} {i} accepted {row["key"]}',flush=True)
    imports = merge_import_roots(args.cache, roots, keys)
    name, code = prefix_source(label,branches)
    theorems = ['forward_chain','backward_chain','from_entry','from_birth','common_with_pilot']
    root, receipt = compile_modules(args.cache/name, [(name,code,theorems)], [imports],
                                    [SIGNED_PACKAGE,*base,keys], args, SIGNED_PACKAGE)
    overlay = merge_import_roots(args.cache, [imports,root], [*keys,receipt['key']])
    result = {k: v for k,v in receipt.items() if k != 'artifacts'}
    result.update(endpoint=label, packet_sha256=checksum, length_each_direction=n,
                  launch_u=str(Fraction(int(label[3:]),1000)), lean_version=version,
                  interval=[str(Fraction(-n,64)),str(Fraction(n,64))],
                  rows=branches, proof_root=str(root), import_path=str(overlay))
    save(args.output,result)
    print(f'{name}.from_birth accepted {receipt["key"]}',flush=True)


if __name__ == '__main__':
    main()
