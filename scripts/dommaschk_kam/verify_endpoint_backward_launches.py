"""Prove the first backward physical ODE step by reflecting a checked forward rectangle."""
import argparse
from fractions import Fraction
from pathlib import Path
import subprocess
from types import SimpleNamespace

from emit_position_slabs import step as step_literal
from endpoint_reflected_trials import paired_rows
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_forward_jacobians import PACKAGE as JACOBIANS
from verify_endpoint_physical_launches import reports
from verify_endpoint_reference_slabs import ENDPOINTS, PACKAGE as REFERENCES
from verify_mirror_physical_hit import admitted
from verify_signed_mirror_passage import merge_import_roots
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


PACKAGE = 'EndpointBackwardCache'
FAMILY_PACKAGE = 'EndpointBackwardFamilyCache'


def source(label, pair, jm, fm):
    name = f'DommaschkPhysical{label.upper()}Back000'
    alpha = '(Real.pi / 2)' if label[1]=='1' else '0'
    axis = 'half_pi_axis' if label[1]=='1' else 'zero_axis'
    radius, height = pair.backward_radii
    return name, f'''module
public import PlasmaLean.Design.DommaschkBackwardRectangle
public import PlasmaLean.Design.DommaschkEndpointFirstSlab
public import {JACOBIANS}.{jm}
public import {REFERENCES}.{fm}

/-! # Physical backward launch at {label} -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkPhysicalTraceStep
open DommaschkKam DommaschkBounceField DommaschkJacobian DommaschkMirrorLaunch Set

abbrev previous := MirrorEndpoint.start .{label}
def row : Step := {step_literal(pair.backward)}

theorem checked : test allLimits previous row = true := by with_unfolding_all rfl

theorem center : CenterMatches row {fm}.reference := by
  constructor <;> with_unfolding_all rfl

theorem rectangle : PositionFrameProjection.Rectangle previous.frame row.frame row.trial
    {radius} {height} := by
  constructor <;> unfold PositionFrameProjection.rowFits <;>
    apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl

theorem projected : DommaschkShiftedTrial.Fits row {jm}.trial {radius} {height} := by
  constructor <;> kernel_fact

theorem fits_backward : {jm}.logNorm ≤ row.mu := by kernel_fact

private theorem clock (t : ℝ) : coord 0 t = 128*t-1 := by unfold coord; ring
private theorem window {{t : ℝ}} (h : t ∈ Icc 0 (0 + 1 / 64)) : t ∈ Icc (0 / 64) (1 / 64) := by
  simpa only [zero_div, zero_add] using h

theorem field_bounds : FieldBounds previous row 0 (euclideanFlow {alpha} (-1))
    (velocityJacobian {alpha} (-1)) ballDomain := by
  apply DommaschkBackwardRectangle.field_bounds DommaschkSymmetricSections.{axis} checked
    rectangle projected (by kernel_fact) (left := {jm}.leftFrame) (right := {jm}.rightFrame) rfl rfl
  · intro t ht R z hu hz
    rw [clock] at hu hz
    simpa only [zero_add, atPoint] using {jm}.denominator_pos (window ht) hu hz
  · intro t ht R z hu hz w
    rw [clock] at hu hz ⊢
    have q := {jm}.physical_clock_log_norm (window ht) hu hz w
    have rate : ({jm}.logNorm : ℝ) ≤ (row.mu : ℝ) := Rat.cast_le.mpr fits_backward
    simpa only [zero_add] using q.trans (mul_le_mul_of_nonneg_right rate (sq_nonneg _))
  · intro t ht
    have h := Ico_subset_Icc_self ht
    apply residual_of_pulled ((Bool.and_eq_true_iff.mp checked).1) center h
    have f : residualFrame previous row = {fm}.frame := by with_unfolding_all rfl
    have b : row.defect = {fm}.budget := rfl
    simpa only [clock, f, b] using {fm}.physical_defect (window h)

theorem physical_step : Fields.TrajectorySlabs.Step (euclideanFlow {alpha} (-1))
    (physicalSlab previous row 0) (stateSet previous) (stateSet (next row)) :=
  physical_step_ball checked field_bounds

theorem from_entry {{uC zC uA zA : Theory.KAM.FA}} {{φ : ℝ}}
    (entry : SectionEntry .{label} uC zC uA zA φ) :
    FollowsFrames .{label} uC zC uA zA φ (-1) 1 (next row) [row] :=
  DommaschkEndpointFirstSlab.from_entry entry checked field_bounds

end PlasmaLean.Design.{name}
'''


def bind(label, jac, ref, cache, version, env):
    section, rad = int(label[1]), int(label[3:])
    archive = RECORD.with_name(f'bounce_frame_q{section}_u{rad}.json.gz')
    checksum = digest(archive)
    pair, = paired_rows(archive,0,0)
    jmodule = jac['module']
    bases = (f'DommaschkJacobian{label.upper()}Forward000',f'DommaschkJacobian{label.upper()}PairedForward000')
    if jmodule not in bases or tuple(jac['projected_radii']) != (
            pair.common_radii if jmodule==bases[1] else pair.forward_radii):
        raise ValueError(f'unexpected forward rectangle for {label}')
    if jmodule==bases[0] and (pair.common_radii != pair.forward_radii
                            or Fraction(pair.forward['log_norm_upper']) > Fraction(pair.backward['log_norm_upper'])):
        raise ValueError(f'{label} requires a wider rectangle or a tighter backward rate')
    fmodule = f'DommaschkTraceResidual{label.upper()}Back000'
    roots=[]
    for witness, direction, module in ((jac,1,jmodule),(ref,-1,fmodule)):
        if (witness['endpoint'],witness['direction'],witness['index'],witness['packet_sha256'],
            witness['module'],witness['section_in_half_pi'],Fraction(witness['launch_u'])) != (
                label,direction,0,checksum,module,section,Fraction(rad,1000)):
            raise ValueError(f'wrong signed input for {label}')
        root,=map(Path,witness['import_paths'])
        marker=admitted(root,module,witness['key'])
        if witness['theorems'] != marker['theorems']:
            raise ValueError(f'wrong theorem list for {module}')
        roots.append(root)
    name, code=source(label,pair,jmodule,fmodule)
    names=['checked','center','rectangle','projected','fits_backward','field_bounds','physical_step','from_entry']
    keys=[version,checksum,jac['key'],ref['key'],*(digest(DESIGN/(n+'.trace')) for n in
          ('DommaschkBackwardRectangle','DommaschkEndpointFirstSlab'))]
    root,marker=compile_modules(cache/name,[(name,code,names)],roots,keys,env,PACKAGE)
    report={k:v for k,v in marker.items() if k!='artifacts'}
    report.update(endpoint=label,index=0,direction=-1,packet_sha256=checksum,
                  jacobian_key=jac['key'],residual_key=ref['key'],
                  import_paths=list(map(str,[root,*roots])))
    save(root/'row.json',report)
    print(f'{label} backward physical launch accepted {marker["key"]}',flush=True)
    return report


def all_launches(rows,cache,version,env):
    by_label={r['endpoint']:r for r in rows}
    labels=list(ENDPOINTS[1:])
    if set(by_label)!=set(labels):
        raise ValueError('all seven additional launches are required')
    name='DommaschkAllBackwardLaunches'
    pilot='DommaschkPhysicalBackwardFirstStep'
    lines=['module',f'public import PlasmaLean.Design.{pilot}',
           'public import PlasmaLean.Design.DommaschkEndpointFirstSlab',
           *[f'public import {PACKAGE}.{by_label[e]["module"]}' for e in labels],
           '', '/-! # The eight backward physical launches from the common nested section tori -/',
           '@[expose] public section','noncomputable section','namespace PlasmaLean.Design.'+name,
           'open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointFirstSlab',
           '', 'def row : MirrorEndpoint → Step', '  | .q0r470 => DommaschkJacobianBackward000.row',
           *[f'  | .{e} => {by_label[e]["module"]}.row' for e in labels],
           '', 'def limits : MirrorEndpoint → Limits', '  | .q0r470 => pilotLimits','  | _ => allLimits',
           '', 'theorem launches : CommonBirths row (-1) := by', '  apply common_births row limits (-1)',
           '  · intro e','    cases e',
           '    · simpa only [row, limits, MirrorEndpoint.pilot_starts.2, DommaschkJacobianBackward000.seed]',
           f'        using {pilot}.checked',
           *[f'    · exact {by_label[e]["module"]}.checked' for e in labels],
           '  · intro e', '    cases e',
           '    · simpa only [row, MirrorEndpoint.pilot_starts.2, DommaschkJacobianBackward000.seed,',
           '        MirrorEndpoint.opposite, azimuth, Bool.false_eq_true, ite_false]',
           f'        using {pilot}.field_bounds',
           *[f'    · exact {by_label[e]["module"]}.field_bounds' for e in labels],
           '', 'end PlasmaLean.Design.'+name, '']
    keys=[version,digest(DESIGN/(pilot+'.trace')),digest(DESIGN/'DommaschkEndpointFirstSlab.trace'),
          *[by_label[e]['key'] for e in labels]]
    deps=merge_import_roots(cache,[Path(p) for e in labels for p in by_label[e]['import_paths']],keys)
    root,marker=compile_modules(cache/name,[(name,'\n'.join(lines),['launches'])],[deps],keys,env,FAMILY_PACKAGE)
    result={k:v for k,v in marker.items() if k!='artifacts'}
    result['import_paths']=list(map(str,[root,deps]))
    print(f'All eight common-torus backward launches accepted {marker["key"]}',flush=True)
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoints',choices=ENDPOINTS[1:],nargs='+',required=True)
    p.add_argument('--jacobians',type=Path,nargs='+',required=True)
    p.add_argument('--references',type=Path,nargs='+',required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-backward')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version=lake('lean','--version')
    env=SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                        lean_path=lake('printenv','LEAN_PATH'))
    refs={r['endpoint']:r for r in reports(a.references) if r['index']==0 and r['direction']==-1}
    js={r['endpoint']:r for r in reports(a.jacobians) if r['index']==0 and r['direction']==1}
    if any(label not in js or label not in refs for label in a.endpoints):
        p.error('each selected launch requires a forward Jacobian and a backward central residual')
    results=[bind(label,js[label],refs[label],a.cache.resolve(),version,env) for label in a.endpoints]
    report={'rows':results}
    if set(a.endpoints)==set(ENDPOINTS[1:]):
        report['common_births']=all_launches(results,a.cache.resolve(),version,env)
    if a.output:
        save(a.output,report)


if __name__ == '__main__':
    main()
