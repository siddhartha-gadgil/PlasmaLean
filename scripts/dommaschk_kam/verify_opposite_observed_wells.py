"""Identify the original opposite birth on the actual trace and bound independent first-well observations."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from time import sleep

from bounce_common_section import section_polynomial_data
from bounce_mirror_pilot import HEIGHTS
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import panel_row
from replay_physical_action_archive import segment
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_opposite_action_subwell import CUT, NAME, PACKAGE, load
from verify_opposite_inner_ode_group import CHECKSUM
from verify_opposite_inner_trajectory import TOP
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


THEORY='DommaschkOppositeFirstWellObservation'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for f in ['packet','core','trajectory','output']:
        p.add_argument('--'+f,type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-observed-wells')
    p.add_argument('--wait-for-trajectory',action='store_true',
                   help='wait for atomic publication of the authenticated through receipt')
    a=p.parse_args()
    if a.wait_for_trajectory and not a.trajectory.is_file():
        print(f'Waiting for {a.trajectory}',flush=True)
        while not a.trajectory.is_file():
            sleep(30)
    tr=json.loads(a.trajectory.read_text()); core=json.loads(a.core.read_text())
    n=tr['length']; prefix=tr['module']
    if (digest(a.packet)!=CHECKSUM or (tr['packet_sha256'],core['packet_sha256'],tr['core'],core['package'])!=
        (CHECKSUM,CHECKSUM,core['key'],PACKAGE) or core['module']!=NAME or not 0<n<=CUT or
        prefix!=f'DommaschkOppositeInnerThrough{n:03}' or tr['panels']!=2*n*24):
        p.error('expected the original signed q1r470 trajectory and its full positive core')
    roots=list(map(Path,tr['import_paths']))
    parent=admitted(roots[0],prefix,tr['key'])
    if f'PlasmaLean.Design.{prefix}.from_nested_tori' not in parent['theorems']:
        p.error('trajectory does not carry the original nested-torus births')
    admitted(Path(core['import_paths'][0]),NAME,core['key'])
    data=section_polynomial_data(1); strength=ShiftedStrength(data)
    packet=load(a.packet)
    total=sum(panel_row(segment(t,i),data,strength,HEIGHTS[1],False,24)[1]
              for t in packet['traces'] for i in range(n))
    raw=F(total,3072*2**40)
    name=f'DommaschkOppositeObservedWells{n:03}'
    pn=f'DommaschkOppositeInnerRows{n:03}'
    src=f'''module
public import {TOP}.{prefix}
public import {PACKAGE}.{NAME}
public import PlasmaLean.Design.{THEORY}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature
open DommaschkOppositeFirstWellObservation DommaschkNativeWellAction DommaschkMirrorLaunch
open DommaschkOppositeInnerTrajectory DommaschkOppositeInnerSeed DommaschkSignedTraceDomain
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
set_option linter.style.longLine false
set_option maxRecDepth 18000
set_option maxHeartbeats 0

abbrev floorMass : ℝ := {raw.numerator}/{raw.denominator}
private theorem positive : {prefix}.blocks.all (fun b => Certificates.PositiveSubwell.positive 48 b.packed) = true := by
  apply List.all_eq_true.mpr
  intro b hb
  apply List.all_eq_true.mp {NAME}.positive_all b
  exact List.mem_of_mem_drop (List.mem_of_mem_take hb)

def Physical (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  (∃ (x : Plane) (y : ℝ → Plane), Trace {n} {pn}.forward {pn}.backward x y ∧
    y (φ-phase) = coordinates.symm (birth uC zC uA zA u φ) ∧
    Covers false (valueW y) (valueF y) level (-{n}/64) {prefix}.blocks) ∧
  (∀ J, Measures uC zC uA zA φ level J → floorMass ≤ J)

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (small : |φ-phase| ≤ width)
    (entry : Entry uC zC uA zA φ) : Physical uC zC uA zA φ := by
  have lf : 0 < {pn}.forward.length := by rw [{pn}.forward_length]; norm_num
  have lb : 0 < {pn}.backward.length := by rw [{pn}.backward_length]; norm_num
  have checkF : packed ({pn}.forward[0]'lf) = true := by kernel_fact
  have checkB : packed ({pn}.backward[0]'lb) = true := by kernel_fact
  obtain ⟨x,y,trace,actual,cells⟩ := born small (by norm_num : 0 < {n}) lf lb checkF checkB ({prefix}.original_birth entry)
  refine ⟨⟨x,y,trace,actual,cells⟩,fun J observation => ?_⟩
  have room : φ-phase ∈ Icc (-({n}:ℝ)/64) ({n}/64) := by
    obtain ⟨l,r⟩ := abs_le.mp small
    unfold width at l r
    constructor <;> linarith
  have len : {prefix}.blocks.length = {n}+{n} := by with_unfolding_all rfl
  have lower := lower_on_measurement len positive trace actual room cells observation
  have sum : total {prefix}.blocks = {total} := by kernel_fact
  rw [sum] at lower
  norm_num [floorMass] at lower ⊢
  exact lower

/-- At the full central cutoff there are no further spatial-cell or mirror-cap premises
beyond an actual birth-bound trace carrying the recorded cover. -/
theorem full_exclusion {{uC zC uA zA : FA}} {{φ J : ℝ}} {{fr br : List Step}} {{x : Plane}} {{y : ℝ → Plane}}
    (trace : Trace 320 fr br x y) (small : |φ-phase| ≤ width)
    (birth_at : y (φ-phase) = coordinates.symm (birth uC zC uA zA u φ))
    (cells : Covers false (valueW y) (valueF y) level (-5) {NAME}.slabs)
    (observation : Measures uC zC uA zA φ level J) : target+3/10000 < J := by
  have room : φ-phase ∈ Icc (-(320:ℝ)/64) (320/64) := by
    obtain ⟨l,r⟩ := abs_le.mp small
    unfold width at l r
    constructor <;> linarith
  have floor := lower_on_measurement (show {NAME}.slabs.length = 320+320 from {NAME}.checked.len)
    {NAME}.positive_all trace birth_at room (by convert cells using 1; norm_num) observation
  have sum : total {NAME}.slabs = {F(core['mass'])*3072*2**40} := by kernel_fact
  rw [sum] at floor
  exact lt_of_lt_of_le (by norm_num [target]) floor

theorem from_nested_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ, |φ-phase| ≤ width → Physical uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,iC,iA,nested,eC,eA,entry⟩ := DommaschkOppositeInnerSeed.from_nested_tori
  exact ⟨uC,zC,uA,zA,R,Z,C,A,iC,iA,nested,eC,eA,fun φ h => from_entry h (entry φ h)⟩

end PlasmaLean.Design.{name}
'''
    declarations=['from_entry','full_exclusion','from_nested_tori']
    if n==CUT:
        ending=f'end PlasmaLean.Design.{name}'
        src=src.replace(ending,f'''/-- The completed physical campaign gives a strict action obstruction for each independent
regular first-well observation through any of the admitted original births. -/
theorem grounded_exclusion {{uC zC uA zA : FA}} {{φ J : ℝ}}
    (small : |φ-phase| ≤ width) (entry : Entry uC zC uA zA φ)
    (measurement : Measures uC zC uA zA φ level J) : target+3/10000 < J := by
  have mass := (from_entry small entry).2 J measurement
  exact lt_of_lt_of_le (by norm_num [target,floorMass]) mass

{ending}''')
        declarations.append('grounded_exclusion')
    env(a)
    deps=[CHECKSUM,a.version,core['key'],tr['key'],digest(DESIGN/(THEORY+'.trace'))]
    item=name,src,declarations
    root,r=compile_modules(a.cache/name,[item],roots,deps,a,'OppositeObservedWellCache')
    out={k:v for k,v in r.items() if k!='artifacts'}
    out.update(trajectory=tr['key'],packet_sha256=CHECKSUM,length=n,core=core['key'],
               floor=str(raw),import_paths=list(map(str,[root,*roots])))
    save(a.output,out)
    print(name,r['key'],out['floor'],flush=True)


if __name__=='__main__':
    main()
