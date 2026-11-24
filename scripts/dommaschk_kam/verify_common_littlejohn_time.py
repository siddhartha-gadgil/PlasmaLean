"""Certify common positive Littlejohn time and prescribed displacement for both QA2R signs."""
from verify_cartesian_mirror_births import verify_passage


NAME = 'DommaschkCommonLittlejohn325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkCommonLittlejohnTime
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325

/-! # Uniform local Littlejohn motion for the original QA2R trapped births -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCommonLittlejohn325
open Set MeasureTheory Fields Contract Contract.TrappedBirthCoordinates
open Kinetic.VacuumLittlejohnWindow
open DommaschkSignedBirthApproach DommaschkFirstMirrorWell DommaschkCartesianAngleFlow
open DommaschkCommonLittlejohnTime DommaschkFirstMirrorLaunchSign
set_option maxRecDepth 16384

/-- Both sign lifts of every original interpolated birth have one common positive time.
Every admissible finite measurable reference also satisfies the contracted radial band. -/
theorem from_birth : ThroughBirth (fun φ y => UniformAt (point y φ) ∧ BandAt (point y φ)) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, every⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, band⟩ := every φ small
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have u := from_path path (by norm_num) region band.1 (small.trans_lt (by norm_num))
  exact ⟨y, start, u, u.band⟩

/-- The original central launch yields positive mass of each sign without any finiteness
assumption on the measure. Both populations share the same closed time interval. -/
theorem common_positive_mass (ν : Measure GCBirth) [Measure.IsOpenPosMeasure ν]
    (m q e h d : ℝ) (hm : 0 < m) (hq : q ≠ 0) (he : 0 < e)
    (hh : h ∈ Icc (height false : ℝ) (height true)) (hd : 0 < d)
    (energies pitches : Set ℝ) (ener : e ∈ interior energies) (pitch : 1 / h ∈ interior pitches) :
    ∃ T > 0, ∀ neg : Bool, ∃ W : Set GCBirth, IsOpen W ∧ 0 < ν W ∧
      W ⊆ trappedReference B m univ energies pitches ∩ signSet neg ∧
      ∀ b ∈ W, Control B m q T d b := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, every⟩ := from_birth
  obtain ⟨y, _, u, _⟩ := every 0 (by norm_num)
  obtain ⟨T, pos, both⟩ :=
    u m q e h d hm hq he hh hd (fun _ => univ) energies pitches (by simp) ener pitch
  refine ⟨T, pos, fun neg => ?_⟩
  obtain ⟨W, op, occurs, inside, control⟩ := both neg
  exact ⟨W, op, op.measure_pos ν ⟨_, occurs⟩, inside, control⟩

end PlasmaLean.Design.DommaschkCommonLittlejohn325
'''


if __name__ == '__main__':
    verify_passage(NAME, SOURCE, ['from_birth', 'common_positive_mass'],
                   'DommaschkCommonLittlejohnTime', 'CommonLittlejohnCache',
                   'common-littlejohn-window', __doc__)
