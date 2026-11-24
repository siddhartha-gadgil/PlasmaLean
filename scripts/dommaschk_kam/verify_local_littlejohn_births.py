"""Certify that open-positive birth laws give positive mass to actual local QA2R Littlejohn orbits."""
from verify_cartesian_mirror_births import verify_passage


NAME = 'DommaschkLocalLittlejohn325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkLocalLittlejohnBirth
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325

/-! # Two signed populations of actual local QA2R guiding-centre solutions -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkLocalLittlejohn325
open Set MeasureTheory Contract Contract.TrappedBirthCoordinates
open DommaschkSignedBirthApproach DommaschkFirstMirrorWell DommaschkCartesianAngleFlow
open DommaschkLocalLittlejohnBirth DommaschkFirstMirrorLaunchSign
set_option maxRecDepth 16384

theorem from_birth : ThroughBirth (fun φ y => BothSigns (point y φ) ∧
    ∀ h ∈ Icc (height false : ℝ) (height true), ‖B (point y φ)‖ < h) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, every⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, band⟩ := every φ small
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have central : |φ| < 316 / 64 := small.trans_lt (by norm_num)
  exact ⟨y, start, from_path path (by norm_num) region band.1 central,
    fun h hh => DommaschkTrappedBirthCoordinates.strict_at_birth band.1 central hh⟩

/-- A nonempty open set of trapped births for each strict velocity sign has genuine
local solutions of the Littlejohn equation and a positive effective parallel field. -/
theorem positive_mass (ν : Measure GCBirth) [Measure.IsOpenPosMeasure ν]
    (m q e h : ℝ) (hm : 0 < m) (hq : q ≠ 0) (he : 0 < e)
    (hh : h ∈ Icc (height false : ℝ) (height true)) (negative : Bool)
    (energies pitches : Set ℝ) (ener : e ∈ interior energies) (pitch : 1 / h ∈ interior pitches) :
    let S : Set GCBirth := {p | if negative then p.2.1 < 0 else 0 < p.2.1}
    0 < ν (interior (localBirths m q S energies pitches)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, every⟩ := from_birth
  obtain ⟨y, _, liftable, strict⟩ := every 0 (by norm_num)
  let S : Set GCBirth := {p | if negative then p.2.1 < 0 else 0 < p.2.1}
  have openS : IsOpen S := by
    have cv : Continuous (fun p : GCBirth => p.2.1) := continuous_fst.comp continuous_snd
    cases negative
    · exact isOpen_lt continuous_const cv
    · exact isOpen_lt cv continuous_const
  have here : lift B m (point y 0) e h negative ∈ interior S := by
    rw [openS.interior_eq]
    exact (lift_values negative hm he (strict h hh)).2.2.1
  exact isOpen_interior.measure_pos ν
    ⟨_, liftable m q e h hm hq he hh negative S energies pitches here ener pitch⟩

theorem positive_volume (m q e h : ℝ) (hm : 0 < m) (hq : q ≠ 0) (he : 0 < e)
    (hh : h ∈ Icc (height false : ℝ) (height true)) (negative : Bool)
    (energies pitches : Set ℝ) (ener : e ∈ interior energies) (pitch : 1 / h ∈ interior pitches) :
    0 < volume (localBirths m q {p | if negative then p.2.1 < 0 else 0 < p.2.1}
      energies pitches) := (positive_mass volume m q e h hm hq he hh negative energies pitches
        ener pitch).trans_le (measure_mono interior_subset)

end PlasmaLean.Design.DommaschkLocalLittlejohn325
'''


if __name__ == '__main__':
    verify_passage(NAME, SOURCE, ['from_birth', 'positive_mass', 'positive_volume'],
                   'DommaschkLocalLittlejohnBirth', 'LocalLittlejohnCache', 'local-littlejohn-birth', __doc__)
