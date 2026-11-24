"""Realize the five-dimensional contracted QA2R trapped reference for both parallel velocity signs."""
from verify_cartesian_mirror_births import verify_passage


NAME = 'DommaschkThermalReference325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkTrappedBirthCoordinates
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325

/-! # Positive mass in the actual position, parallel velocity and magnetic moment variables -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkThermalReference325
open Set MeasureTheory Contract Contract.TrappedBirthCoordinates
open DommaschkSignedBirthApproach DommaschkCartesianAngleFlow DommaschkFirstMirrorWell
open DommaschkTrappedBirthCoordinates DommaschkFirstMirrorLaunchSign
set_option maxRecDepth 16384

/-- Every pilot angle supplies both physical velocity signs at any positive energy and
at all the pilot heights. Open support, energy and pitch cuts persist about each lift. -/
theorem from_birth : ThroughBirth (fun φ y => Lifted (point y φ)) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, every⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, band⟩ := every φ small
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  exact ⟨y, start, from_path path (by norm_num) region band.1 (small.trans_lt (by norm_num))⟩

/-- For a symbolic species mass, energy and attained reciprocal pitch, any open-positive
law charges the contracted reference with either prescribed strict velocity sign. -/
theorem signed_positive_mass (ν : Measure GCBirth) [Measure.IsOpenPosMeasure ν]
    (m e h : ℝ) (hm : 0 < m) (he : 0 < e) (hh : h ∈ Icc (height false : ℝ) (height true))
    (negative : Bool) (energies pitches : Set ℝ) (ener : e ∈ interior energies)
    (pitch : 1 / h ∈ interior pitches) :
    let S : Set GCBirth := {p | if negative then p.2.1 < 0 else 0 < p.2.1}
    0 < ν (interior (trappedReference B m S energies pitches)) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, every⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  obtain ⟨y, start, x, path, band⟩ := every 0 (by norm_num)
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have phase : |(0:ℝ)| < 316 / 64 := by norm_num
  have live := from_path path (by norm_num) region band.1 phase
  have strict := strict_at_birth band.1 phase hh
  let S : Set GCBirth := {p | if negative then p.2.1 < 0 else 0 < p.2.1}
  have openS : IsOpen S := by
    have cv : Continuous (fun p : GCBirth => p.2.1) := continuous_fst.comp continuous_snd
    cases negative
    · exact isOpen_lt continuous_const cv
    · exact isOpen_lt cv continuous_const
  have here : lift B m (point y 0) e h negative ∈ interior S := by
    rw [openS.interior_eq]
    exact (lift_values negative hm he strict).2.2.1
  exact positive_mass ν (live m e h hm he hh negative S energies pitches here ener pitch)

/-- Lebesgue measure in the five original coordinates charges both signs of the physical reference. -/
theorem signed_positive_volume (m e h : ℝ) (hm : 0 < m) (he : 0 < e)
    (hh : h ∈ Icc (height false : ℝ) (height true)) (negative : Bool)
    (energies pitches : Set ℝ) (ener : e ∈ interior energies) (pitch : 1 / h ∈ interior pitches) :
    0 < volume (trappedReference B m {p | if negative then p.2.1 < 0 else 0 < p.2.1}
      energies pitches) :=
  (signed_positive_mass volume m e h hm he hh negative energies pitches ener pitch).trans_le
    (measure_mono interior_subset)

end PlasmaLean.Design.DommaschkThermalReference325
'''


if __name__ == '__main__':
    verify_passage(NAME, SOURCE, ['from_birth', 'signed_positive_mass', 'signed_positive_volume'],
                   'DommaschkTrappedBirthCoordinates', 'TrappedCoordinateCache', 'trapped-birth-coordinates', __doc__)
