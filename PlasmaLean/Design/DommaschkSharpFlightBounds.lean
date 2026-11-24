/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkToroidalFieldBounds
public import PlasmaLean.Design.DommaschkMirrorBandPassage
public import PlasmaLean.Theory.Kinetic.MirrorBranchTimeUpper

/-! # Uniform pilot one-way flight bounds from the full-envelope toroidal field floor -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSharpFlightBounds

open Set MeasureTheory Certificates.PositionFrameSlabs DommaschkFirstMirrorLaunchSign
open DommaschkMirrorTubeCrossing DommaschkSignedTraceDomain DommaschkPhysicalActionPanel
open DommaschkFirstMirrorBounceTime Kinetic.MirrorActionEnvelope DommaschkMirrorBandPassage
open Kinetic.MirrorHeightBand

abbrev ceiling : ℝ := (height true : ℝ) * (8 / 7)

/-- With a reciprocal speed ceiling of 45 on the core, a uniform height-band estimate
on the collar bounds the normalized one-way time along one outward branch. -/
theorem half_upper {f w : ℝ → ℝ}
    (branch : Branch f (316 / 64) (325 / 64) (height false) (height true) (1 / 400))
    (h : Icc (height false : ℝ) (height true))
    (weights : ∀ t ∈ Ioo 0 (branch.time h), w t ≤ ceiling)
    (core : ∀ t ∈ Ioo 0 (branch.time ⟨height false, le_rfl, by norm_num [height]⟩),
      (1 / 45 : ℝ) ^ 2 ≤ 2 * ((h : ℝ) - f t))
    (finite : IntervalIntegrable (fun t => w t / Real.sqrt (2 * ((h : ℝ) - f t)))
      volume 0 (branch.time h)) :
    oneWayBounceTime w f h 0 (branch.time h) < 296 := by
  have ord : (height false : ℝ) ≤ height true := by norm_num [height]
  let s := branch.time ⟨height false, le_rfl, ord⟩
  let r := branch.time h
  have slow : s ∈ Ioo (316 / 64) (325 / 64) := branch.interior_time _
  have high : r ∈ Ioo (316 / 64) (325 / 64) := branch.interior_time _
  have estimate := branch_time_upper (D := 21) (A := 45) (W := ceiling)
    branch ord h (by norm_num) (by norm_num) (by norm_num [height]) (by norm_num)
    (by norm_num [ceiling, height]) (by norm_num)
    (h.2.2.trans (by norm_num [height])) weights core finite
  have gap : r - s ≤ (3 / 8 : ℝ) ^ 2 := by linarith [slow.1, high.2]
  have root : Real.sqrt (r - s) ≤ 3 / 8 := Real.sqrt_le_iff.mpr ⟨by norm_num, gap⟩
  change oneWayBounceTime w f h 0 _ ≤ s * _ + _ * Real.sqrt (r - s) at estimate
  norm_num [ceiling, height] at estimate
  linarith only [estimate, slow.2, root]

/-- The two turning points are those of the genuine first well containing the original birth. -/
def SharpTime (φ : ℝ) (y : ℝ → Plane) : Prop :=
  ∀ h ∈ Icc (height false : ℝ) (height true),
    ∃ l ∈ Ioo (-(325 / 64)) (-(316 / 64)), ∃ r ∈ Ioo (316 / 64) (325 / 64),
      φ ∈ Ioo l r ∧ LaunchWell (fun t => strength t (y t)) 0 h l r ∧
      let w := fun t => arcDensity (y t 0) t (y t 1)
      let f := fun t => strength t (y t)
      IntervalIntegrable (fun t => w t / Real.sqrt (2 * (h - f t))) volume l r ∧
      14 < oneWayBounceTime w f h l r ∧
      ((height false + height true : ℝ) / 2 ≤ h → oneWayBounceTime w f h l r < 592)

theorem of_passage {φ : ℝ} {y : ℝ → Plane} (passage : Passage φ y)
    (region : ∀ t ∈ Icc (-(325 / 64)) (325 / 64), Region (y t)) : SharpTime φ y := by
  intro h hh
  obtain ⟨l, hl, r, hr, atBirth, well, finite, _⟩ := (passage.2.2 h hh).2.2
  have reg (t : ℝ) (ht : t ∈ Ioo l r) := region t ⟨(hl.1.trans ht.1).le, (ht.2.trans hr.2).le⟩
  refine ⟨l, hl, r, hr, atBirth, well, finite, ?_, ?_⟩
  · have lower := well.time_lower (m := 7 / 8) (by norm_num)
      (fun t ht => DommaschkSignedTraceDensity.density_lower t (reg t ht))
      (fun t ht => (DommaschkToroidalFieldBounds.speed_upper (reg t ht) hh.2).le) finite
    norm_num at lower
    linarith [hl.2, hr.1]
  · intro mid
    let H : Icc (height false : ℝ) (height true) := ⟨h, hh⟩
    obtain ⟨⟨p⟩, ⟨m⟩⟩ := passage.1
    have ep := p.unique_time H r (Ioo_subset_Icc_self hr) well.right_hit
    have back : strength (- -l) (y (- -l)) = H := by simpa only [neg_neg] using well.left_hit
    have em := m.unique_time H (-l) ⟨by linarith [hl.2], by linarith [hl.1]⟩ back
    let w (t : ℝ) := arcDensity (y t 0) t (y t 1)
    let g (t : ℝ) := w t / Real.sqrt (2 * (h - strength t (y t)))
    change IntervalIntegrable g volume l r at finite
    have l0 := well.left_lt.le
    have r0 := well.lt_right.le
    have left := finite.mono_set (by rw [uIcc_of_le l0, uIcc_of_le (l0.trans r0)]
                                     exact Icc_subset_Icc_right r0)
    have right := finite.mono_set (by rw [uIcc_of_le r0, uIcc_of_le (l0.trans r0)]
                                      exact Icc_subset_Icc_left l0)
    have weights (t : ℝ) (ht : t ∈ Ioo l r) : w t ≤ ceiling :=
      DommaschkToroidalFieldBounds.density_upper (reg t ht) ((well.accessible t ht).le.trans hh.2)
    have core {f : ℝ → ℝ}
        (branch : Branch f (316 / 64) (325 / 64) (height false) (height true) (1 / 400))
        (t : ℝ) (ht : t ∈ Ioo 0 (branch.time ⟨height false, le_rfl, by norm_num [height]⟩)) :
        (1 / 45 : ℝ) ^ 2 ≤ 2 * ((H : ℝ) - f t) := by
      have small := branch.before ⟨height false, le_rfl, by norm_num [height]⟩ t ⟨ht.1.le, ht.2⟩
      change f t < (height false : ℝ) at small
      change _ ≤ 2 * (h - f t)
      norm_num [height] at mid small
      linarith
    have R := half_upper (w := w) p H (fun t ht => by
      rw [← ep] at ht
      exact weights t ⟨l0.trans_lt ht.1, ht.2⟩) (core p) (ep ▸ right)
    have fi : IntervalIntegrable (fun t => g (-t)) volume 0 (-l) := by
      simpa only [zero_sub, sub_zero] using (left.symm.comp_sub_left 0)
    have L := half_upper (w := fun t => w (-t)) m H (fun t ht => by
      rw [← em] at ht
      exact weights (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩) (core m) (em ▸ fi)
    change (∫ t in 0..m.time H, g (-t)) < 296 at L
    change (∫ t in 0..p.time H, g t) < 296 at R
    rw [← em, intervalIntegral.integral_comp_neg] at L
    rw [← ep] at R
    change (∫ t in l..r, g t) < 592
    rw [← intervalIntegral.integral_add_adjacent_intervals left right]
    simp only [neg_neg, neg_zero] at L
    linarith

end PlasmaLean.Design.DommaschkSharpFlightBounds
