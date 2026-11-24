/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorTimeActionBounds
public import PlasmaLean.Design.DommaschkMirrorBandPassage

/-! # A uniform lower bound on one-way flight time across the pilot height band -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorFlightBounds

open Set MeasureTheory Certificates.PositionFrameSlabs DommaschkFirstMirrorLaunchSign
open DommaschkMirrorTubeCrossing DommaschkSignedTraceDomain DommaschkPhysicalActionPanel
open DommaschkFirstMirrorBounceTime Kinetic.MirrorActionEnvelope DommaschkMirrorBandPassage
open DommaschkBounceField DommaschkKam Kinetic.MirrorHeightBand

set_option maxRecDepth 8192 in
/-- On the accessible portion of the pilot region, the lower toroidal field and
upper mirror height bound the arclength density uniformly. -/
theorem density_upper {t : ℝ} {x : Plane} (inside : Region x)
    (accessible : strength t x ≤ height true) : arcDensity (x 0) t (x 1) ≤ 68 := by
  have hr : 0 < x 0 := by linarith [inside.1.1]
  have den := DommaschkSignedTraceDenominator.regular t inside.1 inside.2
  have hp := toroidal_pos_of_den hr (lt_trans (by norm_num : (0 : ℝ) < 1 / 64) den)
  rw [(field_id hr t (x 1)).1] at den
  have one := pow_le_one₀ hr.le inside.1.2 (n := 7)
  have bphi := mul_le_of_le_one_left hp.le one
  change x 0 * strength t x / cylBphi (x 0) t (x 1) ≤ 68
  apply (div_le_iff₀ hp).mpr
  have mag : 0 ≤ strength t x := norm_nonneg _
  have cap := mul_le_of_le_one_left mag inside.1.2
  norm_num [height] at accessible
  linarith

private theorem upper_half {f w : ℝ → ℝ}
    (branch : Branch f (316 / 64) (325 / 64) (height false) (height true) (1 / 400))
    (h : Icc (height false : ℝ) (height true)) (mid : (height false + height true : ℝ) / 2 ≤ h)
    (weights : ∀ t ∈ Ioo 0 (branch.time h), 0 ≤ w t ∧ w t ≤ 68)
    (finite : IntervalIntegrable (fun t => w t / Real.sqrt (2 * ((h : ℝ) - f t)))
      volume 0 (branch.time h)) :
    oneWayBounceTime w f h 0 (branch.time h) < 17000 := by
  have ordered : (height false : ℝ) ≤ height true := by norm_num [height]
  let lo : Icc (height false : ℝ) (height true) := ⟨_, le_rfl, ordered⟩
  let s := branch.time lo
  let r := branch.time h
  have slow := branch.interior_time lo
  have fast := branch.interior_time h
  have sr : s ≤ r := branch.ordered.monotone h.2.1
  have start : 0 ≤ s := by dsimp [s]; linarith [slow.1]
  have central (t : ℝ) (ht : t ∈ Ioo 0 s) :
      w t / Real.sqrt (2 * ((h : ℝ) - f t)) ≤ 68 * 45 := by
    have small := branch.before lo t ⟨ht.1.le, ht.2⟩
    change f t < (height false : ℝ) at small
    have gap : (1 / 45 : ℝ) ^ 2 ≤ 2 * ((h : ℝ) - f t) := by
      norm_num [height] at mid small
      linarith
    have root : (1 / 45 : ℝ) ≤ Real.sqrt (2 * ((h : ℝ) - f t)) := by
      simpa using Real.sqrt_le_sqrt gap
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 45) root)).mpr
    linarith [(weights t ⟨ht.1, ht.2.trans_le sr⟩).2]
  have collar (t : ℝ) (ht : t ∈ Ioo s r) :
      w t / Real.sqrt (2 * ((h : ℝ) - f t)) ≤ (68 * 21) / Real.sqrt (r - t) := by
    have cap : (h : ℝ) ≤ 1 / 400 * 21 ^ 2 := h.2.2.trans (by norm_num [height])
    have inv := branch_collar_time_bound branch ordered (by norm_num) (by norm_num [height])
      (D := 21) (by norm_num) cap ht (by norm_num)
    have wcap := weights t ⟨start.trans_lt ht.1, ht.2⟩
    calc
      _ ≤ 68 / Real.sqrt (2 * ((h : ℝ) - f t)) :=
        div_le_div_of_nonneg_right wcap.2 (Real.sqrt_nonneg _)
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left inv (by norm_num : (0 : ℝ) ≤ 68) using 1 <;> ring
  have estimate := half_time_upper start sr finite central collar
  have width : r - s ≤ (3 / 8 : ℝ) ^ 2 := by dsimp [s, r]; linarith [slow.1, fast.2]
  have root : Real.sqrt (r - s) ≤ 3 / 8 := Real.sqrt_le_iff.mpr ⟨by norm_num, width⟩
  change (∫ t in 0..r, w t / Real.sqrt (2 * ((h : ℝ) - f t))) < 17000
  have sc : s < 325 / 64 := slow.2
  linarith

/-- One-way time exceeds 237/40 throughout the band and is below 34000 in
the upper half. Both bounds use the dimensionless parallel speed of the archive. -/
def TimeBound (φ : ℝ) (y : ℝ → Plane) : Prop :=
  ∀ h ∈ Icc (height false : ℝ) (height true),
    ∃ l ∈ Ioo (-(325 / 64)) (-(316 / 64)), ∃ r ∈ Ioo (316 / 64) (325 / 64),
      φ ∈ Ioo l r ∧ LaunchWell (fun t => strength t (y t)) 0 h l r ∧
      let w := fun t => arcDensity (y t 0) t (y t 1)
      let f := fun t => strength t (y t)
      IntervalIntegrable (fun t => w t / Real.sqrt (2 * (h - f t))) volume l r ∧
      237 / 40 < oneWayBounceTime w f h l r ∧
        ((height false + height true : ℝ) / 2 ≤ h → oneWayBounceTime w f h l r < 34000)

theorem of_passage {φ : ℝ} {y : ℝ → Plane} (passage : Passage φ y)
    (region : ∀ t ∈ Icc (-(325 / 64)) (325 / 64), Region (y t)) : TimeBound φ y := by
  intro h hh
  obtain ⟨l, hl, r, hr, atBirth, well, finite, _⟩ := (passage.2.2 h hh).2.2
  refine ⟨l, hl, r, hr, atBirth, well, finite, ?_, ?_⟩
  · have speed (t : ℝ) (_ : t ∈ Ioo l r) :
        Real.sqrt (2 * (h - strength t (y t))) ≤ 35 / 24 := by
      apply Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
      have nonneg : 0 ≤ strength t (y t) := norm_nonneg _
      have top := hh.2
      norm_num [height] at top
      linarith
    have lower := well.time_lower (m := 7 / 8) (by norm_num) (fun t ht =>
      DommaschkSignedTraceDensity.density_lower t (region t
        ⟨le_of_lt (hl.1.trans ht.1), le_of_lt (ht.2.trans hr.2)⟩)) speed finite
    norm_num at lower
    linarith [hl.2, hr.1]
  · intro mid
    let H : Icc (height false : ℝ) (height true) := ⟨h, hh⟩
    obtain ⟨⟨p⟩, ⟨m⟩⟩ := passage.1
    have ep : r = p.time H := p.unique_time H r (Ioo_subset_Icc_self hr) well.right_hit
    have eh : strength (- -l) (y (- -l)) = H := by simpa [H] using well.left_hit
    have em : -l = m.time H := m.unique_time H (-l)
      ⟨by linarith [hl.2], by linarith [hl.1]⟩ eh
    let w (t : ℝ) := arcDensity (y t 0) t (y t 1)
    let g (t : ℝ) := w t / Real.sqrt (2 * (h - strength t (y t)))
    change IntervalIntegrable g volume l r at finite
    have l0 := well.left_lt.le
    have r0 := well.lt_right.le
    have left := finite.mono_set (by rw [uIcc_of_le l0, uIcc_of_le (l0.trans r0)]
                                     exact Icc_subset_Icc_right r0)
    have right := finite.mono_set (by rw [uIcc_of_le r0, uIcc_of_le (l0.trans r0)]
                                      exact Icc_subset_Icc_left l0)
    have weights (t : ℝ) (ht : t ∈ Ioo l r) : 0 ≤ w t ∧ w t ≤ 68 := by
      have reg := region t ⟨(hl.1.trans ht.1).le, (ht.2.trans hr.2).le⟩
      exact ⟨(by norm_num : (0 : ℝ) ≤ 7 / 8).trans
        (DommaschkSignedTraceDensity.density_lower t reg),
        density_upper reg ((well.accessible t ht).le.trans hh.2)⟩
    have R := upper_half (w := w) p H mid (fun t ht => by
      rw [← ep] at ht
      exact weights t ⟨l0.trans_lt ht.1, ht.2⟩) (ep ▸ right)
    have fi : IntervalIntegrable (fun t => g (-t)) volume 0 (-l) := by
      simpa only [zero_sub, sub_zero] using (left.symm.comp_sub_left 0)
    have L := upper_half (w := fun t => w (-t)) m H mid (fun t ht => by
      rw [← em] at ht
      exact weights (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩) (em ▸ fi)
    change (∫ t in 0..m.time H, g (-t)) < 17000 at L
    change (∫ t in 0..p.time H, g t) < 17000 at R
    rw [← em, intervalIntegral.integral_comp_neg] at L
    rw [← ep] at R
    change (∫ t in l..r, g t) < 34000
    rw [← intervalIntegral.integral_add_adjacent_intervals left right]
    simp only [neg_neg, neg_zero] at L
    linarith

end PlasmaLean.Design.DommaschkMirrorFlightBounds
