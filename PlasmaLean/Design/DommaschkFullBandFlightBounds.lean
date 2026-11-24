/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCoreClearance
public import PlasmaLean.Design.DommaschkSharpFlightBounds

/-! # A numerical one-way flight-time interval for all pilot heights -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFullBandFlightBounds

open Set MeasureTheory Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing
open DommaschkSignedTraceDomain DommaschkPhysicalActionPanel DommaschkMirrorBandPassage
open DommaschkSignedObservable DommaschkSignedMirrorBand DommaschkSignedMirrorSlope
open Kinetic.MirrorActionEnvelope Kinetic.MirrorProfileStability DommaschkFirstMirrorLaunchSign
open DommaschkSharpFlightBounds

abbrev a : ℝ := 316 / 64
abbrev b : ℝ := 325 / 64

abbrev speedWeight (f w : ℝ → ℝ) (h t : ℝ) := w t / Real.sqrt (2 * (h - f t))

private theorem wing {f w : ℝ → ℝ} {h r : ℝ} (range : r ∈ Ioo a b)
    (cap : h ≤ height true) (hit : f r = h) (under : ∀ t ∈ Ioo a r, f t < h)
    (pos : ∀ t, 0 ≤ f t) (weights : ∀ t ∈ Ioo a r, w t ≤ ceiling)
    (continuous : ContinuousOn f (Icc a b)) (growth : ∀ t ∈ Ioo a b, Rate f (1 / 400) t)
    (finite : IntervalIntegrable (speedWeight f w h) volume a r) :
    (∫ t in a..r, speedWeight f w h t) < 20 := by
  have sep : SlopeSeparatedOn (fun t => (f t) ^ 2) (Icc a b) (1 / 400) := by
    apply separated_of_derivative (convex_Icc _ _) ((continuous_pow 2).comp_continuousOn continuous)
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨v, _, d⟩ := growth t ht
      exact d.differentiableAt.differentiableWithinAt
    · left
      intro t ht
      rw [interior_Icc] at ht
      obtain ⟨v, hv, d⟩ := growth t ht
      exact d.deriv.symm ▸ hv.le
  have collar (t) (ht : t ∈ Ioo a r) :
      speedWeight f w h t ≤ (ceiling * 21) / Real.sqrt (r - t) := by
    have field := under t ht
    have dt := sub_pos.mpr ht.2
    have gap := sep r (Ioo_subset_Icc_self range) t ⟨ht.1.le, ht.2.le.trans range.2.le⟩
    dsimp only at gap
    rw [hit, abs_of_pos dt, abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (pos t) field.le 2))]
      at gap
    have factor : h ≤ (1 / 400 : ℝ) * 21 ^ 2 := cap.trans (by norm_num [height])
    have delta : r - t ≤ (21 : ℝ) ^ 2 * (2 * (h - f t)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr factor) (sub_nonneg.mpr field.le), sq_nonneg (h - f t)]
    have sr := Real.sqrt_le_sqrt delta
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (21 : ℝ) ^ 2), Real.sqrt_sq (by norm_num)] at sr
    have root := Real.sqrt_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr field))
    apply (div_le_div_iff₀ root (Real.sqrt_pos.mpr dt)).mpr
    calc
      w t * Real.sqrt (r - t) ≤ ceiling * Real.sqrt (r - t) :=
        mul_le_mul_of_nonneg_right (weights t ht) (Real.sqrt_nonneg _)
      _ ≤ ceiling * 21 * Real.sqrt (2 * (h - f t)) := by
        rw [mul_assoc ceiling 21 _]
        exact mul_le_mul_of_nonneg_left sr (by norm_num [ceiling, height] : 0 ≤ ceiling)
  have bound := half_time_upper (a := a) (s := a) le_rfl range.1.le finite
    (C := 0) (fun _ ⟨s, t⟩ => ((lt_asymm s t).elim)) collar
  have width : r - a ≤ (3 / 8 : ℝ) ^ 2 := by
    have hr := range.2
    norm_num [a, b] at hr ⊢
    linarith
  have sr : Real.sqrt (r - a) ≤ 3 / 8 := Real.sqrt_le_iff.mpr ⟨by norm_num, width⟩
  norm_num [a, b, ceiling, height] at bound sr ⊢
  linarith only [bound, sr]

/-- Bounds on the two outer collars are stated separately from the signed core
integral so a finer core quadrature can strengthen the global time bound. -/
def BoundedFlight (φ : ℝ) (y : ℝ → Plane) : Prop :=
  ∀ h ∈ Icc (height false : ℝ) (height true),
    ∃ l ∈ Ioo (-b) (-a), ∃ r ∈ Ioo a b, φ ∈ Ioo l r ∧
      let f := fun t => strength t (y t)
      let w := fun t => arcDensity (y t 0) t (y t 1)
      LaunchWell f 0 h l r ∧ IntervalIntegrable (speedWeight f w h) volume l r ∧
      oneWayBounceTime w f h l r < (∫ t in (-a)..a, speedWeight f w h t) + 40 ∧
      14 < oneWayBounceTime w f h l r ∧ oneWayBounceTime w f h l r < 4450

/-- A common physical-path core clearance suffices to enclose every one-way
flight, including the flight at the smallest archived height. -/
theorem on_path {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane} {φ : ℝ}
    (path : Path 325 fs bs fr br x y) (passage : Passage φ y)
    (region : ∀ t ∈ Icc (-b) b, Region (y t)) (rates : Rates y a b (1 / 400))
    (core : ∀ t ∈ Icc (-a) a, strength t (y t) < DommaschkCoreClearance.height) :
    BoundedFlight φ y := by
  have clocks := clock_odes path (a := a) (b := b) (by norm_num [a]) (by norm_num [b])
  let f (t : ℝ) := strength t (y t)
  let w (t : ℝ) := arcDensity (y t 0) t (y t 1)
  have reg (t : ℝ) (ht : t ∈ Icc a b) : Region (y t) ∧ Region (y (-t)) := by
    obtain ⟨lo, hi⟩ := ht
    constructor <;> apply region <;> constructor <;> linarith [show 0 ≤ a by norm_num [a]]
  have fc : ContinuousOn f (Icc a b) := by
    have cy : ContinuousOn y (Icc a b) := fun t ht => (clocks.1 t ht).continuousWithinAt
    simpa only [one_mul, f] using continuousOn_strength cy 1
      (fun t ht => by linarith [((reg t ht).1).1.1])
  have bc : ContinuousOn (fun t => f (-t)) (Icc a b) := by
    have cy : ContinuousOn (fun t => y (-t)) (Icc a b) :=
      fun t ht => (clocks.2 t ht).continuousWithinAt
    simpa only [neg_one_mul, f] using continuousOn_strength cy (-1)
      (fun t ht => by linarith [((reg t ht).2).1.1])
  have growth (t : ℝ) (ht : t ∈ Ioo a b) :=
    rates t (Ioo_subset_Icc_self ht)
      ((clocks.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      ((clocks.2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  intro h hh
  obtain ⟨l, hl, r, hr, birth, well, finite, lower, _⟩ :=
    DommaschkSharpFlightBounds.of_passage passage region h hh
  change l ∈ Ioo (-b) (-a) at hl
  change r ∈ Ioo a b at hr
  let g := speedWeight f w h
  change IntervalIntegrable g volume l r at finite
  have center : -a ≤ a := by norm_num [a]
  have sideL : l ≤ -a := hl.2.le
  have sideR : a ≤ r := hr.1.le
  have order := sideL.trans (center.trans sideR)
  have part {p q : ℝ} (lp : l ≤ p) (pq : p ≤ q) (qr : q ≤ r) :
      IntervalIntegrable g volume p q :=
    finite.mono_set (by rw [uIcc_of_le pq, uIcc_of_le order]; exact Icc_subset_Icc lp qr)
  have left := part le_rfl sideL (center.trans sideR)
  have middle := part sideL center sideR
  have right := part (sideL.trans center) sideR le_rfl
  have wcap (t : ℝ) (ht : t ∈ Ioo l r) : w t ≤ ceiling :=
    DommaschkToroidalFieldBounds.density_upper
      (region t ⟨(hl.1.trans ht.1).le, (ht.2.trans hr.2).le⟩) ((well.accessible t ht).le.trans hh.2)
  have tailR := wing (f := f) (w := w) (h := h) hr hh.2 well.right_hit
    (fun t ht => well.accessible t ⟨(sideL.trans center).trans_lt ht.1, ht.2⟩)
    (fun _ => norm_nonneg _) (fun t ht => wcap t ⟨(sideL.trans center).trans_lt ht.1, ht.2⟩)
    fc (fun t ht => (growth t ht).1) right
  have reflect : IntervalIntegrable (fun t => g (-t)) volume a (-l) := by
    simpa only [zero_sub, neg_neg] using left.symm.comp_sub_left 0
  have mrange : -l ∈ Ioo a b := ⟨by linarith [hl.2], by linarith [hl.1]⟩
  have hit : f (- -l) = h := by simpa only [neg_neg] using well.left_hit
  have inward (t : ℝ) (ht : t ∈ Ioo a (-l)) : -t ∈ Ioo l r :=
    ⟨by linarith [ht.2], by linarith [ht.1, hr.1, show 0 ≤ a by norm_num [a]]⟩
  have tailL := wing (f := fun t => f (-t)) (w := fun t => w (-t)) mrange hh.2 hit
    (fun t ht => well.accessible (-t) (inward t ht)) (fun _ => norm_nonneg _)
    (fun t ht => wcap (-t) (inward t ht)) bc (fun t ht => (growth t ht).2) reflect
  change (∫ t in a..(-l), g (-t)) < 20 at tailL
  rw [intervalIntegral.integral_comp_neg, neg_neg] at tailL
  change (∫ t in a..r, g t) < 20 at tailR
  have short : (∫ t in l..r, g t) < (∫ t in (-a)..a, g t) + 40 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (left.trans middle) right,
      ← intervalIntegral.integral_add_adjacent_intervals left middle]
    linarith only [tailL, tailR]
  refine ⟨l, hl, r, hr, birth, well, finite, short, lower, ?_⟩
  have perTime (t : ℝ) (ht : t ∈ Ioo (-a) a) : g t ≤ ceiling * 368 := by
    have small := core t (Ioo_subset_Icc_self ht)
    have bot := hh.1
    have gap : (1 / 368 : ℝ) ^ 2 ≤ 2 * (h - f t) := by
      change f t < (DommaschkCoreClearance.height : ℝ) at small
      norm_num [DommaschkCoreClearance.height, height] at small bot
      linarith
    have speed : (1 / 368 : ℝ) ≤ Real.sqrt (2 * (h - f t)) := by
      simpa using Real.sqrt_le_sqrt gap
    apply (div_le_iff₀ ((by norm_num : (0 : ℝ) < 1 / 368).trans_le speed)).mpr
    have dens := wcap t ⟨sideL.trans_lt ht.1, ht.2.trans_le sideR⟩
    apply dens.trans
    calc
      ceiling = (ceiling * 368) * (1 / 368) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left speed (by norm_num [ceiling, height])
  have total := intervalIntegral.integral_mono_on_of_le_Ioo center middle
    intervalIntegrable_const perTime
  simp only [intervalIntegral.integral_const, smul_eq_mul] at total
  have size : (a - -a) * (ceiling * 368) + 40 < 4450 := by norm_num [a, ceiling, height]
  change (∫ t in l..r, g t) < 4450
  linarith only [short, total, size]

end PlasmaLean.Design.DommaschkFullBandFlightBounds
