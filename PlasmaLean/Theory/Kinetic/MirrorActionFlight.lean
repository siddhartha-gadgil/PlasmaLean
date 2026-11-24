/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorBounceTime
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Height increments of the clipped action and physical one-way flight time -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionFlight

open MeasureTheory Set Real MirrorHeightAction MirrorActionEnvelope

private def reciprocalSpeed (h : ℝ) : ℝ := 1 / √(2 * h)

private theorem reciprocal_eq {h : ℝ} (hh : 0 ≤ h) :
    reciprocalSpeed h = (1 / √2) * h ^ (-(1 / 2 : ℝ)) := by
  rw [reciprocalSpeed, Real.rpow_neg hh, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  ring

/-- A vanishing or negative energy gap contributes zero to both sides.  The integrable
singularity to its right is the inverse square root. -/
private theorem primitive_zero (b : ℝ) :
    IntervalIntegrable reciprocalSpeed volume 0 b ∧
    (∫ h in (0 : ℝ)..b, reciprocalSpeed h) = √(2 * b) := by
  rcases le_total 0 b with hb | hb
  · have reg := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
      (r := -(1 / 2 : ℝ)) (by norm_num)).const_mul (1 / √2)
    have eq : EqOn (fun h : ℝ => (1 / √2) * h ^ (-(1 / 2 : ℝ))) reciprocalSpeed (uIcc 0 b) := by
      rw [uIcc_of_le hb]
      exact fun h ht => (reciprocal_eq ht.1).symm
    refine ⟨reg.congr (fun t ht => eq (uIoc_subset_uIcc ht)), ?_⟩
    rw [← intervalIntegral.integral_congr eq, intervalIntegral.integral_const_mul]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_zero, sub_zero, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · have eq : EqOn (fun _ : ℝ => (0 : ℝ)) reciprocalSpeed (uIcc 0 b) := by
      rw [uIcc_of_ge hb]
      intro t ht
      simp [reciprocalSpeed, Real.sqrt_eq_zero_of_nonpos (by linarith [ht.2] : 2 * t ≤ 0)]
    refine ⟨intervalIntegrable_const.congr (fun t ht => eq (uIoc_subset_uIcc ht)), ?_⟩
    rw [← intervalIntegral.integral_congr eq, Real.sqrt_eq_zero_of_nonpos (by linarith : 2 * b ≤ 0)]
    simp

private theorem from_level (x b : ℝ) :
    IntervalIntegrable (fun h => reciprocalSpeed (h - x)) volume x b ∧
    (∫ h in x..b, reciprocalSpeed (h - x)) = √(2 * (b - x)) := by
  have p := primitive_zero (b - x)
  refine ⟨?_, ?_⟩
  · simpa only [zero_add, sub_add_cancel] using p.1.comp_sub_right x
  · rw [intervalIntegral.integral_comp_sub_right, sub_self]
    exact p.2

/-- The exact energy integral for a single field value, also when that value is an atom
of the arclength distribution. -/
theorem scalar (x l h : ℝ) :
    IntervalIntegrable (fun u => 1 / √(2 * (u - x))) volume l h ∧
    (∫ u in l..h, 1 / √(2 * (u - x))) = √(2 * (h - x)) - √(2 * (l-x)) := by
  obtain ⟨il, pl⟩ := from_level x l
  obtain ⟨ih, ph⟩ := from_level x h
  have piece := il.symm.trans ih
  have sum := intervalIntegral.integral_add_adjacent_intervals il piece
  rw [pl, ph] at sum
  exact ⟨piece, eq_sub_of_add_eq' sum⟩

/-- Exact action increment on a fixed window. The hypotheses name the two
action integrals and the joint integrability used to exchange angle and height. -/
theorem difference {f w : ℝ → ℝ} {a b l h : ℝ}
    (low : IntervalIntegrable (fun t => w t * √(2 * (l - f t))) volume a b)
    (high : IntervalIntegrable (fun t => w t * √(2 * (h - f t))) volume a b)
    (joint : IntegrableOn (fun q : ℝ × ℝ => w q.2 / √(2 * (q.1 - f q.2)))
      (uIoc l h ×ˢ uIoc a b)) :
    action f w a b h - action f w a b l =
      ∫ u in l..h, oneWayBounceTime w f u a b := by
  change (∫ t in a..b, _) - (∫ t in a..b, _) = ∫ u in l..h, ∫ t in a..b, w t / √(2 * (u - f t))
  rw [← intervalIntegral.integral_sub high low,
    intervalIntegral_intervalIntegral_swap (F := fun u t => w t / √(2 * (u - f t))) joint]
  apply intervalIntegral.integral_congr
  intro t _
  change _ = ∫ u in l..h, w t / √(2 * (u - f t))
  simp_rw [div_eq_mul_one_div (w t)]
  rw [intervalIntegral.integral_const_mul, (scalar (f t) l h).2]
  ring

private theorem compact_product {f w : ℝ → ℝ} {a b l h : ℝ} (lh : l ≤ h)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b)) :
    Integrable (fun q : ℝ × ℝ => w q.2 / √(2 * (q.1 - f q.2)))
      ((volume.restrict (Ioc l h)).prod (volume.restrict (Ioc a b))) := by
  let μ := volume.restrict (Ioc l h)
  let ν := volume.restrict (Ioc a b)
  let K (q : ℝ × ℝ) := w q.2 / √(2 * (q.1 - f q.2))
  have mf : AEStronglyMeasurable f ν :=
    (cf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have mw : AEStronglyMeasurable w ν :=
    (cw.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have mk : AEStronglyMeasurable K (μ.prod ν) :=
    (mw.comp_snd.aemeasurable.div (Real.continuous_sqrt.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.mul (measurable_fst.aestronglyMeasurable.sub
        mf.comp_snd))).aemeasurable).aestronglyMeasurable
  apply (integrable_prod_iff' mk).2
  constructor
  · filter_upwards with t
    have it := ((scalar (f t) l h).1.const_mul (w t))
    simpa only [K, μ, IntegrableOn, div_eq_mul_one_div (w t)] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le lh).mp it
  · have eq (t : ℝ) : (∫ u, ‖K (u, t)‖ ∂μ) =
        |w t| * (√(2 * (h - f t)) - √(2 * (l - f t))) := by
      simp only [K, Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      simp_rw [div_eq_mul_one_div |w t|]
      rw [integral_const_mul, ← intervalIntegral.integral_of_le lh, (scalar (f t) l h).2]
    simp_rw [eq]
    apply ContinuousOn.integrableOn_Icc _ |>.mono_set Ioc_subset_Icc_self
    exact cw.abs.mul ((Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.mul (continuousOn_const.sub cf))).sub
      (Real.continuous_sqrt.comp_continuousOn
        (continuousOn_const.mul (continuousOn_const.sub cf))))

/-- Continuous field and arclength density on a compact positional window suffice for the
exact action increment and height integrability of the clipped flight time. -/
theorem compact_window {f w : ℝ → ℝ} {a b : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b)) (l h : ℝ) :
    IntervalIntegrable (fun u => oneWayBounceTime w f u a b) volume l h ∧
      action f w a b h - action f w a b l = ∫ u in l..h, oneWayBounceTime w f u a b := by
  have ordered (p q : ℝ) (pq : p ≤ q) :
      IntervalIntegrable (fun u => oneWayBounceTime w f u a b) volume p q ∧
        action f w a b q - action f w a b p = ∫ u in p..q, oneWayBounceTime w f u a b := by
    have prod := compact_product pq cf cw
    have level (u : ℝ) : IntervalIntegrable (fun t => w t * √(2 * (u - f t))) volume a b :=
      (cw.mul (Real.continuous_sqrt.comp_continuousOn
        (continuousOn_const.mul (continuousOn_const.sub cf)))).intervalIntegrable_of_Icc ab
    constructor
    · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le pq).2
      simpa only [IntegrableOn, oneWayBounceTime, intervalIntegral.integral_of_le ab] using
        prod.integral_prod_left
    · apply difference (level p) (level q)
      rwa [uIoc_of_le pq, uIoc_of_le ab, IntegrableOn, Measure.volume_eq_prod,
        ← Measure.prod_restrict]
  rcases le_total l h with lh | hl
  · exact ordered l h lh
  · obtain ⟨it, eq⟩ := ordered h l hl
    exact ⟨it.symm, by rw [intervalIntegral.integral_symm, ← eq]; ring⟩

/-- Local height integrability holds even at a flat bottom or an exceptional flight height. -/
theorem locallyIntegrable_time {f w : ℝ → ℝ} {a b : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b)) :
    LocallyIntegrable (fun u => oneWayBounceTime w f u a b) volume := by
  intro x
  refine ⟨Ioc (x - 1) (x + 1), Ioc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
    (compact_window ab cf cw (x - 1) (x + 1)).1

/-- On each finite energy band the clipped action is absolutely continuous. -/
theorem absolutelyContinuous_action {f w : ℝ → ℝ} {a b : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b)) (l h : ℝ) :
    AbsolutelyContinuousOnInterval (action f w a b) l h := by
  have ac := (compact_window ab cf cw l h).1.absolutelyContinuousOnInterval_intervalIntegral
    (c := l) (by simp)
  have const : AbsolutelyContinuousOnInterval (fun _ : ℝ => action f w a b l) l h :=
    contDiffOn_const.absolutelyContinuousOnInterval
  apply (const.add ac).congr
  intro k _
  change action f w a b l + _ = action f w a b k
  linarith [(compact_window ab cf cw l k).2]

private theorem anchored {f w : ℝ → ℝ} {a b : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b)) :
    action f w a b = fun h => action f w a b 0 + ∫ u in (0 : ℝ)..h, oneWayBounceTime w f u a b := by
  funext h
  linarith [(compact_window ab cf cw 0 h).2]

/-- For almost every height the derivative of the clipped action is the one-way flight
integral. This includes fields whose arclength distribution has atoms. -/
theorem ae_hasDerivAt_action {f w : ℝ → ℝ} {a b : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b)) :
    ∀ᵐ h, HasDerivAt (action f w a b) (oneWayBounceTime w f h a b) h := by
  have hf := _root_.LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_time ab cf cw)
  filter_upwards [hf] with h dh
  rw [anchored ab cf cw]
  exact (dh 0).const_add _

/-- At each continuity point of the flight time the action is differentiable with that
derivative. -/
theorem hasDerivAt_of_continuous_time {f w : ℝ → ℝ} {a b h : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b))
    (ht : ContinuousAt (fun u => oneWayBounceTime w f u a b) h) :
    HasDerivAt (action f w a b) (oneWayBounceTime w f h a b) h := by
  have mt := (locallyIntegrable_time ab cf cw).aestronglyMeasurable.stronglyMeasurableAtFilter
    (l := nhds h)
  have d := intervalIntegral.integral_hasDerivAt_right (compact_window ab cf cw 0 h).1 mt ht
  rw [anchored ab cf cw]
  exact d.const_add _

end PlasmaLean.Kinetic.MirrorActionFlight
