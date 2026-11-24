/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Finite flight time between two transverse physical mirrors -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionEnvelope
open Set MeasureTheory
open scoped Interval

/-- Arclength weight times reciprocal parallel speed, integrated from the left mirror
to the right mirror. `finite_bounce_time` supplies the integrability of this integral. -/
def oneWayBounceTime (weight f : ℝ → ℝ) (height left right : ℝ) : ℝ :=
  ∫ t in left..right, weight t / Real.sqrt (2 * (height - f t))

/-- At a simple left root, factor the gap into distance from the root and a strictly
positive continuous divided difference. The only singular factor is distance to
the power −½, which is integrable. -/
private theorem half_time {g weight : ℝ → ℝ} {l c v : ℝ} (lc : l < c)
    (hc : ContinuousOn g (Icc l c)) (hw : ContinuousOn weight (Icc l c))
    (root : g l = 0) (inside : ∀ t ∈ Ioc l c, 0 < g t)
    (d : HasDerivAt g v l) (pos : 0 < v) :
    IntervalIntegrable (fun t => weight t / Real.sqrt (g t)) volume l c := by
  have factor (t : ℝ) : (t - l) * dslope g l t = g t := by
    simpa only [smul_eq_mul, root, sub_zero] using sub_smul_dslope g l t
  have divisor : ∀ t ∈ Icc l c, 0 < dslope g l t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, dslope_same, d.deriv]
      exact pos
    · exact pos_of_mul_pos_right ((factor t).symm ▸ inside t ⟨h, ht.2⟩) (sub_nonneg.mpr h.le)
  have continuous : ContinuousOn (dslope g l) (Icc l c) := by
    intro t ht
    rcases eq_or_ne t l with rfl | ne
    · exact (continuousAt_dslope_same.mpr d.differentiableAt).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne ne).mpr (hc t ht)
  have coeff : ContinuousOn (fun t => weight t / Real.sqrt (dslope g l t)) [[l, c]] := by
    rw [uIcc_of_le lc.le]
    exact hw.div (Real.continuous_sqrt.comp_continuousOn continuous)
      (fun t ht => (Real.sqrt_pos.mpr (divisor t ht)).ne')
  have power : IntervalIntegrable (fun t : ℝ => (t-l) ^ (-(1/2 : ℝ))) volume l c := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c - l)
        (r := -(1/2 : ℝ)) (by norm_num)).comp_sub_right l
  apply (power.continuousOn_mul coeff).congr_uIoo
  intro t ht
  rw [uIoo_of_le lc.le] at ht
  have htl := sub_nonneg.mpr ht.1.le
  change weight t / Real.sqrt (dslope g l t) * (t-l) ^ (-(1/2:ℝ)) = weight t / Real.sqrt (g t)
  rw [Real.rpow_neg htl, ← Real.sqrt_eq_rpow, ← factor t, Real.sqrt_mul htl]
  ring

/-- The elapsed one-way time is a genuine integrable, strictly positive integral
when the field strength crosses the mirror height transversely at both ends.
The arclength density need only be positive in the interior. -/
theorem LaunchWell.finite_bounce_time {f weight : ℝ → ℝ} {c h l r vl vr : ℝ}
    (well : LaunchWell f c h l r)
    (profile : ContinuousOn f (Icc l r)) (density : ContinuousOn weight (Icc l r))
    (positive : ∀ t ∈ Ioo l r, 0 < weight t)
    (dl : HasDerivAt f vl l) (left_slope : vl < 0)
    (dr : HasDerivAt f vr r) (right_slope : 0 < vr) :
    IntervalIntegrable (fun t => weight t / Real.sqrt (2 * (h - f t))) volume l r ∧
      0 < oneWayBounceTime weight f h l r := by
  let g := fun t => 2 * (h - f t)
  have cg : ContinuousOn g (Icc l r) := continuousOn_const.mul (continuousOn_const.sub profile)
  have dg {t v : ℝ} (d : HasDerivAt f v t) : HasDerivAt g (-2*v) t := by
    convert ((d.const_sub h).const_mul 2) using 1; ring
  have left := half_time well.left_lt (cg.mono (Icc_subset_Icc_right well.lt_right.le))
    (density.mono (Icc_subset_Icc_right well.lt_right.le))
    (by simp [g, well.left_hit])
    (fun t ht => mul_pos (by norm_num) (sub_pos.mpr (well.accessible t
      ⟨ht.1, lt_of_le_of_lt ht.2 well.lt_right⟩))) (dg dl) (by linarith)
  have mirror : MapsTo (fun t : ℝ => -t) (Icc (-r) (-c)) (Icc l r) := by
    intro t ht
    exact ⟨by linarith [well.left_lt, ht.2], by linarith [ht.1]⟩
  have rev : HasDerivAt (fun t => g (-t)) (2*vr) (-r) := by
    have at_root : HasDerivAt g (-2*vr) (- -r) := by simpa only [neg_neg] using dg dr
    apply (at_root.scomp (-r) (hasDerivAt_neg (-r))).congr_deriv
    change (-1 : ℝ) * (-2*vr) = 2*vr
    ring
  have backward := half_time (g := fun t => g (-t)) (weight := fun t => weight (-t))
    (neg_lt_neg well.lt_right) (cg.comp continuous_neg.continuousOn mirror)
    (density.comp continuous_neg.continuousOn mirror) (by simp [g, well.right_hit])
    (fun t ht => mul_pos (by norm_num) (sub_pos.mpr (well.accessible (-t)
      ⟨by linarith [well.left_lt, ht.2], by linarith [ht.1]⟩))) rev (by linarith)
  have right : IntervalIntegrable (fun t => weight t / Real.sqrt (g t)) volume c r := by
    simpa only [zero_sub, neg_neg] using backward.symm.comp_sub_left 0
  have finite := left.trans right
  refine ⟨finite, intervalIntegral.intervalIntegral_pos_of_pos_on finite ?_
    (well.left_lt.trans well.lt_right)⟩
  intro t ht
  exact div_pos (positive t ht) (Real.sqrt_pos.mpr
    (mul_pos (by norm_num) (sub_pos.mpr (well.accessible t ht))))

end PlasmaLean.Kinetic.MirrorActionEnvelope
