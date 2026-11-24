/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionHeightShift

/-! # An affine lower bound for the action gain from a uniform field drop -/

public section
noncomputable section
set_option linter.style.longLine false
namespace PlasmaLean.Kinetic.MirrorActionEnvelope
open Set Real MeasureTheory MirrorHeightAction

/-- A supporting affine function for the speed at a positive squared-speed increment. -/
theorem affine_le_speed {a b d v V : ℝ} (hd : 0 < d) (unit : b ^ 2 ≤ d * (1 - a ^ 2))
    (positive : 0 ≤ V) (energy : v ^ 2 + d ≤ V ^ 2) : a * v + b ≤ V := by
  have hs : (a * v + b) ^ 2 ≤ v ^ 2 + d := by
    apply le_of_mul_le_mul_left (a := d) _ hd
    nlinarith only [sq_nonneg (b * v - a * d),
      mul_nonneg (sub_nonneg.mpr unit) (add_nonneg (sq_nonneg v) hd.le)]
  exact le_of_sq_le_sq (hs.trans energy) positive

/-- On the same height, the wider well contains the reference well. The integrated
affine speed bound keeps a positive term proportional to its true arclength. -/
theorem LaunchWell.affine_gain {f g w v : ℝ → ℝ} {c h l r L R k a b d : ℝ}
    (inner : LaunchWell f c h l r) (outer : LaunchWell g c h L R)
    (hd : 0 < d) (hk : 0 ≤ k) (unit : b ^ 2 ≤ d * (1 - a ^ 2))
    (bf : ContinuousOn f (Icc l r)) (bw : ContinuousOn w (Icc l r))
    (gf : ContinuousOn g (Icc L R)) (gv : ContinuousOn v (Icc L R))
    (wn : ∀ t ∈ Icc l r, 0 ≤ w t) (vn : ∀ t ∈ Icc L R, 0 ≤ v t)
    (compare : ∀ t ∈ Ioo l r, k * w t ≤ v t ∧ g t ≤ f t - d / 2) :
    L ≤ l ∧ r ≤ R ∧
      k * (a * action f w l r h + b * (∫ t in l..r, w t)) ≤ action g v L R h := by
  obtain ⟨left, right⟩ := outer.contains_core inner.left_lt.le inner.lt_right.le
    (fun t ht => by linarith only [inner.accessible t ht, (compare t ht).2, hd])
  have lr := (inner.left_lt.trans inner.lt_right).le
  have sub : Icc l r ⊆ Icc L R := Icc_subset_Icc left right
  let u := fun t => w t * √(2 * (h - f t))
  have ji : IntervalIntegrable u volume l r :=
    (bw.mul ((continuousOn_const.mul (continuousOn_const.sub bf)).sqrt)).intervalIntegrable_of_Icc lr
  have wi : IntervalIntegrable w volume l r := bw.intervalIntegrable_of_Icc lr
  have oi : IntervalIntegrable (fun t => v t * √(2 * (h - g t))) volume l r :=
    ((gv.mono sub).mul ((continuousOn_const.mul (continuousOn_const.sub (gf.mono sub))).sqrt)).intervalIntegrable_of_Icc lr
  have bound := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) lr
    (((ji.const_mul a).add (wi.const_mul b)).const_mul k) oi (fun t ht => by
      have q := compare t ht
      have p := inner.accessible t ht
      have speed : a * √(2 * (h - f t)) + b ≤ √(2 * (h - g t)) :=
        affine_le_speed hd unit (sqrt_nonneg _) (by
          rw [Real.sq_sqrt (by linarith only [p]),Real.sq_sqrt (by linarith only [p, q.2, hd])]
          linarith only [q.2])
      change k * (a * u t + b * w t) ≤ _
      calc k * (a * u t + b * w t) = k * w t * (a * √(2 * (h - f t)) + b) := by dsimp [u]; ring
           _ ≤ k * w t * √(2 * (h - g t)) := mul_le_mul_of_nonneg_left speed (mul_nonneg hk (wn t (Ioo_subset_Icc_self ht)))
           _ ≤ _ := mul_le_mul_of_nonneg_right q.1 (sqrt_nonneg _))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (ji.const_mul a) (wi.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at bound
  exact ⟨left, right, bound.trans (action_mono_interval left lr right gf gv vn)⟩

end PlasmaLean.Kinetic.MirrorActionEnvelope
