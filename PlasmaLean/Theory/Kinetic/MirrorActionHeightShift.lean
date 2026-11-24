/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope

/-! # Finite action comparisons between first wells on different field lines -/

public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionEnvelope
open Set Real MeasureTheory MirrorHeightAction

/-- Comparing the two profiles on the interior of one well at a shifted height
forces the second first well to contain it and controls the action between its true contacts. -/
theorem LaunchWell.transfer_height {f g w v : ℝ → ℝ} {c H h l r L R s : ℝ}
    (base : LaunchWell f c H l r) (other : LaunchWell g c h L R)
    (bf : ContinuousOn f (Icc l r)) (bw : ContinuousOn w (Icc l r))
    (gf : ContinuousOn g (Icc L R)) (gv : ContinuousOn v (Icc L R))
    (vn : ∀ t ∈ Icc L R, 0 ≤ v t)
    (compare : ∀ t ∈ Ioo l r, s * w t ≤ v t ∧ H - f t ≤ h - g t) :
    L ≤ l ∧ r ≤ R ∧ s * action f w l r H ≤ action g v L R h := by
  obtain ⟨left, right⟩ := other.contains_core base.left_lt.le base.lt_right.le (by
    intro t ht
    linarith only [base.accessible t ht, (compare t ht).2])
  have lr := (base.left_lt.trans base.lt_right).le
  have sub : Icc l r ⊆ Icc L R := Icc_subset_Icc left right
  have bc : ContinuousOn (fun t => w t * √(2 * (H - f t))) (Icc l r) :=
    bw.mul ((continuousOn_const.mul (continuousOn_const.sub bf)).sqrt)
  have oc : ContinuousOn (fun t => v t * √(2 * (h - g t))) (Icc l r) :=
    (gv.mono sub).mul ((continuousOn_const.mul (continuousOn_const.sub (gf.mono sub))).sqrt)
  have point (t : ℝ) (ht : t ∈ Ioo l r) :
      s * (w t * √(2 * (H - f t))) ≤ v t * √(2 * (h - g t)) := by
    obtain ⟨wt, gap⟩ := compare t ht
    rw [← mul_assoc]
    exact mul_le_mul wt (sqrt_le_sqrt (by linarith only [gap])) (sqrt_nonneg _)
      (vn t (sub (Ioo_subset_Icc_self ht)))
  have cmp := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) lr
    ((bc.intervalIntegrable_of_Icc lr).const_mul s) (oc.intervalIntegrable_of_Icc lr) point
  rw [intervalIntegral.integral_const_mul] at cmp
  exact ⟨left, right, cmp.trans (action_mono_interval left lr right gf gv vn)⟩

end PlasmaLean.Kinetic.MirrorActionEnvelope
