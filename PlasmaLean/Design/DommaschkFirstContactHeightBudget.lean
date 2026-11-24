/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.FirstMirrorRegularValues
public import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign

/-! # A first-contact slope budget at the archived QA2R mirror heights -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFirstContactHeightBudget

open Set MeasureTheory DommaschkFirstMirrorLaunchSign Kinetic.FirstMirror

/-- For brackets of width at most ten original slabs on each side, the measure of
heights with both outward slopes above 1/1250 exceeds half the archived band. -/
theorem good_height_measure {f g : ℝ → ℝ} {a b c d : ℝ}
    (p : Family f a b (height false) (height true))
    (q : Family g c d (height false) (height true)) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (wf : b - a ≤ 10 / 64) (wg : d - c ≤ 10 / 64)
    (df : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (dg : ∀ t ∈ Ioo c d, DifferentiableAt ℝ g t) :
    ENNReal.ofReal (667367655761/2500000000000000) ≤
      volume {H : ℝ | ∃ h : Icc (height false : ℝ) (height true), (h:ℝ) = H ∧
        1/1250 < deriv f (p.time h) ∧ 1/1250 < deriv g (q.time h)} := by
  have coef : ENNReal.ofReal (1/1250) *
      (ENNReal.ofReal (b-a) + ENNReal.ofReal (d-c)) ≤ ENNReal.ofReal (1/4000) := by
    have w := add_le_add (ENNReal.ofReal_le_ofReal wf) (ENNReal.ofReal_le_ofReal wg)
    apply (mul_le_mul_of_nonneg_left w (show 0 ≤ ENNReal.ofReal (1/1250) from zero_le)).trans
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    norm_num
  have eq : (667367655761/2500000000000000:ℝ) =
      (height true : ℝ) - (height false : ℝ) - 1/4000 := by norm_num [height]
  rw [eq,ENNReal.ofReal_sub _ (by norm_num)]
  exact (tsub_le_tsub_left coef _).trans (two_sided_good_heights p q ha hc (1/1250) df dg)

theorem majority : ((height true : ℝ) - height false)/2 < 667367655761/2500000000000000 := by
  norm_num [height]

end PlasmaLean.Design.DommaschkFirstContactHeightBudget
