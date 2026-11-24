/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-! # Nonexpansive retractions for validated Hilbert-space trajectories

The variational inequality for a nearest point makes its projection
nonexpansive. On a ball centered at zero, the projection has the radial
formula which fixes every point of the trial tube.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.HilbertRetraction

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A map satisfying the normal variational inequality on its image is
nonexpansive. Completeness and dimension do not enter this inequality. -/
theorem lipschitz_of_normal {P : E → E} {K : Set E} (hmem : ∀ x, P x ∈ K)
    (hn : ∀ x y, y ∈ K → ⟪x - P x, y - P x⟫ ≤ 0) : LipschitzWith 1 P := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  let d := P x - P y
  have hx : 0 ≤ ⟪x - P x, d⟫ := by
    have e := hn x (P y) (hmem y)
    simpa only [show P y - P x = -d by dsimp [d]; abel, inner_neg_right, neg_nonpos] using e
  have hy : ⟪y - P y, d⟫ ≤ 0 := hn y (P x) (hmem x)
  have eq : x - y = (x - P x) + d - (y - P y) := by dsimp [d]; abel
  have bound : ‖d‖^2 ≤ ⟪x - y, d⟫ := by
    rw [eq, inner_sub_left, inner_add_left, real_inner_self_eq_norm_sq]
    linarith
  have product := bound.trans (real_inner_le_norm (x-y) d)
  by_cases hd : d = 0
  · change ‖d‖ ≤ _
    simp [hd]
  · apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hd)
    simpa only [pow_two] using product

/-- Every nonempty complete convex subset admits a nonexpansive metric
projection which fixes the subset pointwise. -/
theorem convex_retraction {K : Set E} (hK : K.Nonempty) (complete : IsComplete K)
    (convex : Convex ℝ K) :
    ∃ P : E → E, LipschitzWith 1 P ∧ (∀ x, P x ∈ K) ∧ ∀ x ∈ K, P x = x := by
  choose P hm hp using exists_norm_eq_iInf_of_complete_convex hK complete convex
  have hn (x y : E) (hy : y ∈ K) : ⟪x - P x, y - P x⟫ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero convex (hm x)).mp (hp x) y hy
  refine ⟨P, lipschitz_of_normal hm hn, hm, fun x hx => ?_⟩
  have zero := hn x x hx
  rw [real_inner_self_eq_norm_sq] at zero
  exact (sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x-P x)]))).symm

/-- Nearest point in the closed radius-R ball, given by radial scaling outside. -/
def radial (R : ℝ) (x : E) : E := if ‖x‖ ≤ R then x else (R / ‖x‖) • x

/-- The radial formula gives a globally nonexpansive retraction onto the
closed trial ball, including radius zero. -/
theorem radial_retraction {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (radial R : E → E) ∧
      (∀ x : E, radial R x ∈ Metric.closedBall 0 R) ∧
      ∀ x ∈ Metric.closedBall (0 : E) R, radial R x = x := by
  have mem (x : E) : radial R x ∈ Metric.closedBall 0 R := by
    change dist _ _ ≤ _
    rw [dist_zero_right, radial]
    split_ifs with h
    · exact h
    · have pos : 0 < ‖x‖ := hR.trans_lt (lt_of_not_ge h)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR pos.le),
        div_mul_cancel₀ _ pos.ne']
  refine ⟨lipschitz_of_normal mem ?_, mem, fun x hx => ?_⟩
  · intro x y hy
    have yn : ‖y‖ ≤ R := by simpa using hy
    by_cases inside : ‖x‖ ≤ R
    · simp [radial, inside]
    · let c := R / ‖x‖
      have pos : 0 < ‖x‖ := hR.trans_lt (lt_of_not_ge inside)
      have coeff : 0 ≤ 1-c := sub_nonneg.mpr ((div_le_one pos).mpr (lt_of_not_ge inside).le)
      have ray : x - c • x = (1-c) • x := by rw [sub_smul, one_smul]
      have length : c * ‖x‖^2 = ‖x‖ * R := by dsimp [c]; field_simp
      have ip := (real_inner_le_norm x y).trans (mul_le_mul_of_nonneg_left yn pos.le)
      change ⟪x - radial R x, y - radial R x⟫ ≤ 0
      rw [radial, ite_eq_right inside, ray, real_inner_smul_left, inner_sub_right,
        real_inner_smul_right,
        real_inner_self_eq_norm_sq, length]
      exact mul_nonpos_of_nonneg_of_nonpos coeff (sub_nonpos.mpr ip)
  · exact ite_eq_left (by simpa using hx)

end PlasmaLean.Fields.HilbertRetraction
