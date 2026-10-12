/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.CircularCoil
public import PlasmaLean.Theory.Fields.CoilPerturbation

/-!
# Circular coils in arbitrary three-dimensional poses

An explicit linear isometry and centre specify a placed circle. The parameter
orientation is inherited from the supplied map; reflections are allowed and are
NOT silently treated as proper rotations in a magnetic-field transformation law.
Position and tangent errors follow from translation and operator-norm pose errors.
This permits tilted/interlinked coil candidates, but proves neither linking nor
confinement for a particular assembly. No CNT geometry coefficients are invented.
-/
public section
noncomputable section
namespace PlasmaLean.Geometry
open Fields

/-- A circular centerline with explicit centre and orthogonal pose. -/
@[expose] def placedCircle (Q : Space ≃ₗᵢ[ℝ] Space) (center : Space) (R t : ℝ) : Space :=
  center + Q (circularCoil R 0 t)

/-- Actual angular derivative of a placed circle. -/
theorem placedCircle_derivative (Q : Space ≃ₗᵢ[ℝ] Space) (center : Space) (R t : ℝ) :
    HasDerivAt (placedCircle Q center R) (Q (circularTangent R t)) t := by
  exact (Q.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (circularCoil_derivative R 0 t)).const_add center

/-- Rigid placement preserves the exact tangent norm. -/
theorem placedCircle_speed (Q : Space ≃ₗᵢ[ℝ] Space) (center : Space) (R t : ℝ) :
    ‖deriv (placedCircle Q center R) t‖ = |R| := by
  rw [(placedCircle_derivative Q center R t).deriv, Q.norm_map, circularTangent_norm]

/-- Every placed circle is a C¹ curve in the actual real-derivative sense. -/
theorem placedCircle_C1 (Q : Space ≃ₗᵢ[ℝ] Space) (center : Space) (R : ℝ) :
    Differentiable ℝ (placedCircle Q center R) ∧ Continuous (deriv (placedCircle Q center R)) := by
  refine ⟨fun t => (placedCircle_derivative Q center R t).differentiableAt, ?_⟩
  have hd : deriv (placedCircle Q center R) = fun t => Q (circularTangent R t) :=
    funext (fun t => (placedCircle_derivative Q center R t).deriv)
  rw [hd]
  exact Q.continuous.comp (circularTangent_continuous R)

/-- Closure is preserved by rigid placement, including the original orientation convention. -/
theorem placedCircle_periodic (Q : Space ≃ₗᵢ[ℝ] Space) (center : Space) (R : ℝ) :
    Function.Periodic (placedCircle Q center R) (2 * Real.pi) := by
  intro t
  simp only [placedCircle, circularCoil_periodic R 0 t]

/-- A positive-radius placed circle remains simple during a single half-open turn. -/
theorem placedCircle_injective_on_turn (Q : Space ≃ₗᵢ[ℝ] Space) (center : Space)
    {R : ℝ} (hR : R ≠ 0) : Set.InjOn (placedCircle Q center R) (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht u hu he
  exact circularCoil_injective_on_turn hR 0 ht hu
    (Q.injective (add_left_cancel he))

/-- Exact distance of the reference circle from its centre. -/
theorem circularCoil_zero_norm (R t : ℝ) : ‖circularCoil R 0 t‖ = |R| := by
  have hs : ‖circularCoil R 0 t‖ ^ 2 = R ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_three]
    change (R * Real.cos t) ^ 2 + (R * Real.sin t) ^ 2 + (0 : ℝ) ^ 2 = R ^ 2
    nlinarith [congrArg (fun s : ℝ => R ^ 2 * s) (Real.sin_sq_add_cos_sq t)]
  nlinarith [norm_nonneg (circularCoil R 0 t), abs_nonneg R, sq_abs R]

/-- All centreline points have the same exact distance from the specified centre. -/
theorem placedCircle_radius (Q : Space ≃ₗᵢ[ℝ] Space) (center : Space) (R t : ℝ) :
    ‖placedCircle Q center R t - center‖ = |R| := by
  simp only [placedCircle, add_sub_cancel_left, Q.norm_map, circularCoil_zero_norm]

/-- Translation and orthogonal-pose errors give a full-curve position budget.
The rotation error α is an operator-norm bound, not an angle measured in degrees. -/
theorem placedCircle_position_error (Q P : Space ≃ₗᵢ[ℝ] Space) (center actualCenter : Space)
    (R t : ℝ) {ε α : ℝ} (hc : ‖actualCenter - center‖ ≤ ε)
    (hQ : ‖P.toContinuousLinearEquiv.toContinuousLinearMap -
      Q.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ α) :
    ‖placedCircle P actualCenter R t - placedCircle Q center R t‖ ≤ ε + α * |R| := by
  let D := P.toContinuousLinearEquiv.toContinuousLinearMap -
    Q.toContinuousLinearEquiv.toContinuousLinearMap
  have he : placedCircle P actualCenter R t - placedCircle Q center R t =
      (actualCenter - center) + D (circularCoil R 0 t) := by
    change actualCenter + P (circularCoil R 0 t) - (center + Q (circularCoil R 0 t)) =
      (actualCenter - center) + (P (circularCoil R 0 t) - Q (circularCoil R 0 t))
    abel
  rw [he]
  have hb := ContinuousLinearMap.le_of_opNorm_le (f := D) hQ (circularCoil R 0 t)
  rw [circularCoil_zero_norm] at hb
  exact (norm_add_le _ _).trans (add_le_add hc hb)

/-- The identical pose error gives a tangent budget; translation contributes none. -/
theorem placedCircle_tangent_error (Q P : Space ≃ₗᵢ[ℝ] Space) (center actualCenter : Space)
    (R t : ℝ) {α : ℝ} (hQ : ‖P.toContinuousLinearEquiv.toContinuousLinearMap -
      Q.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ α) :
    ‖deriv (placedCircle P actualCenter R) t - deriv (placedCircle Q center R) t‖ ≤ α * |R| := by
  rw [(placedCircle_derivative P actualCenter R t).deriv,
    (placedCircle_derivative Q center R t).deriv]
  have hb := ContinuousLinearMap.le_of_opNorm_le
    (f := P.toContinuousLinearEquiv.toContinuousLinearMap -
      Q.toContinuousLinearEquiv.toContinuousLinearMap) hQ (circularTangent R t)
  change ‖P (circularTangent R t) - Q (circularTangent R t)‖ ≤ α * ‖circularTangent R t‖ at hb
  rwa [circularTangent_norm] at hb

end PlasmaLean.Geometry
