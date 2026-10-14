/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FirstIntegral
public import PlasmaLean.Theory.Fields.Maxwell
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Clebsch fields are divergence free

For C² potentials ψ, χ the Clebsch field B = ∇ψ × ∇χ has an actual Fréchet derivative
`DB(x) v = (Hψ v) × ∇χ + ∇ψ × (Hχ v)`, where `H` is the Hessian operator (derivative of
the gradient). Since Hessians are symmetric (Schwarz, `ContDiffAt.isSymmSndFDerivAt`),
each term has zero divergence, so `∇ · B = 0`. Divergence and curl use the operator
conventions of `PlasmaLean.Theory.Fields.Maxwell`.

Reusable tools: `hasFDerivAt_of_coords` assembles a vector derivative from coordinate
derivatives; `divergence_cross_left/right` show v ↦ (L v) × b and v ↦ a × (L v) are
trace free whenever L has a symmetric coordinate matrix.

Scope: this is a pointwise differential identity. It says nothing about curl (a Clebsch
field need not be curl free, so need not be a vacuum field), about coil realizability,
or about field-line topology beyond the first-integral theorems.
-/

open scoped RealInnerProductSpace
public section
noncomputable section
namespace PlasmaLean.Fields
open WithLp

/-- Assemble a vector-valued derivative from derivatives of the three coordinates. -/
theorem hasFDerivAt_of_coords {B : Space → Space} {L : Fin 3 → (Space →L[ℝ] ℝ)} {x : Space}
    (h : ∀ k, HasFDerivAt (fun y => B y k) (L k) x) :
    HasFDerivAt B (∑ k, (L k).smulRight (basis k)) x := by
  have hB : B = fun y => ∑ k, B y k • basis k := by
    funext y
    ext j
    fin_cases j <;> simp [Fin.sum_univ_three, basis]
  rw [hB]
  exact HasFDerivAt.fun_sum (fun k _ => (h k).smul_const (basis k))

/-- Coordinates of an assembled operator. -/
theorem coords_apply (L : Fin 3 → (Space →L[ℝ] ℝ)) (v : Space) (j : Fin 3) :
    (∑ k, (L k).smulRight (basis k)) v j = L j v := by
  fin_cases j <;> simp [Fin.sum_univ_three, basis]

/-- An operator whose coordinate matrix `(L eᵢ)ⱼ` is symmetric. -/
@[expose] def CoordSymm (L : Space →L[ℝ] Space) : Prop :=
  ∀ i j, L (basis i) j = L (basis j) i

/-- Sanity check: the identity operator is coordinate symmetric. -/
theorem coordSymm_id : CoordSymm (ContinuousLinearMap.id ℝ Space) := by
  intro i j
  by_cases h : i = j
  · rw [h]
  · simp [basis, h, Ne.symm h]

/-- For symmetric `L`, the field derivative `v ↦ (L v) × b` is trace free. -/
theorem divergence_cross_left {L : Space →L[ℝ] Space} (hL : CoordSymm L) (b : Space) :
    divergence ((crossBilinear.flip b).comp L) = 0 := by
  rw [divergence_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    crossBilinear_apply]
  rw [(cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2,
    hL 0 1, hL 0 2, hL 1 2]
  ring

/-- For symmetric `L`, the field derivative `v ↦ a × (L v)` is trace free. -/
theorem divergence_cross_right {L : Space →L[ℝ] Space} (hL : CoordSymm L) (a : Space) :
    divergence ((crossBilinear a).comp L) = 0 := by
  rw [divergence_apply]
  simp only [ContinuousLinearMap.comp_apply, crossBilinear_apply]
  rw [(cross_coords _ _).1, (cross_coords _ _).2.1, (cross_coords _ _).2.2,
    hL 0 1, hL 0 2, hL 1 2]
  ring

/-- Hessian operator: the derivative of the gradient, assembled by coordinates. -/
@[expose] def hessianOp (ψ : Space → ℝ) (x : Space) : Space →L[ℝ] Space :=
  ∑ k, ((ContinuousLinearMap.apply ℝ ℝ (basis k)).comp
    (fderiv ℝ (fderiv ℝ ψ) x)).smulRight (basis k)

/-- Coordinates of the Hessian operator are second derivatives. -/
theorem hessianOp_apply (ψ : Space → ℝ) (x v : Space) (j : Fin 3) :
    hessianOp ψ x v j = fderiv ℝ (fderiv ℝ ψ) x v (basis j) := by
  rw [hessianOp, coords_apply]
  rfl

/-- Gradient coordinates are directional derivatives along the basis. -/
theorem gradient_coord (ψ : Space → ℝ) (y : Space) (k : Fin 3) :
    gradient ψ y k = fderiv ℝ ψ y (basis k) := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

/-- For C² ψ the gradient has the Hessian operator as actual derivative. -/
theorem gradient_hasFDerivAt {ψ : Space → ℝ} {x : Space} (h : ContDiffAt ℝ 2 ψ x) :
    HasFDerivAt (gradient ψ) (hessianOp ψ x) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply hasFDerivAt_of_coords
  intro k
  have hk := (ContinuousLinearMap.apply ℝ ℝ (basis k)).hasFDerivAt.comp x hd.hasFDerivAt
  convert hk using 1
  funext y
  simp [gradient_coord]

/-- Schwarz: the Hessian operator of a C² function is coordinate symmetric. -/
theorem hessianOp_symm {ψ : Space → ℝ} {x : Space} (h : ContDiffAt ℝ 2 ψ x) :
    CoordSymm (hessianOp ψ x) := by
  intro i j
  rw [hessianOp_apply, hessianOp_apply]
  exact (h.isSymmSndFDerivAt (by simp)).eq _ _

/-- Actual derivative of a Clebsch field of C² potentials. -/
theorem clebsch_hasFDerivAt {ψ χ : Space → ℝ} {x : Space} (hψ : ContDiffAt ℝ 2 ψ x)
    (hχ : ContDiffAt ℝ 2 χ x) :
    HasFDerivAt (clebschField ψ χ)
      ((crossBilinear (gradient ψ x)).comp (hessianOp χ x) +
        (crossBilinear.flip (gradient χ x)).comp (hessianOp ψ x)) x := by
  have h := crossBilinear.hasFDerivAt_of_bilinear (gradient_hasFDerivAt hψ)
    (gradient_hasFDerivAt hχ)
  refine HasFDerivAt.congr_fderiv (f := clebschField ψ χ) h ?_
  ext1 v
  simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL]

/-- Clebsch fields of C² potentials are divergence free: ∇ · (∇ψ × ∇χ) = 0. -/
theorem clebsch_divergence_free {ψ χ : Space → ℝ} {x : Space} (hψ : ContDiffAt ℝ 2 ψ x)
    (hχ : ContDiffAt ℝ 2 χ x) : divergence (fderiv ℝ (clebschField ψ χ) x) = 0 := by
  rw [(clebsch_hasFDerivAt hψ hχ).fderiv, divergence, map_add, ← divergence, ← divergence,
    divergence_cross_right (hessianOp_symm hχ), divergence_cross_left (hessianOp_symm hψ),
    add_zero]

/-- Degenerate case: a constant second potential gives the zero field. -/
theorem clebsch_const_right (ψ : Space → ℝ) (k : ℝ) :
    clebschField ψ (fun _ => k) = fun _ => 0 := by
  funext x
  have hg : gradient (fun _ : Space => k) x = 0 := by
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using hasFDerivAt_const k x
  simp [clebschField, hg, cross]

/-- Antisymmetry: swapping the potentials reverses the Clebsch field. -/
theorem clebsch_swap (ψ χ : Space → ℝ) (x : Space) :
    clebschField χ ψ x = -clebschField ψ χ x := by
  simp only [clebschField, cross]
  rw [← toLp_neg, cross_anticomm]

end PlasmaLean.Fields
