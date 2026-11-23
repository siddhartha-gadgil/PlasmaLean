/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.NoetherLagrangian

/-!
# Sanity checks for `Theory/Kinetic/NoetherLagrangian`

The uniform field `B₀ e_z` in the Landau gauge `A = B₀ x e_y`.

* `curl_landau`: `∇ × A = B₀ e_z`.
* Accepted: `landau_momentum_conserved`: along every Lorentz orbit in the uniform field,
  `m v_y + q B₀ x` is constant (translation symmetry along `e_y`).
* Hypothesis check: `landau_not_invariant_x`: the Landau gauge is not invariant along `e_x`
  (for `B₀ ≠ 0`), so the theorem does not give conservation of `m v_x`.
* Regression (audit AV-M4), a potential that is not linear: `shearPotential`,
  `A = (x²/2) e_y`, with the position-dependent derivative `hasFDerivAt_shearPotential` and
  curl `curl_shearPotential`, `∇ × A = x e_z` (a field that is not uniform).
  `shear_momentum_conserved`: `m v_y + q x²/2` is constant along every Lorentz orbit in the
  field `x e_z`. `shearPotential_not_invariant_x`: the potential is not invariant along `e_x`.
-/

@[expose] public section

namespace PlasmaLean.Sanity.NoetherLagrangian

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum
open scoped RealInnerProductSpace

/-- The Landau gauge `A(x) = B₀ x e_y`, as a continuous linear map. -/
noncomputable def landau (B₀ : ℝ) : Space →L[ℝ] Space :=
  (B₀ • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ)).smulRight (coordVec 1)

/-- Components of the Landau gauge. -/
theorem landau_apply (B₀ : ℝ) (y : Space) : landau B₀ y = (B₀ * y 0) • coordVec 1 := by
  simp [landau]

/-- `∇ × A = B₀ e_z` for the Landau gauge. -/
theorem curl_landau (B₀ : ℝ) (y : Space) :
    fieldCurl (landau B₀) y = B₀ • coordVec 2 := by
  rw [fieldCurl, (landau B₀).fderiv]
  ext i
  fin_cases i <;> simp [curlOp, landau_apply]

/-- The Landau gauge is invariant under translation along `e_y`. -/
theorem landau_invariant_y (B₀ : ℝ) (y : Space) (s : ℝ) :
    landau B₀ (y + s • coordVec 1) = landau B₀ y := by
  simp [landau_apply]

/-- Hypothesis check: it is not invariant along `e_x` when `B₀ ≠ 0`. -/
theorem landau_not_invariant_x {B₀ : ℝ} (hB : B₀ ≠ 0) :
    ¬ ∀ (y : Space) (s : ℝ), landau B₀ (y + s • coordVec 0) = landau B₀ y := by
  intro h
  have h1 : B₀ = 0 := by
    simpa [landau_apply] using congrArg (fun z : Space => z 1) (h 0 1)
  exact hB h1

/-- **Accepted fixture**: in the uniform field `B₀ e_z`, the canonical momentum
`m v_y + q B₀ x` is constant along every Lorentz orbit. -/
theorem landau_momentum_conserved {m q B₀ : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (s t : ℝ) :
    m * v s 1 + q * (B₀ * x s 0) = m * v t 1 + q * (B₀ * x t 0) := by
  have key := noetherMomentum_translation_conserved (A := landau B₀) (e := coordVec 1) h
    (landau B₀).differentiable (fun y => (curl_landau B₀ y).symm) (landau_invariant_y B₀) s t
  simpa [noetherMomentum, landau_apply, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, inner_smul_left] using key

/-! ### Regression (audit AV-M4): a potential that is not linear -/

/-- The vector potential `A = (x²/2) e_y` of the sheared field `B = x e_z`. It is not linear,
so its derivative depends on the position. -/
noncomputable def shearPotential (y : Space) : Space := (y 0 ^ 2 / 2) • coordVec 1

/-- The derivative of `A = (x²/2) e_y` at `y` is `δ ↦ (x δ_x) e_y`. -/
theorem hasFDerivAt_shearPotential (y : Space) :
    HasFDerivAt shearPotential
      ((y 0 • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ)).smulRight (coordVec 1)) y := by
  have p0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt (x := y)
  have h := ((p0.pow 2).const_mul (1 / 2 : ℝ)).smul_const (coordVec 1 : Space)
  have hf : shearPotential = fun z : Space =>
      (1 / 2 * (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0) z ^ 2) • (coordVec 1 : Space) := by
    funext z
    rw [shearPotential]
    congr 1
    simp
    ring
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply]
  congr 1
  simp
  ring

/-- `A = (x²/2) e_y` is differentiable. -/
theorem differentiable_shearPotential : Differentiable ℝ shearPotential := fun y =>
  (hasFDerivAt_shearPotential y).differentiableAt

/-- Regression (audit AV-M4): `∇ × ((x²/2) e_y) = x e_z`, computed from the
position-dependent derivative. -/
theorem curl_shearPotential (y : Space) : fieldCurl shearPotential y = y 0 • coordVec 2 := by
  rw [fieldCurl, (hasFDerivAt_shearPotential y).fderiv]
  ext i
  fin_cases i <;> simp [curlOp]

/-- `A = (x²/2) e_y` is invariant under translation along `e_y`. -/
theorem shearPotential_invariant_y (y : Space) (s : ℝ) :
    shearPotential (y + s • coordVec 1) = shearPotential y := by
  simp [shearPotential]

/-- Hypothesis check: `A = (x²/2) e_y` is not invariant along `e_x`. -/
theorem shearPotential_not_invariant_x :
    ¬ ∀ (y : Space) (s : ℝ), shearPotential (y + s • coordVec 0) = shearPotential y := by
  intro h
  have h1 := congrArg (fun z : Space => z 1) (h 0 1)
  simp [shearPotential] at h1

/-- Regression (audit AV-M4): in the sheared field `B = x e_z`, which is not uniform and whose
potential `(x²/2) e_y` is not linear, the canonical momentum `m v_y + q x²/2` is constant along
every Lorentz orbit, from `noetherMomentum_translation_conserved`. -/
theorem shear_momentum_conserved {m q : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun y => y 0 • coordVec 2) x v) (s t : ℝ) :
    m * v s 1 + q * (x s 0 ^ 2 / 2) = m * v t 1 + q * (x t 0 ^ 2 / 2) := by
  have key := noetherMomentum_translation_conserved (A := shearPotential) (e := coordVec 1) h
    differentiable_shearPotential (fun y => (curl_shearPotential y).symm)
    shearPotential_invariant_y s t
  simpa [noetherMomentum, shearPotential, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, inner_smul_left] using key

end PlasmaLean.Sanity.NoetherLagrangian
