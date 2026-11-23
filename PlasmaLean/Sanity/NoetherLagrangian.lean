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

end PlasmaLean.Sanity.NoetherLagrangian
