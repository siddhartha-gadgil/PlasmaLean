/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormCalculus
public import PlasmaLean.Sanity.Forms

/-!
# Sanity checks for `Theory/Fields/FormCalculus`

* Accepted: the uniform weakly quasisymmetric fixture has an invariant flux form
  (`lieDerivForm_uniform`); the hyperbolic vacuum field has a scalar and a vector potential on
  all of `ℝ³` (`hyperbolic_scalarPotential`, `hyperbolic_vectorPotential`).
* Rejected: the flux form of the uniform field is not invariant under the dilation field
  `ξ(x) = x`: `L_ξ ω = 2ω ≠ 0` (`lieDerivForm_dilation_ne_zero`). So `L_ξ ω = 0` has content.
* Hypothesis check: the dilation field satisfies no equation `ι_ξ ω = -dψ` with the uniform flux
  form near any point, for any `C²` potential (`dilation_not_hamiltonian`); otherwise
  `lieDerivForm_eq_zero_of_interior` would contradict the rejected fixture.
* The rejected fixture for the potential theorems (a vacuum field with no potential, on a region
  that is not star-convex) is not in this file: it is `wireField_no_potential` in
  `Sanity/FormTopology`.
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormCalculus

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open TauCeti Topology

/-- Accepted fixture: for the uniform field `e_z` with generator `e_z`, `L_ξ ω = 0`. -/
theorem lieDerivForm_uniform (x : Space) :
    lieDerivForm (fun _ => basis 2) (fluxField fun _ => basis 2) x = 0 :=
  weakQS_uniform.lieDerivForm_flux_eq_zero isOpen_univ (fun _ _ => differentiableAt_const _)
    (fun y _ => by simp [fieldDiv, divOp]) (fun _ _ => contDiffAt_const) (Set.mem_univ x)

/-- Rejected fixture: the uniform flux form is not invariant under the dilation field
`ξ(x) = x`; on `(e_x, e_y)` the Lie derivative is `2`. -/
theorem lieDerivForm_dilation_apply (x : Space) :
    lieDerivForm (fun y : Space => y) (fluxField fun _ => basis 2) x ![basis 0, basis 1] = 2 := by
  rw [lieDerivForm_apply]
  have hc : fderiv ℝ (fluxField fun _ : Space => basis 2) x = 0 := by
    change fderiv ℝ (fun _ : Space => flux (basis 2)) x = 0
    simp
  simp [hc, Function.update_eq_self, fluxField_apply, flux_apply, volForm_vec, basis]

/-- The dilation field does not preserve the uniform flux form. -/
theorem lieDerivForm_dilation_ne_zero (x : Space) :
    lieDerivForm (fun y : Space => y) (fluxField fun _ => basis 2) x ≠ 0 := by
  intro h
  have := lieDerivForm_dilation_apply x
  rw [h] at this
  norm_num at this

/-- Hypothesis check: there is no `C²` potential `ψ` with `ι_ξ ω = -dψ` near `x` for the
dilation field and the uniform flux form (the form `ι_ξ ω = x dy - y dx` is not closed). -/
theorem dilation_not_hamiltonian (x : Space) (ψ : Space → ℝ) (hψ : ContDiffAt ℝ 2 ψ x) :
    ¬ ∀ᶠ y in 𝓝 x, ((fluxField fun _ => basis 2) y).curryLeft y = -formGrad ψ y := fun h =>
  lieDerivForm_dilation_ne_zero x
    (lieDerivForm_eq_zero_of_interior
      (show DifferentiableAt ℝ (fun _ : Space => flux (basis 2)) x from differentiableAt_const _)
      differentiableAt_id
      (show extDeriv (fun _ : Space => flux (basis 2)) x = 0 by
        rw [extDeriv_flux]; simp [fieldDiv, divOp])
      h hψ)

/-- Accepted fixture: the hyperbolic vacuum field is a gradient on `ℝ³`. -/
theorem hyperbolic_scalarPotential :
    ∃ φ : Space → ℝ, φ 0 = 0 ∧ ∀ x, hyperbolicField x = gradient φ x := by
  obtain ⟨φ, -, h0, h⟩ :=
    hyperbolic_gradient_vacuum.exists_scalarPotential (starConvex_univ (0 : Space))
  exact ⟨φ, h0, fun x => h x (Set.mem_univ x)⟩

/-- Accepted fixture: the hyperbolic vacuum field is a curl on `ℝ³`. -/
theorem hyperbolic_vectorPotential :
    ∃ A : Space → Space, ∀ x, hyperbolicField x = fieldCurl A x := by
  obtain ⟨A, -, h⟩ :=
    hyperbolic_gradient_vacuum.exists_vectorPotential (starConvex_univ (0 : Space))
  exact ⟨A, fun x => h x (Set.mem_univ x)⟩

end PlasmaLean.Sanity.FormCalculus
