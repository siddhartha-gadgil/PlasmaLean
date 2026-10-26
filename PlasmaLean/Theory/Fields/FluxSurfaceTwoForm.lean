/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.CurlProduct
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The magnetic 2-form vanishes on flux surfaces

The magnetic flux 2-form is `ω_B = i_B vol`, i.e. `ω_B(u, v) = vol(B, u, v) = ⟪B, u × v⟫`
(`magneticTwoForm`). If `B` is tangent to the level sets of a flux function `ψ`
(`B · ∇ψ = 0`) and `∇ψ ≠ 0`, then `ω_B` restricted to the level set through `x` vanishes:
`ω_B(u, v) = 0` for all `u, v ⟂ ∇ψ(x)` (`magneticTwoForm_flux_surface`). This is the pointwise
statement behind the "flat bundle on flux surfaces" correction of the implementation plan (§1):
the pull-back of `ω_B` to a flux surface is zero, so no curvature is carried by `ω_B` there.

The proof is the vector identity (`triple_smul_eq`)

`⟪a, b × c⟫ d = ⟪d, a⟫ (b × c) + ⟪d, b⟫ (c × a) + ⟪d, c⟫ (a × b)`,

applied with `d = ∇ψ(x)`: the right side vanishes, hence so does the triple product.

Results.

* `magneticTwoForm`, `magneticTwoForm_eq_cross_inner` (`ω_B(u, v) = ⟪B × u, v⟫`),
  `magneticTwoForm_antisymm`.
* `triple_smul_eq`: the identity above.
* `magneticTwoForm_eq_zero_of_orthogonal`: linear-algebra form, `n ≠ 0`, `B, u, v ⟂ n`.
* `magneticTwoForm_flux_surface`: the field form with `ψ`, `B`, `x`.
* sanity: `magneticTwoForm_basis` (`ω_{e_z}(e_x, e_y) = 1`, so the form is nonzero off the
  tangency hypothesis) and `magneticTwoForm_tangent_example` (`B = e_x`, `ψ = z`).
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Fields

/-- Inner product of physical vectors in coordinates. -/
theorem inner_coords3 (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]; ring

/-- The magnetic flux 2-form `ω_B = i_B vol`: `ω_B(u, v) = vol(B, u, v) = ⟪B, u × v⟫`. -/
@[expose] def magneticTwoForm (B u v : Space) : ℝ := ⟪B, cross u v⟫

/-- `ω_B(u, v) = ⟪B × u, v⟫`. -/
theorem magneticTwoForm_eq_cross_inner (B u v : Space) :
    magneticTwoForm B u v = ⟪cross B u, v⟫ := by
  obtain ⟨a0, a1, a2⟩ := cross_coords u v
  obtain ⟨b0, b1, b2⟩ := cross_coords B u
  rw [magneticTwoForm, inner_coords3, inner_coords3, a0, a1, a2, b0, b1, b2]
  ring

/-- `ω_B` is antisymmetric. -/
theorem magneticTwoForm_antisymm (B u v : Space) :
    magneticTwoForm B u v = -magneticTwoForm B v u := by
  obtain ⟨a0, a1, a2⟩ := cross_coords u v
  obtain ⟨b0, b1, b2⟩ := cross_coords v u
  rw [magneticTwoForm, magneticTwoForm, inner_coords3, inner_coords3, a0, a1, a2, b0, b1, b2]
  ring

/-- The vector identity
`⟪a, b × c⟫ d = ⟪d, a⟫ (b × c) + ⟪d, b⟫ (c × a) + ⟪d, c⟫ (a × b)` in `ℝ³`. -/
theorem triple_smul_eq (a b c d : Space) :
    ⟪a, cross b c⟫ • d =
      ⟪d, a⟫ • cross b c + ⟪d, b⟫ • cross c a + ⟪d, c⟫ • cross a b := by
  obtain ⟨p0, p1, p2⟩ := cross_coords b c
  obtain ⟨q0, q1, q2⟩ := cross_coords c a
  obtain ⟨r0, r1, r2⟩ := cross_coords a b
  apply space_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_coords3, p0, p1, p2, q0, q1,
      q2, r0, r1, r2] <;> ring

/-- **Linear-algebra form.** If `n ≠ 0` and `B`, `u`, `v` are all orthogonal to `n`, then
`ω_B(u, v) = 0`. -/
theorem magneticTwoForm_eq_zero_of_orthogonal {B u v n : Space} (hn : n ≠ 0)
    (hB : ⟪B, n⟫ = 0) (hu : ⟪u, n⟫ = 0) (hv : ⟪v, n⟫ = 0) : magneticTwoForm B u v = 0 := by
  have h := triple_smul_eq B u v n
  rw [real_inner_comm B n, hB, real_inner_comm u n, hu, real_inner_comm v n, hv] at h
  simp only [zero_smul, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_right hn

/-- **The magnetic 2-form vanishes on flux surfaces.** If `∇ψ(x) ≠ 0` and `B(x) · ∇ψ(x) = 0`,
then `ω_{B(x)}(u, v) = 0` for all `u`, `v` tangent to the level set of `ψ` through `x`
(`u, v ⟂ ∇ψ(x)`). -/
theorem magneticTwoForm_flux_surface {ψ : Space → ℝ} {B : Space → Space} {x : Space}
    (hgrad : gradient ψ x ≠ 0) (htan : ⟪B x, gradient ψ x⟫ = 0) {u v : Space}
    (hu : ⟪u, gradient ψ x⟫ = 0) (hv : ⟪v, gradient ψ x⟫ = 0) :
    magneticTwoForm (B x) u v = 0 :=
  magneticTwoForm_eq_zero_of_orthogonal hgrad htan hu hv

/-- Sanity: `ω_{e_z}(e_x, e_y) = 1`, so `ω_B` does not vanish on planes to which `B` is
transverse. -/
theorem magneticTwoForm_basis : magneticTwoForm (basis 2) (basis 0) (basis 1) = 1 := by
  obtain ⟨a0, a1, a2⟩ := cross_coords (basis 0) (basis 1)
  rw [magneticTwoForm, inner_coords3, a0, a1, a2]
  simp

/-- Sanity: for `ψ = z` and `B = e_x` (tangent to the planes `z = const`), `ω_B` vanishes on
the tangent vectors `e_x`, `e_y`. -/
theorem magneticTwoForm_tangent_example (x : Space) :
    magneticTwoForm (basis 0) (basis 0) (basis 1) = 0 := by
  have hg : gradient (fun y : Space => y 2) x = basis 2 := by
    have h : fderiv ℝ (fun y : Space => y 2) x =
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) :=
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.fderiv
    apply space_ext <;> rw [← fderiv_apply_basis, h] <;> simp
  refine magneticTwoForm_flux_surface (ψ := fun y : Space => y 2) (B := fun _ => basis 0)
    (x := x) ?_ ?_ ?_ ?_ <;>
    rw [hg]
  · intro h
    have := congrArg (fun v : Space => v 2) h
    simp at this
  all_goals simp [EuclideanSpace.inner_single_right]

end PlasmaLean.Fields
