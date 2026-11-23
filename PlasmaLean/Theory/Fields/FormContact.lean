/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormBridges
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Geometry.Contact.Volume

/-!
# The wedge product and the contact condition, linked to TauCeti (v4.36.0)

`Theory/Fields/FormBridges` defines one wedge product by hand, `wedge12 : Form 1 → Form 2 →
Form 3`, and the contact condition `IsContactAt β x` (`β ∧ dβ ≠ 0`). This file identifies them
with the general objects of TauCeti.

* `wedge12_eq_wedge`: `wedge12 a b` is TauCeti's wedge product
  `ContinuousAlternatingMap.wedge a b` (normalized as in Lee, *Introduction to Smooth
  Manifolds*, Ch. 14).
* `isContactAt_iff_wedge`: the contact condition is `β ∧ dβ ≠ 0` for that product.
* `isContactAt_iff_nondegenerate`: the contact condition in the intrinsic form used by TauCeti
  (`Module.Dual.IsContact`): `β x ≠ 0`, and `dβ x` is nondegenerate on the plane `ker β x`.
* `IsBeltramiOn.reeb`: for a Beltrami field with `B ≠ 0`, the vector `R = B / ‖B‖²` satisfies
  the Reeb equations of `β = B♭`: `β(R) = 1` and `ι_R dβ = 0`. When `λ ≠ 0` the form is contact
  and `R` is its Reeb vector.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix
open scoped RealInnerProductSpace

/-! ## The wedge product -/

/-- TauCeti's wedge of a 1-form `α` with a 2-form, on a triple whose last two vectors are
killed by `α`. -/
theorem wedge_apply_of_ker (α : Form 1) (b : Form 2) (u w₀ w₁ : Space)
    (h₀ : α ![w₀] = 0) (h₁ : α ![w₁] = 0) :
    (ContinuousAlternatingMap.wedge α b : Form 3) ![u, w₀, w₁] = α ![u] * b ![w₀, w₁] := by
  have h := ContinuousAlternatingMap.pairedWedge_apply_vecCons_of_forall
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ α b u ![w₀, w₁]
    (fun i => by fin_cases i <;> assumption)
  have e : (Matrix.vecCons u ![w₀, w₁] ∘ Fin.cast (Nat.add_comm 1 2)) = ![u, w₀, w₁] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h
  rw [ContinuousAlternatingMap.wedge_def]
  simpa using h

/-- **`wedge12` is TauCeti's wedge product** of a 1-form and a 2-form. -/
theorem wedge12_eq_wedge (a : Form 1) (b : Form 2) :
    wedge12 a b = (ContinuousAlternatingMap.wedge a b : Form 3) := by
  apply density.symm.injective
  rw [density_symm_apply, density_symm_apply, wedge12_apply]
  obtain ⟨p, rfl⟩ := flat.surjective a
  have hp : p = p 0 • coordVec 0 + p 1 • coordVec 1 + p 2 • coordVec 2 := by
    ext i; fin_cases i <;> simp
  have hc (i j : Fin 3) : flat (coordVec i) ![coordVec j] = if i = j then 1 else 0 := by
    simp [flat_apply, EuclideanSpace.inner_single_left]
  have hf (i : Fin 3) : flat p ![coordVec i] = p i := by
    simp [flat_apply, EuclideanSpace.inner_single_right]
  have e0 := wedge_apply_of_ker (flat (coordVec 0)) b (coordVec 0) (coordVec 1) (coordVec 2)
    (by simp [hc]) (by simp [hc])
  have e1 := wedge_apply_of_ker (flat (coordVec 1)) b (coordVec 1) (coordVec 0) (coordVec 2)
    (by simp [hc]) (by simp [hc])
  have e2 := wedge_apply_of_ker (flat (coordVec 2)) b (coordVec 2) (coordVec 0) (coordVec 1)
    (by simp [hc]) (by simp [hc])
  rw [hf, hf, hf]
  conv_rhs => rw [hp]
  simp only [map_add, map_smul, ContinuousAlternatingMap.wedge_add_left,
    ContinuousAlternatingMap.wedge_smul_left, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [e0, form3_swap01 _ (coordVec 0) (coordVec 1) (coordVec 2), e1,
    form3_swap12 _ (coordVec 0) (coordVec 1) (coordVec 2),
    form3_swap01 _ (coordVec 0) (coordVec 2) (coordVec 1), e2]
  simp [hc]
  ring

/-! ## The contact condition -/

/-- The contact condition is `β ∧ dβ ≠ 0` for TauCeti's wedge product. -/
theorem isContactAt_iff_wedge (β : Space → Form 1) (x : Space) :
    IsContactAt β x ↔ (ContinuousAlternatingMap.wedge (β x) (extDeriv β x) : Form 3) ≠ 0 := by
  rw [IsContactAt, wedge12_eq_wedge]

/-- The first wedge power of a 2-form is the form itself. -/
theorem wedgePow_one (B : Form 2) : (B.wedgePow 1 : Form 2) = B := by
  ext v
  have h := ContinuousAlternatingMap.pairedWedge_apply_zero_left (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (B.wedgePow 0) B v
  have e : v ∘ Fin.cast (Nat.zero_add 2).symm = v := by
    funext i; rfl
  rw [e] at h
  rw [ContinuousAlternatingMap.wedgePow_succ]
  simpa using h

/-- **The contact condition in intrinsic form** (the one TauCeti uses for contact forms on
manifolds): `β ∧ dβ ≠ 0` at `x` exactly when `β x ≠ 0` and `dβ x` is nondegenerate on the plane
`ker β x`. This is TauCeti's linear contact volume criterion in dimension three. -/
theorem isContactAt_iff_nondegenerate (β : Space → Form 1) (x : Space) :
    IsContactAt β x ↔ β x ≠ 0 ∧ ∀ v, β x ![v] = 0 →
      (∀ w, β x ![w] = 0 → extDeriv β x ![v, w] = 0) → v = 0 := by
  have h := ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff (E := Space) (n := 1)
    (by simp) (β x) (extDeriv β x)
  rw [wedgePow_one] at h
  rw [isContactAt_iff_wedge, ContinuousAlternatingMap.wedge_def]
  exact h

/-! ## The Reeb vector of a Beltrami field -/

/-- **Reeb equations for a Beltrami field.** If `∇ × B = λ B` at `x` and `B x ≠ 0`, then
`R = B / ‖B‖²` satisfies `β(R) = 1` and `ι_R dβ = 0` for `β = B♭`. -/
theorem IsBeltramiOn.reeb {B : Space → Space} {lam : Space → ℝ} {U : Set Space}
    (h : IsBeltramiOn B lam U) {x : Space} (hx : x ∈ U) (hB : B x ≠ 0) :
    flat (B x) ![(‖B x‖ ^ 2)⁻¹ • B x] = 1 ∧
      (extDeriv (fun y => flat (B y)) x).curryLeft ((‖B x‖ ^ 2)⁻¹ • B x) = 0 := by
  have hn : ‖B x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hB)
  constructor
  · rw [flat_apply]
    simp [inner_smul_right, hn]
  · rw [extDeriv_flat, (h x hx).2, map_smul, curryLeft_flux_cross]
    obtain ⟨h0, h1, h2⟩ := cross_coords (lam x • B x) (B x)
    have hc : cross (lam x • B x) (B x) = 0 := by
      ext i; fin_cases i <;> simp [h0, h1, h2] <;> ring
    rw [hc]; simp

end PlasmaLean.Forms
