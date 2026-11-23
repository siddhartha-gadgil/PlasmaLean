/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormCalculus
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace
public import TauCeti.Geometry.Manifold.DeRham.SimplyConnected

/-!
# A bridge from the form kernel to forms on manifolds (TauCeti v4.36.0)

The form kernel writes a differential form on a region of `ℝ³` as a function
`Space → Form k`. TauCeti's de Rham theory is stated for forms on a manifold. An open subset
`U` of `ℝ³` is a manifold, and a rough form on it is, by definition, the field of alternating
maps `U → Form k`. So the bridge is restriction to `U`:

* `onOpens U β`: the manifold form on `U` with the values of `β`.
* `isSmoothForm_onOpens_iff`: it is `C^n` exactly when `β` is `C^n` on `U`.
* `mextDeriv_onOpens`: its manifold exterior derivative is the restriction of `extDeriv β`.

Both comparison theorems are TauCeti's (`isSmoothForm_opens_iff`, `mextDeriv_opens_eq_extDeriv`).

## Topological statements obtained through the bridge

* `VacuumForm.exists_scalarPotential_of_simplyConnected`,
  `VacuumField.exists_scalarPotential_of_simplyConnected`: on a **simply connected** open region
  a vacuum field is a gradient. This replaces the star-convexity hypothesis of
  `Theory/Fields/FormCalculus` by the topological one. It uses TauCeti's monodromy theorem
  `exists_mextDeriv_eq_of_simplyConnectedSpace`.
* `not_simplyConnected_of_no_potential`: conversely, a vacuum field on `U` that is not a
  gradient shows that `U` is not simply connected.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields
open TauCeti TopologicalSpace Topology
open scoped Manifold

/-- **The bridge**: the differential form on the manifold `U` (an open subset of `ℝ³`) with
the values of the field `β` of alternating maps. -/
def onOpens (U : Opens Space) {k : ℕ} (β : Space → Form k) : RoughForm 𝓘(ℝ, Space) U ℝ k :=
  fun x => β x

/-- The bridge does not change values. -/
@[simp] theorem onOpens_apply (U : Opens Space) {k : ℕ} (β : Space → Form k) (x : U) :
    onOpens U β x = β x := rfl

/-- Regularity is the same on both sides of the bridge. -/
theorem isSmoothForm_onOpens_iff (U : Opens Space) {k : ℕ} (β : Space → Form k)
    {n : WithTop ℕ∞} :
    IsSmoothForm 𝓘(ℝ, Space) n (onOpens U β) ↔ ContDiffOn ℝ n β U :=
  isSmoothForm_opens_iff fun _ => rfl

/-- The exterior derivative is the same on both sides of the bridge, at every point of `U` and
with no differentiability hypothesis. -/
theorem mextDeriv_onOpens (U : Opens Space) {k : ℕ} (β : Space → Form k) (x : U) :
    mextDeriv (onOpens U β) x = extDeriv β x :=
  mextDeriv_opens_eq_extDeriv (fun _ => rfl) x

/-- A form is closed on the manifold `U` exactly when it is closed at every point of `U`. -/
theorem mextDeriv_onOpens_eq_zero_iff (U : Opens Space) {k : ℕ} (β : Space → Form k) :
    mextDeriv (onOpens U β) = 0 ↔ ∀ x ∈ U, extDeriv β x = 0 :=
  mextDeriv_opens_eq_zero_iff fun _ => rfl

/-- **Scalar potential on a simply connected region.** On a simply connected open region a
vacuum 2-form satisfies `⋆ω = dφ` for a `C²` function `φ`. -/
theorem VacuumForm.exists_scalarPotential_of_simplyConnected {U : Opens Space}
    [SimplyConnectedSpace U] {ω : Space → Form 2} (h : VacuumForm U ω) :
    ∃ φ : Space → ℝ, ContDiffOn ℝ 2 φ U ∧ ∀ x ∈ U, formGrad φ x = hodge (ω x) := by
  have hreg : ContDiffOn ℝ ((2 : ℕ∞) : WithTop ℕ∞) (fun y => hodge (ω y)) U := by
    have h1 := flux.toContinuousLinearEquiv.symm.contDiff (n := 2) |>.comp_contDiffOn h.contDiffOn
    have h2 := flat.toContinuousLinearEquiv.contDiff (n := 2) |>.comp_contDiffOn h1
    exact_mod_cast h2
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_simplyConnectedSpace (r := 2) (by norm_num)
    ((isSmoothForm_onOpens_iff U _).2 hreg)
    ((mextDeriv_onOpens_eq_zero_iff U _).2 h.coclosed)
  obtain ⟨ψ₀, hψ₀, heq⟩ := hψ.exists_contDiffOn_opens
  let e := ContinuousAlternatingMap.constOfIsEmptyLIE ℝ Space ℝ (Fin 0)
  refine ⟨fun y => e.symm (ψ₀ y), ?_, fun x hx => ?_⟩
  · have := e.symm.contDiff (n := 2) |>.comp_contDiffOn hψ₀
    exact_mod_cast this
  · have h1 : mextDeriv ψ ⟨x, hx⟩ = extDeriv ψ₀ x := mextDeriv_opens_eq_extDeriv heq ⟨x, hx⟩
    have h2 : mextDeriv ψ ⟨x, hx⟩ = hodge (ω x) := by rw [hdψ]; rfl
    rw [← h2, h1, ← extDeriv_formGrad]
    congr 1
    funext y
    exact (e.apply_symm_apply (ψ₀ y))

/-- **Scalar potential on a simply connected region, vector language**: a vacuum field on a
simply connected open region is the gradient of a `C²` function. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.exists_scalarPotential_of_simplyConnected
    {U : Opens Space} [SimplyConnectedSpace U] {B : Space → Space} (h : VacuumField U B) :
    ∃ φ : Space → ℝ, ContDiffOn ℝ 2 φ U ∧ ∀ x ∈ U, B x = gradient φ x := by
  obtain ⟨φ, hφ, hd⟩ := (vacuumForm_flux_iff.2 h).exists_scalarPotential_of_simplyConnected
  refine ⟨φ, hφ, fun x hx => ?_⟩
  have := hd x hx
  rw [← flat_gradient, fluxField_apply, hodge, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] at this
  exact (flat.injective this).symm

/-- **A field without a potential detects topology.** If a vacuum field on the open region `U`
is not the gradient of any function that is differentiable on `U`, then `U` is not simply
connected. -/
theorem not_simplyConnected_of_no_potential {U : Opens Space} {B : Space → Space}
    (h : VacuumField U B)
    (hno : ¬ ∃ φ : Space → ℝ, DifferentiableOn ℝ φ U ∧ ∀ x ∈ U, B x = gradient φ x) :
    ¬ SimplyConnectedSpace U := fun _ =>
  hno (by
    obtain ⟨φ, hφ, hd⟩ := h.exists_scalarPotential_of_simplyConnected
    exact ⟨φ, hφ.differentiableOn (by norm_num), hd⟩)

end PlasmaLean.Forms
