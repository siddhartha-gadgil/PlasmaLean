/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Common-witness certificate composition

This logical interface indexes every property by the same design, operating state,
and equilibrium witness. The predicates must be instantiated with actual models;
constructing the interface proves no physics. Existence is inside the uncertainty
quantifier. Distinct witness proofs may be composed only with a uniqueness bridge.
-/
public section

namespace PlasmaLean.Bridge

/-- Separate contracts sharing candidate, operating parameter, and equilibrium types. -/
structure DesignContracts (D Θ E : Type*) where
  equilibrium : D → Θ → E → Prop
  stability : D → Θ → E → Prop
  transport : D → Θ → E → Prop
  components : D → Θ → E → Prop

/-- A robust certificate carries one common witness per admissible operating state. -/
@[expose] def RobustDesign {D Θ E : Type*} (C : DesignContracts D Θ E) (d : D) (U : Set Θ) : Prop :=
  ∀ θ ∈ U, ∃ e, C.equilibrium d θ e ∧ C.stability d θ e ∧
    C.transport d θ e ∧ C.components d θ e

/-- A supplied branch satisfying all contracts yields a robust certificate. -/
theorem compose_branch {D Θ E : Type*} (C : DesignContracts D Θ E)
    (d : D) (U : Set Θ) (branch : Θ → E)
    (he : ∀ θ ∈ U, C.equilibrium d θ (branch θ))
    (hs : ∀ θ ∈ U, C.stability d θ (branch θ))
    (ht : ∀ θ ∈ U, C.transport d θ (branch θ))
    (hc : ∀ θ ∈ U, C.components d θ (branch θ)) : RobustDesign C d U := by
  intro θ hθ
  exact ⟨branch θ, he θ hθ, hs θ hθ, ht θ hθ, hc θ hθ⟩

/-- A robust certificate restricts to a smaller uncertainty set. -/
theorem robust_mono {D Θ E : Type*} {C : DesignContracts D Θ E} {d : D}
    {U V : Set Θ} (h : RobustDesign C d U) (hv : V ⊆ U) : RobustDesign C d V := by
  intro θ hθ; exact h θ (hv hθ)

/-- Uniqueness is a sufficient bridge for independently obtained equilibrium witnesses. -/
theorem compose_of_unique {E : Type*} (equilibrium stable transported : E → Prop)
    (unique : ∀ a b, equilibrium a → equilibrium b → a = b)
    (hs : ∃ a, equilibrium a ∧ stable a)
    (ht : ∃ b, equilibrium b ∧ transported b) :
    ∃ a, equilibrium a ∧ stable a ∧ transported a := by
  obtain ⟨a, ha, hsa⟩ := hs
  obtain ⟨b, hb, htb⟩ := ht
  have hab := unique a b ha hb
  subst b
  exact ⟨a, ha, hsa, htb⟩

/-- Separate existence claims need not have a common witness. -/
theorem incompatible_witnesses :
    (∃ b : Bool, b = true) ∧ (∃ b : Bool, b = false) ∧
    ¬ (∃ b : Bool, b = true ∧ b = false) := by
  refine ⟨⟨true, rfl⟩, ⟨false, rfl⟩, ?_⟩
  rintro ⟨b, rfl, h⟩
  cases h

end PlasmaLean.Bridge
