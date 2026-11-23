/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormContact

/-!
# Sanity checks for `Theory/Fields/FormContact`

* Accepted: for the helical Beltrami field `(cos z, sin z, 0)`, TauCeti's wedge `β ∧ dβ` is
  nonzero (`helical_wedge_ne_zero`), `dβ` is nondegenerate on `ker β`
  (`helical_nondegenerate`), and the Reeb equations hold for `B/‖B‖²` (`helical_reeb`).
* Rejected: a constant 1-form fails the intrinsic contact condition
  (`const_not_nondegenerate`), and its wedge `β ∧ dβ` is zero (`const_wedge_eq_zero`).
* Regression (audit AV-L), hypothesis check: `IsBeltramiOn.reeb_unique` needs `λ(x) ≠ 0`. The
  constant field `e_x` is a Beltrami field with `λ = 0` (`const_beltrami`), and
  `R = e_x + e_y` satisfies both Reeb equations without being `B/‖B‖²`
  (`reeb_not_unique_of_lam_zero`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormContact

open PlasmaLean PlasmaLean.Forms PlasmaLean.Vacuum PlasmaLean.Fields

/-- Accepted: `β ∧ dβ ≠ 0` for the helical field, with TauCeti's wedge product. -/
theorem helical_wedge_ne_zero (x : Space) :
    (ContinuousAlternatingMap.wedge (flat (helicalField x))
      (extDeriv (fun y => flat (helicalField y)) x) : Form 3) ≠ 0 :=
  (isContactAt_iff_wedge _ x).1 (helicalField_contact x)

/-- Accepted: the helical 1-form satisfies the intrinsic contact condition. -/
theorem helical_nondegenerate (x : Space) :
    flat (helicalField x) ≠ 0 ∧ ∀ v, flat (helicalField x) ![v] = 0 →
      (∀ w, flat (helicalField x) ![w] = 0 →
        extDeriv (fun y => flat (helicalField y)) x ![v, w] = 0) → v = 0 :=
  (isContactAt_iff_nondegenerate _ x).1 (helicalField_contact x)

/-- Accepted: the Reeb equations for the helical field. -/
theorem helical_reeb (x : Space) :
    flat (helicalField x) ![(‖helicalField x‖ ^ 2)⁻¹ • helicalField x] = 1 ∧
      (extDeriv (fun y => flat (helicalField y)) x).curryLeft
        ((‖helicalField x‖ ^ 2)⁻¹ • helicalField x) = 0 :=
  helicalField_beltrami.reeb (Set.mem_univ x) (helicalField_ne_zero x)

/-- Rejected: a constant 1-form does not satisfy the intrinsic contact condition. -/
theorem const_not_nondegenerate (B₀ x : Space) :
    ¬ (flat B₀ ≠ 0 ∧ ∀ v, flat B₀ ![v] = 0 →
      (∀ w, flat B₀ ![w] = 0 → extDeriv (fun _ : Space => flat B₀) x ![v, w] = 0) → v = 0) :=
  fun h => const_not_contact B₀ x ((isContactAt_iff_nondegenerate (fun _ => flat B₀) x).2 h)

/-- Rejected: `β ∧ dβ = 0` for a constant 1-form, with TauCeti's wedge product. -/
theorem const_wedge_eq_zero (B₀ x : Space) :
    (ContinuousAlternatingMap.wedge (flat B₀) (extDeriv (fun _ : Space => flat B₀) x) : Form 3)
      = 0 := by
  by_contra h
  exact const_not_contact B₀ x ((isContactAt_iff_wedge (fun _ => flat B₀) x).2 h)

/-- Regression (audit AV-L): **the hypothesis `λ(x) ≠ 0` of `IsBeltramiOn.reeb_unique` is
needed.** For the constant field `B = e_x`, a Beltrami field with `λ = 0`
(`const_beltrami`, first conjunct) and `B ≠ 0`, the vector `R = e_x + e_y` satisfies both
Reeb equations `β(R) = 1` and `ι_R dβ = 0` (here `dβ = 0`), and `R ≠ B/‖B‖²`. So without
`λ ≠ 0` the Reeb equations do not determine `R`; the form `B♭` is then not a contact form. -/
theorem reeb_not_unique_of_lam_zero (x : Space) :
    IsBeltramiOn (fun _ : Space => coordVec 0) (fun _ => 0) Set.univ ∧
      flat (coordVec 0) ![coordVec 0 + coordVec 1] = 1 ∧
      (extDeriv (fun _ : Space => flat (coordVec 0)) x).curryLeft
        (coordVec 0 + coordVec 1) = 0 ∧
      coordVec 0 + coordVec 1 ≠ (‖(coordVec 0 : Space)‖ ^ 2)⁻¹ • (coordVec 0 : Space) := by
  refine ⟨const_beltrami _ _, ?_, ?_, fun h => ?_⟩
  · simp [flat_apply, inner_coords3]
  · have h : extDeriv (fun _ : Space => flat (coordVec 0)) x = 0 := by
      simp
    rw [h]
    simp
  · have := congrArg (fun v : Space => v 1) h
    simp at this

end PlasmaLean.Sanity.FormContact
