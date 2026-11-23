/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormContact
public import TauCeti.Geometry.Contact.Reeb

/-!
# The 1-form of a magnetic field as a contact form on the manifold `ℝ³` (TauCeti v4.36.0)

`Theory/Fields/FormContact` states the contact condition for `β = B♭` pointwise, with
PlasmaLean's predicate `IsContactAt`. TauCeti has contact forms on manifolds
(`TauCeti.SmoothForm.IsContactForm`) and their Reeb vector fields
(`TauCeti.SmoothForm.reebVectorField`). This file links the two on the manifold `ℝ³`, modelled
on itself.

* `flatSmoothForm B hB`: for a smooth field `B`, the smooth 1-form `B♭` as a TauCeti
  `SmoothForm` on `ℝ³`.
* `isContactFormAt_flat_iff`: TauCeti's pointwise condition `IsContactFormAt` for `B♭` is
  `IsContactAt`, with no regularity hypothesis.
* `isContactForm_flatSmoothForm_iff`: `flatSmoothForm B hB` is a TauCeti contact form exactly
  when `IsContactAt` holds at every point.
* `IsBeltramiOn.isContactForm_flatSmoothForm`: a smooth Beltrami field with `λ ≠ 0` and `B ≠ 0`
  everywhere gives a TauCeti contact form.
* `IsBeltramiOn.reebVectorField_flatSmoothForm`: its TauCeti Reeb vector field is `B / ‖B‖²`.

Not proved here: the same statements on an open subset `U` of `ℝ³` (the manifold
`TopologicalSpace.Opens Space`). Everything is stated on all of `ℝ³`.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix
open TauCeti
open scoped Manifold ContDiff

/-- The smooth 1-form `B♭` of a smooth field `B` on `ℝ³`, as a TauCeti smooth form on the
manifold `ℝ³` (modelled on itself). Its value at `x` is `flat (B x)`. -/
noncomputable def flatSmoothForm (B : Space → Space) (hB : ContDiff ℝ ∞ B) :
    SmoothForm 𝓘(ℝ, Space) Space ℝ 1 :=
  ⟨fun x => flat (B x),
    (isSmoothForm_modelSpace_iff.2
      (flat.toContinuousLinearEquiv.contDiff.comp hB)).mem_smoothBundleForms⟩

/-- The value of `flatSmoothForm B hB` at `x` is `flat (B x)`. -/
theorem flatSmoothForm_apply (B : Space → Space) (hB : ContDiff ℝ ∞ B) (x : Space) :
    (flatSmoothForm B hB).1 x = flat (B x) := rfl

/-- The underlying rough form of `flatSmoothForm B hB` is `fun x => flat (B x)`. -/
theorem flatSmoothForm_toRoughForm (B : Space → Space) (hB : ContDiff ℝ ∞ B) :
    (flatSmoothForm B hB).1 = fun x => flat (B x) := rfl

/-- The manifold exterior derivative of `flatSmoothForm B hB` is the kernel's `extDeriv` of
`B♭`. -/
theorem mextDeriv_flatSmoothForm (B : Space → Space) (hB : ContDiff ℝ ∞ B) (x : Space) :
    mextDeriv (flatSmoothForm B hB).1 x = extDeriv (fun y => flat (B y)) x :=
  mextDeriv_eq_extDeriv _ x

/-- **Pointwise link.** TauCeti's pointwise contact condition for the rough form `β` on the
manifold `ℝ³` is PlasmaLean's `IsContactAt`. No regularity of `β` is needed. -/
theorem isContactFormAt_iff_isContactAt (β : Space → Form 1) (x : Space) :
    IsContactFormAt (I := 𝓘(ℝ, Space)) (M := Space) β x ↔ IsContactAt β x := by
  rw [isContactAt_iff_nondegenerate]
  have hd : mextDeriv (I := 𝓘(ℝ, Space)) (M := Space) β x = extDeriv β x :=
    mextDeriv_eq_extDeriv _ x
  constructor
  · intro h
    refine ⟨h.ne_zero, fun v hv hvw => ?_⟩
    refine h.nondegenerate v (RoughForm.mem_ker.2 hv) fun w hw => ?_
    rw [hd]
    exact hvw w (RoughForm.mem_ker.1 hw)
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun v hv hvw => ?_⟩
    refine h v (RoughForm.mem_ker.1 hv) fun w hw => ?_
    rw [← hd]
    exact hvw w (RoughForm.mem_ker.2 hw)

/-- The pointwise link for `β = B♭`. -/
theorem isContactFormAt_flat_iff (B : Space → Space) (x : Space) :
    IsContactFormAt (I := 𝓘(ℝ, Space)) (M := Space) (fun y => flat (B y)) x ↔
      IsContactAt (fun y => flat (B y)) x :=
  isContactFormAt_iff_isContactAt _ x

/-- **Global link.** For a smooth field `B`, the form `B♭` is a TauCeti contact form on `ℝ³`
exactly when PlasmaLean's contact condition `β ∧ dβ ≠ 0` holds at every point. -/
theorem isContactForm_flatSmoothForm_iff (B : Space → Space) (hB : ContDiff ℝ ∞ B) :
    (flatSmoothForm B hB).IsContactForm ↔ ∀ x, IsContactAt (fun y => flat (B y)) x := by
  rw [SmoothForm.isContactForm_iff_forall_isContactFormAt]
  exact forall_congr' fun x => isContactFormAt_flat_iff B x

/-- **A smooth Beltrami field with `λ ≠ 0` and `B ≠ 0` everywhere gives a TauCeti contact
form** `B♭` on `ℝ³`. -/
theorem IsBeltramiOn.isContactForm_flatSmoothForm {B : Space → Space} {lam : Space → ℝ}
    (h : IsBeltramiOn B lam Set.univ) (hB : ContDiff ℝ ∞ B) (hl : ∀ x, lam x ≠ 0)
    (hne : ∀ x, B x ≠ 0) : (flatSmoothForm B hB).IsContactForm :=
  (isContactForm_flatSmoothForm_iff B hB).2 fun x =>
    isContactAt_of_beltrami h (Set.mem_univ x) (hl x) (hne x)

/-- **The TauCeti Reeb vector field of a Beltrami field is `B / ‖B‖²`.** For a smooth Beltrami
field with `λ ≠ 0` and `B ≠ 0` everywhere, the Reeb vector field of the contact form `B♭` at
`x` is `(‖B x‖ ^ 2)⁻¹ • B x`. -/
theorem IsBeltramiOn.reebVectorField_flatSmoothForm {B : Space → Space} {lam : Space → ℝ}
    (h : IsBeltramiOn B lam Set.univ) (hB : ContDiff ℝ ∞ B) (hl : ∀ x, lam x ≠ 0)
    (hne : ∀ x, B x ≠ 0) (x : Space) :
    (flatSmoothForm B hB).reebVectorField x = (‖B x‖ ^ 2)⁻¹ • B x := by
  obtain ⟨h1, h2⟩ := h.reeb (Set.mem_univ x) (hne x)
  obtain ⟨R, hR⟩ : ∃ R : TangentSpace 𝓘(ℝ, Space) x, R = (‖B x‖ ^ 2)⁻¹ • B x := ⟨_, rfl⟩
  have key := (h.isContactForm_flatSmoothForm hB hl hne).eq_reebVectorField_iff
    (x := x) (v := R)
  rw [← hR]
  refine (key.2 ⟨?_, fun w => ?_⟩).symm
  · rw [flatSmoothForm_apply, hR]
    exact h1
  · rw [mextDeriv_flatSmoothForm, hR]
    exact congrArg (fun a : Form 1 => a ![w]) h2

end PlasmaLean.Forms
