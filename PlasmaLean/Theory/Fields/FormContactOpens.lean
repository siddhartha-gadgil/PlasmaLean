/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormContactManifold
public import PlasmaLean.Theory.Fields.FormTopology

/-!
# The 1-form of a magnetic field as a contact form on an open subset of `ℝ³`

`Theory/Fields/FormContactManifold` links PlasmaLean's pointwise contact condition
`IsContactAt` with TauCeti's contact forms on the manifold `ℝ³`. This file does the same on the
manifold `U`, an open subset of `ℝ³` (`U : TopologicalSpace.Opens Space`), so that the link
applies to fields that are smooth, Beltrami or nonvanishing only on a region. The bridge is
`onOpens` of `Theory/Fields/FormTopology`. The tangent spaces of `U` are `Space` itself.

* `flatSmoothFormOn U B hB`: for a field `B` smooth on `U`, the smooth 1-form `B♭` as a TauCeti
  `SmoothForm` on `U`.
* `isContactFormAt_onOpens_iff`: TauCeti's pointwise condition `IsContactFormAt` for
  `onOpens U β` at `x : U` is `IsContactAt β x`, with no regularity hypothesis.
* `isContactForm_flatSmoothFormOn_iff`: `flatSmoothFormOn U B hB` is a TauCeti contact form
  exactly when `IsContactAt` holds at every point of `U`.
* `IsBeltramiOn.isContactForm_flatSmoothFormOn`: a field that is smooth and Beltrami on `U`,
  with `λ ≠ 0` and `B ≠ 0` on `U`, gives a TauCeti contact form on `U`.
* `IsBeltramiOn.reebVectorField_flatSmoothFormOn`: its TauCeti Reeb vector field is `B / ‖B‖²`.
* `isContactForm_flatSmoothFormOn_top_iff`, `reebVectorField_flatSmoothFormOn_top`: for `U = ⊤`
  and a field smooth on `ℝ³`, the contact condition and the Reeb vector field are those of
  `flatSmoothForm` on `ℝ³`.
* `IsContactForm.flatSmoothFormOn_mono`: a contact form on `U` restricts to a contact form on a
  smaller open set.

Not proved here: nothing is said about the points outside `U`; no statement about the flow of
the Reeb vector field, or about its smoothness as a vector field on `U`; no comparison of the
manifolds `(⊤ : Opens Space)` and `Space` beyond the two lemmas for `U = ⊤` above.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix
open TauCeti TopologicalSpace
open scoped Manifold ContDiff

/-- The smooth 1-form `B♭` of a field `B` that is smooth on the open set `U`, as a TauCeti
smooth form on the manifold `U`. Its value at `x : U` is `flat (B x)`. -/
noncomputable def flatSmoothFormOn (U : Opens Space) (B : Space → Space)
    (hB : ContDiffOn ℝ ∞ B U) : SmoothForm 𝓘(ℝ, Space) U ℝ 1 :=
  ⟨onOpens U fun y => flat (B y),
    ((isSmoothForm_onOpens_iff U _).2
      (flat.toContinuousLinearEquiv.contDiff.comp_contDiffOn hB)).mem_smoothBundleForms⟩

/-- The value of `flatSmoothFormOn U B hB` at `x : U` is `flat (B x)`. -/
theorem flatSmoothFormOn_apply (U : Opens Space) (B : Space → Space) (hB : ContDiffOn ℝ ∞ B U)
    (x : U) : (flatSmoothFormOn U B hB).1 x = flat (B x) := rfl

/-- The underlying rough form of `flatSmoothFormOn U B hB` is the bridge `onOpens` applied to
`fun y => flat (B y)`. -/
theorem flatSmoothFormOn_toRoughForm (U : Opens Space) (B : Space → Space)
    (hB : ContDiffOn ℝ ∞ B U) :
    (flatSmoothFormOn U B hB).1 = onOpens U fun y => flat (B y) := rfl

/-- The manifold exterior derivative of `flatSmoothFormOn U B hB` at `x : U` is the kernel's
`extDeriv` of `B♭` at `x`. -/
theorem mextDeriv_flatSmoothFormOn (U : Opens Space) (B : Space → Space)
    (hB : ContDiffOn ℝ ∞ B U) (x : U) :
    mextDeriv (flatSmoothFormOn U B hB).1 x = extDeriv (fun y => flat (B y)) x :=
  mextDeriv_onOpens U (fun y => flat (B y)) x

/-- **Pointwise link on an open set.** TauCeti's pointwise contact condition for the rough form
`onOpens U β` on the manifold `U`, at `x : U`, is PlasmaLean's `IsContactAt β x`. No regularity
of `β` is needed. -/
theorem isContactFormAt_onOpens_iff (U : Opens Space) (β : Space → Form 1) (x : U) :
    IsContactFormAt (onOpens U β) x ↔ IsContactAt β (x : Space) := by
  rw [isContactAt_iff_nondegenerate]
  have hd : mextDeriv (onOpens U β) x = extDeriv β x := mextDeriv_onOpens U β x
  have hk : ∀ v : Space, v ∈ RoughForm.ker (onOpens U β) x ↔ β x ![v] = 0 := fun v =>
    RoughForm.mem_ker (α := onOpens U β) (x := x) (v := v)
  constructor
  · intro h
    refine ⟨h.ne_zero, fun v hv hvw => ?_⟩
    refine h.nondegenerate v ((hk v).2 hv) fun w hw => ?_
    rw [hd]
    exact hvw w ((hk w).1 hw)
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun v hv hvw => ?_⟩
    refine h v ((hk v).1 hv) fun w hw => ?_
    rw [← hd]
    exact hvw w ((hk w).2 hw)

/-- The pointwise link on an open set for `β = B♭`. -/
theorem isContactFormAt_onOpens_flat_iff (U : Opens Space) (B : Space → Space) (x : U) :
    IsContactFormAt (onOpens U fun y => flat (B y)) x ↔
      IsContactAt (fun y => flat (B y)) (x : Space) :=
  isContactFormAt_onOpens_iff U _ x

/-- **Global link on an open set.** For a field `B` smooth on `U`, the form `B♭` is a TauCeti
contact form on the manifold `U` exactly when PlasmaLean's contact condition `β ∧ dβ ≠ 0` holds
at every point of `U`. -/
theorem isContactForm_flatSmoothFormOn_iff (U : Opens Space) (B : Space → Space)
    (hB : ContDiffOn ℝ ∞ B U) :
    (flatSmoothFormOn U B hB).IsContactForm ↔
      ∀ x ∈ U, IsContactAt (fun y => flat (B y)) x := by
  rw [SmoothForm.isContactForm_iff_forall_isContactFormAt]
  constructor
  · intro h x hx
    exact (isContactFormAt_onOpens_flat_iff U B ⟨x, hx⟩).1 (h ⟨x, hx⟩)
  · intro h x
    exact (isContactFormAt_onOpens_flat_iff U B x).2 (h x x.2)

/-- **Restriction.** If `B♭` is a contact form on `W` and `U ≤ W`, then it is a contact form on
`U`. -/
theorem IsContactForm.flatSmoothFormOn_mono {U W : Opens Space} (hUW : U ≤ W)
    {B : Space → Space} {hB : ContDiffOn ℝ ∞ B W}
    (h : (flatSmoothFormOn W B hB).IsContactForm) :
    (flatSmoothFormOn U B (hB.mono hUW)).IsContactForm :=
  (isContactForm_flatSmoothFormOn_iff U B _).2 fun x hx =>
    (isContactForm_flatSmoothFormOn_iff W B hB).1 h x (hUW hx)

/-- **A field that is smooth and Beltrami on `U`, with `λ ≠ 0` and `B ≠ 0` on `U`, gives a
TauCeti contact form** `B♭` on the manifold `U`. -/
theorem IsBeltramiOn.isContactForm_flatSmoothFormOn {U : Opens Space} {B : Space → Space}
    {lam : Space → ℝ} (h : IsBeltramiOn B lam U) (hB : ContDiffOn ℝ ∞ B U)
    (hl : ∀ x ∈ U, lam x ≠ 0) (hne : ∀ x ∈ U, B x ≠ 0) :
    (flatSmoothFormOn U B hB).IsContactForm :=
  (isContactForm_flatSmoothFormOn_iff U B hB).2 fun x hx =>
    isContactAt_of_beltrami h hx (hl x hx) (hne x hx)

/-- **The TauCeti Reeb vector field of a Beltrami field on `U` is `B / ‖B‖²`.** For a field
that is smooth and Beltrami on `U`, with `λ ≠ 0` and `B ≠ 0` on `U`, the Reeb vector field of
the contact form `B♭` at `x : U` is `(‖B x‖ ^ 2)⁻¹ • B x`. The tangent space of `U` at `x` is
`Space`. -/
theorem IsBeltramiOn.reebVectorField_flatSmoothFormOn {U : Opens Space} {B : Space → Space}
    {lam : Space → ℝ} (h : IsBeltramiOn B lam U) (hB : ContDiffOn ℝ ∞ B U)
    (hl : ∀ x ∈ U, lam x ≠ 0) (hne : ∀ x ∈ U, B x ≠ 0) (x : U) :
    (flatSmoothFormOn U B hB).reebVectorField x = (‖B x‖ ^ 2)⁻¹ • B x := by
  obtain ⟨h1, h2⟩ := h.reeb x.2 (hne x x.2)
  obtain ⟨R, hR⟩ : ∃ R : TangentSpace 𝓘(ℝ, Space) x, R = (‖B x‖ ^ 2)⁻¹ • B x := ⟨_, rfl⟩
  have key := (h.isContactForm_flatSmoothFormOn hB hl hne).eq_reebVectorField_iff
    (x := x) (v := R)
  rw [← hR]
  refine (key.2 ⟨?_, fun w => ?_⟩).symm
  · rw [flatSmoothFormOn_apply, hR]
    exact h1
  · rw [mextDeriv_flatSmoothFormOn, hR]
    exact congrArg (fun a : Form 1 => a ![w]) h2

/-! ## Consistency with the statements on all of `ℝ³` -/

/-- **Consistency for `U = ⊤`.** For a field smooth on `ℝ³`, the form on the manifold
`(⊤ : Opens Space)` is a contact form exactly when `flatSmoothForm B hB` is a contact form on
the manifold `ℝ³`. -/
theorem isContactForm_flatSmoothFormOn_top_iff (B : Space → Space) (hB : ContDiff ℝ ∞ B) :
    (flatSmoothFormOn ⊤ B hB.contDiffOn).IsContactForm ↔ (flatSmoothForm B hB).IsContactForm := by
  rw [isContactForm_flatSmoothFormOn_iff, isContactForm_flatSmoothForm_iff]
  exact ⟨fun h x => h x trivial, fun h x _ => h x⟩

/-- The values of the two forms agree: at `x : (⊤ : Opens Space)` both are `flat (B x)`. -/
theorem flatSmoothFormOn_top_apply (B : Space → Space) (hB : ContDiff ℝ ∞ B)
    (x : (⊤ : Opens Space)) :
    (flatSmoothFormOn ⊤ B hB.contDiffOn).1 x = (flatSmoothForm B hB).1 (x : Space) := rfl

/-- **Consistency of the Reeb vector fields for `U = ⊤`.** For a contact form `B♭` of a field
smooth on `ℝ³`, the Reeb vector field on the manifold `(⊤ : Opens Space)` at `x` is the Reeb
vector field on the manifold `ℝ³` at `x`. -/
theorem reebVectorField_flatSmoothFormOn_top (B : Space → Space) (hB : ContDiff ℝ ∞ B)
    (h : (flatSmoothForm B hB).IsContactForm) (x : (⊤ : Opens Space)) :
    (flatSmoothFormOn ⊤ B hB.contDiffOn).reebVectorField x =
      (flatSmoothForm B hB).reebVectorField (x : Space) := by
  obtain ⟨R, hR⟩ : ∃ R : TangentSpace 𝓘(ℝ, Space) x,
    R = (flatSmoothForm B hB).reebVectorField (x : Space) := ⟨_, rfl⟩
  have key := ((isContactForm_flatSmoothFormOn_top_iff B hB).2 h).eq_reebVectorField_iff
    (x := x) (v := R)
  obtain ⟨h1, h2⟩ := h.eq_reebVectorField_iff.1
    (rfl : (flatSmoothForm B hB).reebVectorField (x : Space) = _)
  rw [← hR]
  refine (key.2 ⟨?_, fun w => ?_⟩).symm
  · rw [flatSmoothFormOn_apply, hR]
    exact h1
  · have := h2 w
    rw [mextDeriv_flatSmoothForm] at this
    rw [mextDeriv_flatSmoothFormOn, hR]
    exact this

end PlasmaLean.Forms
