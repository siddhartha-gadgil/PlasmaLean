/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.Forms
public import PlasmaLean.Theory.Fields.FormBridges

/-!
# Strict-audit checks for `Kernel/Forms` and `Theory/Fields/FormBridges`

Audit of 16 November 2026 (record `notes/audit/2026-11-16-forms-audit.md`, findings `AD-*`).
The sanity checks of `Sanity/Forms` are transported through the dictionary theorems
(`vacuumForm_flux_iff`, `formForceBalance_iff`), so they cannot detect a convention error
shared by the equivalences and the dictionary. This module adds:

1. **Checks that do not use the dictionary** (finding AD-M2). `extDeriv_x_dy`: Mathlib's
   exterior derivative of `x dy`, computed from `extDeriv_apply`, is `1` on `(e₀, e₁)`.
   `interior_pinch_direct`: the pinch sign by a determinant. `div_curl_eq_zero`: `d ∘ d = 0`
   (Mathlib) read through both dictionary theorems gives `∇ · (∇ × B) = 0`, a cross-check of
   `extDeriv_flat` against `extDeriv_flux`. `wedge_eq_inner_hodge`: `a ∧ b = ⟪a, ⋆b⟫ vol`,
   an independent characterisation of the Hodge star.
2. **Totalized derivatives** (AD-M1, AD-M3). The kink field of `Sanity/AuditVacuum` has
   `dω = 0` and `d⋆ω = 0` at the kink but is not a vacuum form there; it satisfies the
   Beltrami curl equation with `λ = 0` at the kink but is not `IsBeltramiOn`.
3. **Vacuity regressions** (AD-M1, AD-M4, AD-M5). The zero field is Beltrami for every `λ`;
   `B = x` is Beltrami with `λ = 0` but `∇ · B = 3`; `FormSymmetricFlux ω (-ι_K ω) K` always
   holds; the zero form is weakly quasisymmetric for a constant generator.
4. **Missing triad members** (AD-M5, AD-M6). Accepted and rejected fixtures for
   `FormSymmetricFlux`, `FormFirstIntegralOn`, `FormWeakQS` (the mirror field) and
   `IsContactAt` (the rotation field: nonzero curl, not contact; the helical form has
   `β ∧ dβ = -vol`, a negative contact form).
-/

open scoped RealInnerProductSpace
open InnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Sanity.AuditForms

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
  PlasmaLean.Sanity.Audit PlasmaLean.Sanity.Forms Matrix

/-! ### Checks that do not go through the dictionary (AD-M2) -/

/-- **`d(x dy) = dx ∧ dy`**, computed from Mathlib's formula `extDeriv_apply` and not from
`extDeriv_flat`: the value on `(e₀, e₁)` is `1`. This fixes the normalization (no factor
`1/2`) and the sign of the exterior derivative used by the dictionary. -/
theorem extDeriv_x_dy (x : Euclid3) :
    extDeriv (fun y : Euclid3 => flat ((y 0) • coordVec 1)) x ![coordVec 0, coordVec 1] = 1 := by
  have p : HasFDerivAt (fun y : Euclid3 => y 0)
      (EuclideanSpace.proj (0 : Fin 3) : Euclid3 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (0 : Fin 3) : Euclid3 →L[ℝ] ℝ).hasFDerivAt
  have hB : HasFDerivAt (fun y : Euclid3 => (y 0) • coordVec 1)
      ((EuclideanSpace.proj (0 : Fin 3) : Euclid3 →L[ℝ] ℝ).smulRight (coordVec 1)) x :=
    p.smul_const _
  have hd : DifferentiableAt ℝ (fun y : Euclid3 => flat ((y 0) • coordVec 1)) x :=
    flat.toContinuousLinearEquiv.comp_differentiableAt_iff.2 hB.differentiableAt
  have e0 : Fin.removeNth (0 : Fin 2) ![coordVec 0, coordVec 1] = ![coordVec 1] := by
    ext i; fin_cases i; rfl
  have e1 : Fin.removeNth (1 : Fin 2) ![coordVec 0, coordVec 1] = ![coordVec 0] := by
    ext i; fin_cases i; rfl
  have a : (fun y : Euclid3 => flat ((y 0) • coordVec 1) ![coordVec 1]) = fun y => y 0 := by
    funext y; simp [coordVec]
  have b : (fun y : Euclid3 => flat ((y 0) • coordVec 1) ![coordVec 0]) = fun _ => 0 := by
    funext y; simp [coordVec, EuclideanSpace.inner_single_left]
  rw [extDeriv_apply hd, Fin.sum_univ_two, e0, e1, a, b, p.fderiv]
  simp [coordVec]

/-- The same form through the dictionary: `x dy = B♭` for `B = (0, x, 0)`, whose curl is
`e_z`, and `flux e_z (e₀, e₁) = 1`. Agreement with `extDeriv_x_dy` is the consistency check. -/
theorem flux_coordVec_two : flux (coordVec 2) ![coordVec 0, coordVec 1] = 1 := by
  simp [flux_apply, volForm_vec]

/-- The remaining basis value of the flux form: `ι_{e₁} vol = dz ∧ dx`. -/
theorem flux_coordVec_one : flux (coordVec 1) ![coordVec 2, coordVec 0] = 1 := by
  simp [flux_apply, volForm_vec]

/-- **Pinch sign by a determinant**, without `curryLeft_flux`: for `ω_J = dx ∧ dy` and
`B = e_y`, `(ι_B ω_J)(e_x) = vol(e_z, e_y, e_x) = -1`, the inward pressure gradient. -/
theorem interior_pinch_direct :
    (flux (coordVec 2)).curryLeft (coordVec 1) ![coordVec 0] = -1 := by
  simp [flux_cons, volForm_vec]

/-- **`∇ · (∇ × B) = 0` from `d ∘ d = 0`.** Mathlib's `extDeriv_extDeriv` read through
`extDeriv_flat` and then `extDeriv_flux`. If the two dictionary theorems used inconsistent
conventions this would not typecheck as a proof. -/
theorem div_curl_eq_zero {B : Euclid3 → Euclid3} (hB : ContDiff ℝ 2 B) (x : Euclid3) :
    fieldDiv (fun y => fieldCurl B y) x = 0 := by
  have hβ : ContDiff ℝ 2 (fun y => flat (B y)) :=
    flat.toContinuousLinearEquiv.contDiff.comp hB
  have h := congrFun (extDeriv_extDeriv hβ (by simp)) x
  have e : extDeriv (fun y => flat (B y)) = fun y => flux (fieldCurl B y) :=
    funext fun y => extDeriv_flat B y
  rw [e, extDeriv_flux] at h
  simpa using h

/-- **`a ∧ b = ⟪a, ⋆b⟫ vol`**: the alternating product of a 1-form and a 2-form equals the
inner product of `a` with the Hodge star of `b`, times the volume form. This characterises
`hodge` independently of its definition through `flux` and `flat`. -/
theorem wedge_eq_inner_hodge (a : Form 1) (b : Form 2) (u v w : Euclid3) :
    a ![u] * b ![v, w] - a ![v] * b ![u, w] + a ![w] * b ![u, v] =
      ⟪flat.symm a, flat.symm (hodge b)⟫ * volForm ![u, v, w] := by
  rw [← wedge12_apply, wedge12, density_apply]
  simp [hodge]

/-- A concrete value of the wedge product: `dx ∧ (dy ∧ dz) = vol`. -/
theorem wedge12_dx_dydz :
    wedge12 (flat (coordVec 0)) (flux (coordVec 0)) ![coordVec 0, coordVec 1, coordVec 2] = 1 := by
  rw [wedge12_flat_flux, density_apply]
  simp [volForm_vec, coordVec]

/-- A wedge product that vanishes: `dx ∧ (dz ∧ dx) = 0`. -/
theorem wedge12_dx_dzdx : wedge12 (flat (coordVec 0)) (flux (coordVec 1)) = 0 := by
  rw [wedge12_flat_flux]
  simp [coordVec, EuclideanSpace.inner_single_left]

/-! ### Totalized derivatives (AD-M1, AD-M3) -/

/-- **Totalization hazard in form language.** At the kink of `absField`, both `dω` and `d⋆ω`
vanish by Lean's convention for `fderiv`. -/
theorem absField_form_closed_coclosed :
    extDeriv (fluxField absField) 0 = 0 ∧
      extDeriv (fun y => hodge (fluxField absField y)) 0 = 0 := by
  constructor
  · rw [show fluxField absField = fun y => flux (absField y) from rfl, extDeriv_flux,
      absField_fieldDiv_zero, map_zero]
  · simp only [fluxField_apply, hodge_flux]
    rw [extDeriv_flat, absField_fieldCurl_zero, map_zero]

/-- The regularity field of `VacuumForm` excludes the kink form on any region containing the
kink (transported from `absField_not_vacuum`). -/
theorem absField_not_vacuumForm {Ω : Set Euclid3} (h0 : (0 : Euclid3) ∈ Ω) :
    ¬ VacuumForm Ω (fluxField absField) :=
  fun h => absField_not_vacuum h0 (vacuumForm_flux_iff.1 h)

/-- **Regression (AD-M1).** At the kink, `absField` satisfies the Beltrami curl equation with
`λ = 0`, by totalization. -/
theorem absField_curl_equation : fieldCurl absField 0 = (0 : ℝ) • absField 0 := by
  rw [absField_fieldCurl_zero, zero_smul]

/-- **Regression (AD-M1).** The differentiability clause of `IsBeltramiOn` excludes it. -/
theorem absField_not_beltrami : ¬ IsBeltramiOn absField (fun _ => 0) {0} := fun h =>
  absField_not_differentiableAt (h 0 rfl).1

/-- A function that is not differentiable at `x` is not a first integral there, whatever the
field (the differentiability clause of `FormFirstIntegralOn` has content). -/
theorem not_formFirstIntegralOn_of_not_differentiableAt {ω : Space → Form 2} {ψ : Space → ℝ}
    {x : Space} (h : ¬ DifferentiableAt ℝ ψ x) : ¬ FormFirstIntegralOn ω ψ {x} := fun hf =>
  h (hf x rfl).1

/-! ### Beltrami: vacuity and scope (AD-M1) -/

/-- **Vacuity regression.** The zero field is Beltrami for every `λ` on every set. -/
theorem zero_beltrami (lam : Space → ℝ) (U : Set Space) :
    IsBeltramiOn (fun _ => (0 : Space)) lam U := by
  intro x _
  refine ⟨differentiableAt_const _, ?_⟩
  have : fderiv ℝ (fun _ : Space => (0 : Space)) x = 0 := fderiv_const_apply 0
  rw [fieldCurl, this, smul_zero, curlOp_eq_zero_iff]
  simp

/-- **Scope regression.** `IsBeltramiOn` does not include `∇ · B = 0`: the field `B = x` is
Beltrami with `λ = 0` on all of space and has divergence `3`, so it is not a magnetic
field. -/
theorem id_beltrami_not_solenoidal :
    IsBeltramiOn (fun y : Space => y) (fun _ => 0) Set.univ ∧
      ∀ x, fieldDiv (fun y : Euclid3 => y) x = 3 := by
  refine ⟨fun x _ => ⟨differentiableAt_id, ?_⟩, fieldDiv_id⟩
  rw [fieldCurl_id]
  simp

/-- The helical field is a force-free magnetic field in the full sense: Beltrami and
divergence free. -/
theorem helicalField_div (x : Space) : fieldDiv helicalField x = 0 := by
  simp [fieldDiv, divOp, helicalField_fderiv_apply, coordVec, Fin.sum_univ_three]

/-- The helical field satisfies the kernel force balance with zero pressure differential
(through `IsBeltramiOn.formForceBalance`). -/
theorem helicalField_forceFree (x : Space) :
    FormForceBalance (flux (helicalField x)) (flux (fieldCurl helicalField x)) 0 :=
  helicalField_beltrami.formForceBalance (Set.mem_univ x)

/-! ### Contact condition (AD-M6) -/

/-- **The helical form is a negative contact form**: `β ∧ dβ = -vol`. -/
theorem helicalField_wedge (x : Space) :
    wedge12 (flat (helicalField x)) (extDeriv (fun y => flat (helicalField y)) x) =
      density (-1) := by
  rw [wedge12_flat_extDeriv, helicalField_curl, inner_smul_right, inner_coords3]
  congr 1
  have := Real.sin_sq_add_cos_sq (x 2)
  simp [helicalField]
  nlinarith

/-- **Rejected fixture with nonzero curl**: for the rotation field `(-y, x, 0)`,
`β = -y dx + x dy` has `dβ = 2 dx ∧ dy ≠ 0` but `β ∧ dβ = 0`. It is not a contact form
anywhere (its kernel is the integrable plane field containing `e_z` and the radial
direction). -/
theorem rotationField_not_contact (x : Space) :
    ¬ IsContactAt (fun y => flat (rotationField y)) x := by
  rw [isContactAt_flat_iff, fieldCurl_rotationField, inner_smul_right, inner_coords3]
  obtain ⟨-, -, h2⟩ := rotationField_coords x
  simp [h2, basis]

/-! ### Force balance (AD-L3) -/

/-- Both tangencies for generic data: under `FormForceBalance`, `dp(B) = 0` and
`dp(J) = 0`. -/
theorem form_tangencies (ωB ωJ : Form 2) (dp : Form 1) [FormForceBalance ωB ωJ dp] :
    dp ![flux.symm ωB] = 0 ∧ dp ![flux.symm ωJ] = 0 :=
  ⟨form_field_tangency ωB ωJ dp, form_current_tangency ωB ωJ dp⟩

/-- Vanishing pressure differential does not force vanishing current, even for a nonzero
field (form version of `force_free_nonvacuum`). -/
theorem form_force_free_nonvacuum :
    ∃ ωB ωJ : Form 2, FormForceBalance ωB ωJ 0 ∧ ωB ≠ 0 ∧ ωJ ≠ 0 := by
  have hne : flux (coordVec 0) ≠ 0 := fun h => by
    have := congrArg (fun ω : Form 2 => ω ![coordVec 1, coordVec 2]) h
    simp [flux_apply, volForm_vec] at this
  exact ⟨_, _, parallelFormBalance (flux (coordVec 0)), hne, hne⟩

/-! ### Symmetric flux (AD-M4) -/

/-- **Regression (vacuity hazard, as E-1).** Every flux form and every field `K` satisfy
`FormSymmetricFlux` with the datum `γ := -ι_K ω`. The law has content only when `γ` is
separately the differential of a function. -/
theorem formSymmetricFlux_of_interior (ω : Space → Form 2) (K : Space → Space) :
    FormSymmetricFlux ω (fun x => -(ω x).curryLeft (K x)) K := by
  intro x
  simp

/-- Degenerate case: the zero generator with zero datum. -/
theorem formSymmetricFlux_zero (ω : Space → Form 2) :
    FormSymmetricFlux ω (fun _ => 0) (fun _ => 0) := by
  intro x
  simp

/-- Concrete instance: the uniform field `e_z` (flux form `dx ∧ dy`) is symmetric under
translation along `e_x`, with `ψ = -y`: `ι_{e_x}(dx ∧ dy) = dy = -d(-y)`. -/
theorem formSymmetricFlux_uniform :
    FormSymmetricFlux (fluxField fun _ => basis 2) (fun _ => flat (-basis 1))
      (fun _ => basis 0) := by
  intro x
  rw [fluxField_apply, curryLeft_flux_cross, ← map_neg, neg_neg]
  congr 1
  apply space_ext <;> simp [cross, cross_apply, basis]

/-- Counterexample: the same field and generator with the datum `dx` are rejected. -/
theorem not_formSymmetricFlux_uniform :
    ¬ FormSymmetricFlux (fluxField fun _ => basis 2) (fun _ => flat (basis 0))
      (fun _ => basis 0) := by
  intro h
  have hx := h 0
  rw [fluxField_apply, curryLeft_flux_cross, ← map_neg] at hx
  have h1 := congrArg (fun v : Space => v 1) (flat.injective hx)
  simp [cross, cross_apply, basis] at h1

/-! ### First integrals and weak quasisymmetry (AD-M5) -/

/-- Degenerate case: a constant is a first integral of every flux form. -/
theorem formFirstIntegralOn_const (ω : Space → Form 2) (k : ℝ) (U : Set Space) :
    FormFirstIntegralOn ω (fun _ => k) U := by
  intro x _
  refine ⟨differentiableAt_const _, ?_⟩
  have : fderiv ℝ (fun _ : Space => k) x = 0 := fderiv_const_apply k
  simp [formGrad_apply, this]

/-- Counterexample: `x` is not a first integral of the uniform field `e_x`
(`dx(e_x) = 1`). -/
theorem not_formFirstIntegralOn_x (x : Space) :
    ¬ FormFirstIntegralOn (fluxField fun _ => basis 0) (fun y => y 0) {x} := by
  intro h
  have h1 := (h x rfl).2
  have p : HasFDerivAt (fun y : Space => y 0)
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  rw [formGrad_apply, p.fderiv] at h1
  simp [basis] at h1

/-- **Vacuity regression.** The zero flux form is weakly quasisymmetric on all of space for
a constant generator and `ψ = 0` (as the zero field is for `WeakQS`). -/
theorem formWeakQS_zero :
    FormWeakQS (fun _ => (0 : Form 2)) (fun _ => basis 0) (fun _ => 0) Set.univ := by
  refine ⟨fun x _ => by simp, fun x _ => by simp, fun x _ => by simp, fun x _ => ?_,
    fun x _ => ?_, fun x _ => ?_, fun x _ => ?_⟩
  · intro h
    have := congrArg (fun v : Space => v 0) h
    simp [basis] at this
  · rw [extDeriv_flux]
    have : fderiv ℝ (fun _ : Space => (basis 0 : Space)) x = 0 := fderiv_const_apply _
    simp [fieldDiv, this, divOp]
  · ext w
    have : fderiv ℝ (fun _ : Space => (0 : ℝ)) x = 0 := fderiv_const_apply _
    simp [formGrad, this]
  · simp [formGrad]

/-- **Rejected fixture** (transported from `not_weakQS_mirror`): the flux form of the mirror
field `(1 + x²) e_x` is not weakly quasisymmetric, for any generator and potential, on any
set containing the `x`-axis on which `dψ = 0`. -/
theorem not_formWeakQS_mirror {ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space}
    (hT : ∀ t, xAxis t ∈ T) (hψ : ∀ t, formGrad ψ (xAxis t) = 0) :
    ¬ FormWeakQS (fluxField mirrorField) ξ ψ T := fun h =>
  not_weakQS_mirror hT
    (fun t => by rw [← flat_symm_formGrad, hψ t, map_zero]) (formWeakQS_flux_iff.1 h)

end PlasmaLean.Sanity.AuditForms
