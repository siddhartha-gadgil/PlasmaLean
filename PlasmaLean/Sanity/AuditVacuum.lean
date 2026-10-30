/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.Vacuum

/-!
# Strict-audit checks for `Kernel/Vacuum` (audit of 30 October 2026)

Added by the first strict kernel audit (`notes/audit/2026-10-30-kernel-audit.md`, commit
`cda8bd0`). `Sanity/Vacuum` already gives the degenerate case (`zero_vacuum`), concrete
instances (constant, hyperbolic and filament fields) and a curl counterexample
(`rotationField_not_vacuum`). This module adds:

* independence of the two field laws: the identity field `B = x` is curl free with divergence
  `3` (`fieldCurl_id`, `fieldDiv_id`, `id_not_vacuum`), and the rotation field is divergence
  free (`fieldDiv_rotationField`), so `∇ · B = 0` and `∇ × B = 0` each have content;
* nonempty domain (regression for finding V-1): every field, including the rotation field, is a
  vacuum field on the empty region (`vacuumField_empty`, `rotationField_vacuum_empty`);
* totalized derivatives: at a kink, where `B = |x| e_x` is not differentiable, Lean's `fderiv`
  is `0`, so the pointwise divergence and curl vanish there (`absField_fieldDiv_zero`,
  `absField_fieldCurl_zero`); the open-set and `C²` laws are what make the operator equations
  meaningful (`absField_not_vacuum`);
* linearity: vacuum fields are closed under scaling (`VacuumField.const_smul`).
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Sanity.Audit
open PlasmaLean.Vacuum PlasmaLean.Sanity

/-! ### Independence of the divergence and curl laws -/

/-- The derivative of the identity field is the identity operator. -/
theorem fderiv_idField (x : Euclid3) :
    fderiv ℝ (fun y : Euclid3 => y) x = ContinuousLinearMap.id ℝ Euclid3 := fderiv_fun_id

/-- The identity field `B = x` has divergence `3`. -/
theorem fieldDiv_id (x : Euclid3) : fieldDiv (fun y => y) x = 3 := by
  rw [fieldDiv, fderiv_idField, divOp_id]

/-- The identity field `B = x` is curl free (its Jacobian is the identity, hence symmetric). -/
theorem fieldCurl_id (x : Euclid3) : fieldCurl (fun y => y) x = 0 := by
  rw [fieldCurl, fderiv_idField, curlOp_eq_zero_iff]
  intro i j
  simp only [ContinuousLinearMap.id_apply, coordVec, PiLp.single_apply]
  by_cases h : i = j
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- **Counterexample to the divergence law.** The curl-free field `B = x` is not a vacuum
field on any nonempty region: the law `∇ · B = 0` is not implied by `∇ × B = 0`. -/
theorem id_not_vacuum {Ω : Set Euclid3} (hne : Ω.Nonempty) : ¬ VacuumField Ω (fun y => y) := by
  intro h
  obtain ⟨x, hx⟩ := hne
  have := h.div_eq_zero x hx
  rw [fieldDiv_id] at this
  norm_num at this

/-- The rotation field `(-y, x, 0)` is divergence free, so the curl law of
`rotationField_not_vacuum` is not implied by `∇ · B = 0`. -/
theorem fieldDiv_rotationField (x : Euclid3) : fieldDiv (fun y => rotationField y) x = 0 := by
  rw [fieldDiv, rotationField.fderiv, divOp_apply]
  obtain ⟨a0, -, -⟩ := rotationField_coords (coordVec 0)
  obtain ⟨-, b1, -⟩ := rotationField_coords (coordVec 1)
  obtain ⟨-, -, c2⟩ := rotationField_coords (coordVec 2)
  rw [a0, b1, c2]
  simp

/-! ### Nonempty domain -/

/-- **Regression (finding V-1, nonempty domain).** Every field is a vacuum field on the empty
region; theorems quantifying over `VacuumField Ω B` need `Ω` nonempty (or a point of `Ω`) to
have content. -/
theorem vacuumField_empty (B : Euclid3 → Euclid3) : VacuumField ∅ B :=
  ⟨isOpen_empty, contDiffOn_empty, fun _ h => h.elim, fun _ h => h.elim⟩

/-- The rejected rotation field is accepted on the empty region. -/
theorem rotationField_vacuum_empty : VacuumField ∅ (fun y => rotationField y) :=
  vacuumField_empty _

/-! ### Totalized derivatives -/

/-- A field with a kink on the plane `x = 0`: `B(y) = |y₀| e_x`. -/
@[expose] def absField (y : Euclid3) : Euclid3 := |y 0| • coordVec 0

/-- The kink field is not differentiable at the origin. -/
theorem absField_not_differentiableAt : ¬ DifferentiableAt ℝ absField 0 := by
  intro h
  have hline : DifferentiableAt ℝ (fun t : ℝ => t • coordVec 0) 0 :=
    differentiableAt_id.smul_const _
  have h0 : DifferentiableAt ℝ absField ((0 : ℝ) • coordVec 0) := by rwa [zero_smul]
  have hc : DifferentiableAt ℝ
      (fun t : ℝ => EuclideanSpace.proj (0 : Fin 3) (absField (t • coordVec 0))) 0 :=
    ((EuclideanSpace.proj (0 : Fin 3)).differentiableAt.comp 0 (h0.comp 0 hline) :)
  have he : (fun t : ℝ => EuclideanSpace.proj (0 : Fin 3) (absField (t • coordVec 0))) =
      fun t => |t| := by
    funext t
    simp [absField, coordVec]
  rw [he] at hc
  exact not_differentiableAt_abs_zero hc

/-- **Totalization hazard.** At the kink, `fderiv` is `0` by convention, so the pointwise
divergence of the non-differentiable field vanishes there. -/
theorem absField_fieldDiv_zero : fieldDiv absField 0 = 0 := by
  rw [fieldDiv, fderiv_zero_of_not_differentiableAt absField_not_differentiableAt]
  simp [divOp]

/-- **Totalization hazard.** At the kink, the pointwise curl of the non-differentiable field
also vanishes. -/
theorem absField_fieldCurl_zero : fieldCurl absField 0 = 0 := by
  rw [fieldCurl, fderiv_zero_of_not_differentiableAt absField_not_differentiableAt]
  ext k
  fin_cases k <;> simp [curlOp]

/-- The regularity law excludes the kink field on any open region containing the kink, although
its pointwise divergence and curl vanish there. -/
theorem absField_not_vacuum {Ω : Set Euclid3} (h0 : (0 : Euclid3) ∈ Ω) :
    ¬ VacuumField Ω absField := by
  intro h
  exact absField_not_differentiableAt
    ((h.contDiffOn.differentiableOn two_ne_zero).differentiableAt (h.isOpen.mem_nhds h0))

/-! ### Linearity -/

/-- Scaling of the divergence operator. -/
theorem divOp_smul (a : ℝ) (L : Euclid3 →L[ℝ] Euclid3) : divOp (a • L) = a * divOp L := by
  simp [divOp, Finset.mul_sum]

/-- Scaling of the curl operator. -/
theorem curlOp_smul (a : ℝ) (L : Euclid3 →L[ℝ] Euclid3) : curlOp (a • L) = a • curlOp L := by
  ext k
  fin_cases k <;> simp [curlOp] <;> ring

/-- **Linearity.** A constant multiple of a vacuum field is a vacuum field on the same region. -/
theorem VacuumField.const_smul {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (h : VacuumField Ω B) (a : ℝ) : VacuumField Ω (fun y => a • B y) := by
  have hd : ∀ x ∈ Ω, fderiv ℝ (fun y => a • B y) x = a • fderiv ℝ B x := fun x hx =>
    fderiv_const_smul ((h.contDiffOn.differentiableOn two_ne_zero).differentiableAt
      (h.isOpen.mem_nhds hx)) a
  refine ⟨h.isOpen, h.contDiffOn.const_smul a, fun x hx => ?_, fun x hx => ?_⟩
  · rw [fieldDiv, hd x hx, divOp_smul, ← fieldDiv, h.div_eq_zero x hx, mul_zero]
  · rw [fieldCurl, hd x hx, curlOp_smul, ← fieldCurl, h.curl_eq_zero x hx, smul_zero]

end PlasmaLean.Sanity.Audit
