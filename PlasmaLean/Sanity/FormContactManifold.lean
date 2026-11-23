/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormContactManifold

/-!
# Sanity checks for `Theory/Fields/FormContactManifold`

* Accepted: the helical Beltrami field `(cos z, sin z, 0)` is smooth
  (`helicalField_contDiff`) and has norm one (`norm_helicalField`); its 1-form is a TauCeti
  contact form on `ℝ³` (`helical_isContactForm`), TauCeti's pointwise condition holds
  (`helical_isContactFormAt`), and its TauCeti Reeb vector field is the field itself
  (`helical_reebVectorField`).
* Rejected: the 1-form of a constant field is not a TauCeti contact form
  (`const_not_isContactForm`), and fails TauCeti's pointwise condition at every point
  (`const_not_isContactFormAt`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormContactManifold

open PlasmaLean PlasmaLean.Forms PlasmaLean.Vacuum PlasmaLean.Fields
open TauCeti
open scoped Manifold ContDiff

/-- The helical field is smooth. -/
theorem helicalField_contDiff : ContDiff ℝ ∞ helicalField := by
  have hz : ContDiff ℝ ∞ fun y : Space => y 2 := contDiff_euclidean.1 contDiff_id 2
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · exact Real.contDiff_cos.comp hz
  · exact Real.contDiff_sin.comp hz
  · exact contDiff_const

/-- The helical field has norm one. -/
theorem norm_helicalField (x : Space) : ‖helicalField x‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three]
  simp [helicalField]

/-- Accepted: the helical 1-form `cos z dx + sin z dy` is a TauCeti contact form on `ℝ³`. -/
theorem helical_isContactForm :
    (flatSmoothForm helicalField helicalField_contDiff).IsContactForm :=
  helicalField_beltrami.isContactForm_flatSmoothForm helicalField_contDiff
    (fun _ => by norm_num) helicalField_ne_zero

/-- Accepted: TauCeti's pointwise contact condition holds for the helical 1-form. -/
theorem helical_isContactFormAt (x : Space) :
    IsContactFormAt (I := 𝓘(ℝ, Space)) (M := Space) (fun y => flat (helicalField y)) x :=
  (isContactFormAt_flat_iff helicalField x).2 (helicalField_contact x)

/-- Accepted: the TauCeti Reeb vector field of the helical contact form is the helical field
itself. -/
theorem helical_reebVectorField (x : Space) :
    (flatSmoothForm helicalField helicalField_contDiff).reebVectorField x = helicalField x := by
  rw [helicalField_beltrami.reebVectorField_flatSmoothForm helicalField_contDiff
    (fun _ => by norm_num) helicalField_ne_zero, norm_helicalField]
  exact (by simp : ((1 : ℝ) ^ 2)⁻¹ • helicalField x = helicalField x)

/-- Rejected: the 1-form of a constant field is not a TauCeti contact form. -/
theorem const_not_isContactForm (B₀ : Space) :
    ¬ (flatSmoothForm (fun _ => B₀) contDiff_const).IsContactForm := fun h =>
  const_not_contact B₀ 0 ((isContactForm_flatSmoothForm_iff _ contDiff_const).1 h 0)

/-- Rejected: the 1-form of a constant field fails TauCeti's pointwise contact condition. -/
theorem const_not_isContactFormAt (B₀ x : Space) :
    ¬ IsContactFormAt (I := 𝓘(ℝ, Space)) (M := Space) (fun _ : Space => flat B₀) x := fun h =>
  const_not_contact B₀ x ((isContactFormAt_flat_iff (fun _ => B₀) x).1 h)

end PlasmaLean.Sanity.FormContactManifold
