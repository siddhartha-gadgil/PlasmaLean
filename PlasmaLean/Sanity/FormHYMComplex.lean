/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMComplex
public import PlasmaLean.Sanity.FormHYMStar

/-!
# Sanity checks for the complex structure of the lift (`Theory/Fields/FormHYMComplex`)

The direction is `n = e₂`, the one of the source (complex coordinates `x₀ + i x₁`, `x₂ + i τ`).

1. **Values.** `J e₀ = e₁`, `J e₁ = -e₀`, `J e₂ = e_τ`, `J e_τ = -e₂`; `J² = -1` on `e₀`. The
   Kähler form is `1` on the planes `(e₀, e₁)` and `(e₂, e_τ)`, `0` on `(e₁, e₂)` and
   `(e₀, e_τ)`, and `-1` on `(e₁, e₀)`.
2. **Accepted.** The lift of `dx₁ ∧ dx₂` (field `e₀`) is a non-zero form of type `(1,1)` that
   is primitive.
3. **Rejected.** The opposite-sign form `π^*b + π^*(⋆b) ∧ dτ` for `b = dx₁ ∧ dx₂` (field `e₀`,
   orthogonal to `n`) is primitive but NOT of type `(1,1)`: it fails the type condition. For
   the field `e₂ = n` the opposite-sign form is the Kähler form: of type `(1,1)` but NOT
   primitive.
4. **The Kähler form** is of type `(1,1)` and not primitive (`⟨ω, ω⟩ = 2`).
5. **Not of type `(1,1)`.** `π^*(dx₁ ∧ dx₂)` alone is `1` on `(e₁, e₂)` and `0` on
   `(J e₁, J e₂) = (-e₀, e_τ)`.
6. **Junk closedness on the circle product.** For `ω = |x₀| dx₁ ∧ dx₂`, not differentiable at
   the origin, the circle form is "closed" at `(0, θ)`: `mextDeriv` is the junk value `0`
   there, so the hypothesis-free iff `mextDeriv_hymLiftCircleForm_eq_zero_iff'` is
   `True ↔ True` at such a point, exactly as `extDeriv_hymLift_eq_zero_iff` on `ℝ³ × ℝ`.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormHYMComplex

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields Matrix TauCeti
open scoped Manifold

/-- The direction `e₂` is a unit vector. -/
theorem norm_e2 : ‖(coordVec 2 : Space)‖ = 1 := by simp [coordVec]

/-! ### Values -/

/-- `J e₀ = e₁`. -/
theorem J_e0 : liftJ (coordVec 2) (coordVec 0, 0) = (coordVec 1, 0) :=
  liftJ_coordVec_two_frame.1

/-- `J e₁ = -e₀`. -/
theorem J_e1 : liftJ (coordVec 2) (coordVec 1, 0) = (-coordVec 0, 0) :=
  liftJ_coordVec_two_frame.2.1

/-- `J e₂ = e_τ`. -/
theorem J_e2 : liftJ (coordVec 2) (coordVec 2, 0) = (0, 1) :=
  liftJ_coordVec_two_frame.2.2.1

/-- `J e_τ = -e₂`. -/
theorem J_etau : liftJ (coordVec 2) (0, 1) = (-coordVec 2, 0) :=
  liftJ_coordVec_two_frame.2.2.2

/-- `J² e₀ = -e₀`, from the two values above (not from the general theorem). -/
theorem J_J_e0 : liftJ (coordVec 2) (liftJ (coordVec 2) (coordVec 0, 0)) = -(coordVec 0, 0) := by
  rw [J_e0, J_e1]
  simp

/-- The Kähler form is `1` on the plane `(e₀, e₁)`. -/
theorem kahler_e0_e1 : kahlerForm (coordVec 2) ![(coordVec 0, 0), (coordVec 1, 0)] = 1 := by
  rw [kahlerForm_apply, J_e0]
  simp [liftDot, coordVec]

/-- The Kähler form is `-1` on `(e₁, e₀)`. -/
theorem kahler_e1_e0 : kahlerForm (coordVec 2) ![(coordVec 1, 0), (coordVec 0, 0)] = -1 := by
  rw [kahlerForm_apply, J_e1]
  simp [liftDot, coordVec]

/-- The Kähler form is `1` on the plane `(e₂, e_τ)`. -/
theorem kahler_e2_etau : kahlerForm (coordVec 2) ![(coordVec 2, 0), (0, 1)] = 1 := by
  rw [kahlerForm_apply, J_e2]
  simp [liftDot]

/-- The Kähler form vanishes on the plane `(e₁, e₂)`. -/
theorem kahler_e1_e2 : kahlerForm (coordVec 2) ![(coordVec 1, 0), (coordVec 2, 0)] = 0 := by
  rw [kahlerForm_apply, J_e1]
  simp [liftDot, coordVec, inner_components]

/-- The Kähler form vanishes on the plane `(e₀, e_τ)`. -/
theorem kahler_e0_etau : kahlerForm (coordVec 2) ![(coordVec 0, 0), (0, 1)] = 0 := by
  rw [kahlerForm_apply, J_e0]
  simp [liftDot]

/-! ### Accepted: the lift of `dx₁ ∧ dx₂` -/

/-- The lift of `dx₁ ∧ dx₂` is of type `(1,1)`. -/
theorem lift_e0_type11 : IsType11 (coordVec 2) (hymLiftAt (flux (coordVec 0))) :=
  isType11_hymLiftAt norm_e2 _

/-- The lift of `dx₁ ∧ dx₂` is primitive. -/
theorem lift_e0_primitive : IsPrimitive (coordVec 2) (hymLiftAt (flux (coordVec 0))) :=
  isPrimitive_hymLiftAt _ _

/-- The accepted form is not zero, so the two conditions are not satisfied trivially. -/
theorem lift_e0_ne_zero : hymLiftAt (flux (coordVec 0)) ≠ 0 := FormHYMStar.lift_e0_ne_zero

/-- An independent check of the type condition on one pair: `ℱ(e₁, e₂) = 1` and
`ℱ(J e₁, J e₂) = ℱ(-e₀, e_τ) = 1`. -/
theorem lift_e0_J_value :
    hymLiftAt (flux (coordVec 0)) ![(coordVec 1, 0), (coordVec 2, 0)] = 1 ∧
    hymLiftAt (flux (coordVec 0))
      ![liftJ (coordVec 2) (coordVec 1, 0), liftJ (coordVec 2) (coordVec 2, 0)] = 1 := by
  rw [J_e1, J_e2]
  constructor <;>
  · rw [hymLiftAt_apply, hodge_flux, flux_apply, volForm_vec]
    simp [coordVec]

/-! ### Rejected: the opposite sign -/

/-- **Rejected (type).** The opposite-sign form of the field `e₀` is not of type `(1,1)`. -/
theorem sdLift_e0_not_type11 : ¬ IsType11 (coordVec 2) (sdLiftAt (flux (coordVec 0))) := by
  rw [isType11_sdLiftAt_flux_iff norm_e2]
  intro h
  have k := congrFun (congrArg (fun v : Space => v.ofLp) h) 0
  simp [coordVec] at k

/-- The opposite-sign form of the field `e₀` is primitive: it fails only the type condition. -/
theorem sdLift_e0_primitive : IsPrimitive (coordVec 2) (sdLiftAt (flux (coordVec 0))) := by
  rw [IsPrimitive, sdLiftAt, hodge_flux, kahlerForm, liftInner_ofParts_flux_flat]
  simp [coordVec, inner_components]

/-- The opposite-sign form of the field `e₂ = n` is the Kähler form. -/
theorem sdLift_e2_eq_kahler : sdLiftAt (flux (coordVec 2)) = kahlerForm (coordVec 2) := by
  rw [sdLiftAt, hodge_flux, kahlerForm]

/-- **Rejected (primitivity).** The opposite-sign form of the field `e₂` is not primitive. -/
theorem sdLift_e2_not_primitive : ¬ IsPrimitive (coordVec 2) (sdLiftAt (flux (coordVec 2))) := by
  rw [sdLift_e2_eq_kahler]
  exact not_isPrimitive_kahlerForm norm_e2

/-- The opposite-sign form is not anti-self-dual, for either field. -/
theorem sdLift_e0_not_antiSelfDual :
    liftStar (sdLiftAt (flux (coordVec 0))) ≠ -sdLiftAt (flux (coordVec 0)) := fun h =>
  sdLift_e0_not_type11 ((liftStar_eq_neg_iff_isType11_and_isPrimitive norm_e2 _).1 h).1

/-! ### The Kähler form -/

/-- The Kähler form is of type `(1,1)`. -/
theorem kahler_type11 : IsType11 (coordVec 2) (kahlerForm (coordVec 2)) :=
  isType11_kahlerForm norm_e2

/-- The Kähler form is not primitive. -/
theorem kahler_not_primitive : ¬ IsPrimitive (coordVec 2) (kahlerForm (coordVec 2)) :=
  not_isPrimitive_kahlerForm norm_e2

/-- `⟨ω, ω⟩ = 2`, computed from the six coordinate planes. -/
theorem kahler_inner : liftInner (kahlerForm (coordVec 2)) (kahlerForm (coordVec 2)) = 2 := by
  rw [liftInner_kahlerForm_self, norm_e2]
  norm_num

/-- The Kähler form is self-dual, hence not anti-self-dual. -/
theorem kahler_not_antiSelfDual :
    liftStar (kahlerForm (coordVec 2)) ≠ -kahlerForm (coordVec 2) := fun h =>
  kahler_not_primitive ((liftStar_eq_neg_iff_isType11_and_isPrimitive norm_e2 _).1 h).2

/-- `ω ∧ ω = 2 vol` on the standard frame: the complex orientation is
`dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`. -/
theorem kahler_wedge_self :
    (ContinuousAlternatingMap.wedge (kahlerForm (coordVec 2)) (kahlerForm (coordVec 2)))
      ![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0), (0, 1)] = 2 := by
  rw [kahlerForm_wedge_kahlerForm, liftVol_frame, norm_e2]
  norm_num

/-! ### A form that is not of type `(1,1)` -/

/-- **Rejected (type).** `π^*(dx₁ ∧ dx₂)` is not of type `(1,1)`: it is `1` on `(e₁, e₂)` and
`0` on `(J e₁, J e₂) = (-e₀, e_τ)`. -/
theorem spatial_not_type11 : ¬ IsType11 (coordVec 2) (ofParts (flux (coordVec 0)) 0) := by
  intro h
  have k := h (coordVec 1, 0) (coordVec 2, 0)
  rw [J_e1, J_e2, ofParts_apply, ofParts_apply, flux_apply, flux_apply, volForm_vec,
    volForm_vec] at k
  simp [coordVec] at k

/-! ### Junk closedness on the circle product -/

/-- **A "closed" circle form that is a junk value.** For `ω = |x₀| dx₁ ∧ dx₂`, which is not
differentiable at the origin, `mextDeriv` of the circle form at `(0, θ)` is `0`. -/
theorem absCircle_junk_closed (ℓ : ℝ) [Fact (0 < ℓ)] (θ : AddCircle ℓ) :
    ¬ DifferentiableAt ℝ FormHYMLift.absForm 0 ∧
      mextDeriv (hymLiftCircleForm ℓ FormHYMLift.absForm) (0, θ) = 0 :=
  ⟨FormHYMLift.absForm_not_differentiableAt,
    mextDeriv_hymLiftCircleForm_of_not_differentiableAt ℓ
      FormHYMLift.absForm_not_differentiableAt θ⟩

end PlasmaLean.Sanity.FormHYMComplex
