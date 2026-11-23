/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMCircle
public import PlasmaLean.Sanity.FormHYMLift
public import PlasmaLean.Sanity.FormHYMStar

/-!
# Sanity checks for the lift on `ℝ³ × S¹` (`Theory/Fields/FormHYMCircle`)

All fixtures are on the manifold `ℝ³ × AddCircle 1` with TauCeti's `mextDeriv`.

1. **Accepted.** The lifts of constant 2-forms and of the hyperbolic vacuum field `(x, y, -2z)`
   are closed on `ℝ³ × S¹`, and the constant lift is a smooth form.
2. **Rejected, one fixture for each vacuum equation.** The lift of the rotation field
   `(-y, x, 0)` (divergence free, curl `2 e₂`) and the lift of the identity field (curl free,
   divergence `3`) are closed at no point of `ℝ³ × S¹`; the rotation lift is closed on the
   manifold `Ω × S¹` for no nonempty open `Ω`.
3. **Regularity has content.** The lift of a discontinuous field of forms is not a continuous
   form on `ℝ³ × S¹`.
4. **Energy.** `|ℱ|² = 2` for the lift of `dx₁ ∧ dx₂` (restating `lift_e0_inner` of
   `Sanity/FormHYMStar` through the general identity), and the lifts of `dx₁ ∧ dx₂` and
   `dx₂ ∧ dx₀` are orthogonal.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormHYMCircle

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Sanity PlasmaLean.Sanity.Audit
  PlasmaLean.Sanity.Forms PlasmaLean.Fields Matrix TauCeti
open scoped Manifold

/-! ### Accepted fixtures -/

/-- The lift of a constant 2-form is closed on `ℝ³ × S¹`. -/
theorem const_circle_closed (b : Form 2) :
    mextDeriv (hymLiftCircleForm 1 fun _ => b) = 0 :=
  (hymLiftCircleForm_closed_iff_vacuumForm 1 contDiff_const).2 (const_vacuumForm isOpen_univ b)

/-- The lift of a constant 2-form is a smooth form on `ℝ³ × S¹`. -/
theorem const_circle_smooth (b : Form 2) :
    IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) ⊤ (hymLiftCircleForm 1 fun _ => b) :=
  isSmoothForm_hymLiftCircleForm 1 contDiff_const

/-- The lift of the hyperbolic vacuum field `(x, y, -2z)` is closed on `ℝ³ × S¹`. -/
theorem hyperbolic_circle_closed :
    mextDeriv (hymLiftCircleForm 1 (fluxField fun y => hyperbolicField y)) = 0 :=
  (hymLiftCircleForm_closed_iff_vacuumForm 1
    (contDiffOn_univ.1 hyperbolic_vacuumForm.contDiffOn)).2 hyperbolic_vacuumForm

/-! ### Rejected fixtures -/

/-- The flux form of the rotation field is smooth. -/
theorem contDiff_flux_rotation {n : WithTop ℕ∞} :
    ContDiff ℝ n (fluxField fun y => rotationField y) :=
  flux.toContinuousLinearEquiv.contDiff.comp rotationField.contDiff

/-- The flux form of the identity field is smooth. -/
theorem contDiff_flux_id {n : WithTop ℕ∞} : ContDiff ℝ n (fluxField fun y : Euclid3 => y) :=
  flux.toContinuousLinearEquiv.contDiff.comp contDiff_id

/-- The rotation field is not curl free: its lift is closed at no point of `ℝ³ × S¹`. -/
theorem rotation_circle_not_closed (p : Space × AddCircle (1 : ℝ)) :
    mextDeriv (hymLiftCircleForm 1 (fluxField fun y => rotationField y)) p ≠ 0 := by
  obtain ⟨x, θ⟩ := p
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  intro h
  refine FormHYMLift.rotation_lift_not_closed (x, τ) ?_
  rw [← mextDeriv_hymLiftCircleForm_coe 1 contDiff_flux_rotation.contDiffAt τ]
  exact h

/-- The identity field is not divergence free: its lift is closed at no point of `ℝ³ × S¹`. -/
theorem id_circle_not_closed (p : Space × AddCircle (1 : ℝ)) :
    mextDeriv (hymLiftCircleForm 1 (fluxField fun y => y)) p ≠ 0 := by
  obtain ⟨x, θ⟩ := p
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  intro h
  refine FormHYMLift.id_lift_not_closed (x, τ) ?_
  rw [← mextDeriv_hymLiftCircleForm_coe 1 contDiff_flux_id.contDiffAt τ]
  exact h

/-- On the manifold `Ω × S¹`, for a nonempty open `Ω`, the rotation lift is not closed. -/
theorem rotation_region_not_closed (U : TopologicalSpace.Opens Space)
    (hne : (U : Set Space).Nonempty) :
    mextDeriv (hymLiftRegionForm 1 U (fluxField fun y => rotationField y)) ≠ 0 := fun h =>
  rotation_not_vacuumForm hne
    ((hymLiftRegionForm_closed_iff_vacuumForm 1 U contDiff_flux_rotation.contDiffOn).1 h)

/-! ### Regularity has content -/

/-- A field of 2-forms that is not continuous has a lift that is not a continuous form on
`ℝ³ × S¹`. -/
theorem discontinuous_circle_not_continuous {w : Space → Form 2} (hw : ¬ Continuous w) :
    ¬ IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) 0 (hymLiftCircleForm 1 w) := fun h =>
  hw (contDiff_zero.1 ((isSmoothForm_hymLiftCircleForm_iff 1 w).1 h))

/-! ### Energy -/

/-- The squared norm of the lift of `dx₁ ∧ dx₂` is `2`, through the general identity
`|ℱ|² = 2 |B|²`. -/
theorem lift_e0_inner : liftInner (hymLiftAt (flux (coordVec 0)))
    (hymLiftAt (flux (coordVec 0))) = 2 := by
  rw [liftInner_hymLiftAt_flux_self]
  simp [coordVec]

/-- The lifts of `dx₁ ∧ dx₂` and `dx₂ ∧ dx₀` are orthogonal. -/
theorem lift_e0_e1_inner : liftInner (hymLiftAt (flux (coordVec 0)))
    (hymLiftAt (flux (coordVec 1))) = 0 := by
  rw [liftInner_hymLiftAt_flux]
  simp [coordVec, EuclideanSpace.inner_single_left]

/-- The Yang–Mills density of the lift of `dx₁ ∧ dx₂` is `1`, twice the magnetic energy density
`½` of the unit field `e₀`. -/
theorem lift_e0_ymDensity : ymDensity (hymLiftAt (flux (coordVec 0))) = 1 := by
  rw [ymDensity_hymLiftAt_flux]
  simp [coordVec]

end PlasmaLean.Sanity.FormHYMCircle
