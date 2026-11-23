/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMLift
public import PlasmaLean.Sanity.Forms

/-!
# Sanity checks for the Hermitian–Yang–Mills lift `Theory/Fields/FormHYMLift`

1. **Values.** The lift of the constant flux form `dx₁ ∧ dx₂` (field `e₀`) on coordinate
   planes: `1` on `(e₁, e₂)`, `-1` on `(e₀, e_τ)` (the sign of the source's `ℱ = β - α ∧ dτ`),
   `0` on `(e₁, e_τ)`.
2. **Accepted.** The lifts of constant forms and of the hyperbolic vacuum field are closed.
3. **Rejected, one fixture for each vacuum equation.** The rotation field `(-y, x, 0)` is
   divergence free but has curl `2 e₂`: its lift is closed at no point, and the defect is the
   `dτ` part (`rotation_lift_defect`). The identity field has zero curl but divergence `3`:
   its lift is closed at no point, and the defect is the part without `dτ`
   (`id_lift_defect`).
4. **Anti-self-duality has content.** The form with the opposite sign,
   `π^*b + π^*(⋆b) ∧ dτ` for `b = dx₁ ∧ dx₂`, is not anti-self-dual.
5. **Regression (audit AV-M6): the hypothesis-free iff is empty at non-differentiability
   points.** The field of forms `|x₀| dx₁ ∧ dx₂` is not differentiable at the origin
   (`absForm_not_differentiableAt`); there `dω = 0`, `d(⋆ω) = 0` and `dℱ = 0` all hold as junk
   values (`absLift_junk_closed`), so `extDeriv_hymLift_eq_zero_iff` is `True ↔ True` at such
   a point. The `C²` statements are not affected.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormHYMLift

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Sanity PlasmaLean.Sanity.Audit
  PlasmaLean.Sanity.Forms PlasmaLean.Fields Matrix

/-! ### Values -/

/-- The lift of `dx₁ ∧ dx₂` is `1` on the plane `(e₁, e₂)`. -/
theorem lift_e0_spatial :
    hymLiftAt (flux (coordVec 0)) ![(coordVec 1, 0), (coordVec 2, 0)] = 1 := by
  rw [hymLiftAt_apply, flux_coordVec]
  simp

/-- The lift of `dx₁ ∧ dx₂` is `-1` on the plane `(e₀, e_τ)`: the sign of `ℱ = β - α ∧ dτ`. -/
theorem lift_e0_tau :
    hymLiftAt (flux (coordVec 0)) ![(coordVec 0, 0), (0, 1)] = -1 := by
  rw [hymLiftAt_apply, hodge_flux, flat_coordVec_apply, flat_coordVec_apply, flux_apply,
    volForm_vec]
  simp [coordVec]

/-- The lift of `dx₁ ∧ dx₂` vanishes on the plane `(e₁, e_τ)`. -/
theorem lift_e0_mixed :
    hymLiftAt (flux (coordVec 0)) ![(coordVec 1, 0), (0, 1)] = 0 := by
  rw [hymLiftAt_apply, hodge_flux, flat_coordVec_apply, flat_coordVec_apply, flux_apply,
    volForm_vec]
  simp [coordVec]

/-! ### Accepted fixtures -/

/-- The lift of a constant 2-form is closed everywhere. -/
theorem const_lift_closed (b : Form 2) (p : LiftSpace) :
    extDeriv (hymLift fun _ => b) p = 0 :=
  (const_vacuumForm isOpen_univ b).hymLift_closed p ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- The lift of the hyperbolic vacuum field `(x, y, -2z)` is closed everywhere. -/
theorem hyperbolic_lift_closed (p : LiftSpace) :
    extDeriv (hymLift (fluxField fun y => hyperbolicField y)) p = 0 :=
  hyperbolic_vacuumForm.hymLift_closed p ⟨Set.mem_univ _, Set.mem_univ _⟩

/-! ### Rejected fixtures -/

/-- The rotation field is divergence free but not curl free: its lift is closed at no point.
This is the Ampère half of `extDeriv_hymLift_eq_zero_iff`. -/
theorem rotation_lift_not_closed (p : LiftSpace) :
    extDeriv (hymLift (fluxField fun y => rotationField y)) p ≠ 0 := by
  obtain ⟨x, τ⟩ := p
  intro h
  have h2 := ((extDeriv_hymLift_eq_zero_iff _ x τ).1 h).2
  simp only [fluxField_apply, hodge_flux] at h2
  rw [extDeriv_flat, fieldCurl_rotationField] at h2
  have h3 := congrArg (fun v : Euclid3 => v 2) (flux.injective (h2.trans (map_zero flux).symm))
  simp [basis] at h3

/-- The defect of the rotation lift is in the `dτ` part: `dℱ(e_τ, e₀, e₁) = -2`. -/
theorem rotation_lift_defect (x : Space) (τ : ℝ) :
    extDeriv (hymLift (fluxField fun y => rotationField y)) (x, τ)
      ![(0, 1), (coordVec 0, 0), (coordVec 1, 0)] = -2 := by
  rw [extDeriv_hymLift_apply, rotation_closed]
  simp only [fluxField_apply, hodge_flux]
  rw [extDeriv_flat, fieldCurl_rotationField, flux_apply, volForm_vec]
  simp [basis, coordVec]

/-- The identity field is curl free but has divergence `3`: its lift is closed at no point.
This is the Gauss half of `extDeriv_hymLift_eq_zero_iff`. -/
theorem id_lift_not_closed (p : LiftSpace) :
    extDeriv (hymLift (fluxField fun y => y)) p ≠ 0 := by
  obtain ⟨x, τ⟩ := p
  intro h
  have h1 := ((extDeriv_hymLift_eq_zero_iff _ x τ).1 h).1
  rw [show fluxField (fun y : Euclid3 => y) = fun y => flux y from rfl, extDeriv_flux_id] at h1
  have h3 := density.injective (h1.trans (map_zero density).symm)
  norm_num at h3

/-- The defect of the identity lift is in the part without `dτ`: `dℱ(e₀, e₁, e₂) = 3`. -/
theorem id_lift_defect (x : Space) (τ : ℝ) :
    extDeriv (hymLift (fluxField fun y => y)) (x, τ)
      ![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0)] = 3 := by
  rw [extDeriv_hymLift_apply,
    show fluxField (fun y : Euclid3 => y) = fun y => flux y from rfl, extDeriv_flux_id,
    density_apply, volForm_frame]
  simp

/-! ### Anti-self-duality has content -/

/-- The lift with the opposite sign, `π^*b + π^*(⋆b) ∧ dτ`, of `b = dx₁ ∧ dx₂` is not
anti-self-dual for the source's orientation (it is self-dual). -/
theorem wrong_sign_not_antiSelfDual :
    ¬ IsAntiSelfDual (2 • (flux (coordVec 0)).compContinuousLinearMap
        (ContinuousLinearMap.fst ℝ Space ℝ) - hymLiftAt (flux (coordVec 0))) := by
  intro h
  have h0 := h.1
  have e (a b : LiftSpace) :
      ((Prod.fst : LiftSpace → Space) ∘ ![a, b]) = ![a.1, b.1] := by
    funext i; fin_cases i <;> rfl
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_fst', e,
    lift_e0_tau, lift_e0_spatial, flux_coordVec] at h0
  rw [flux_apply, volForm_vec] at h0
  norm_num [coordVec] at h0

/-! ### The hypothesis-free iff at a point of non-differentiability (audit AV-M6) -/

/-- The field of 2-forms `|x₀| dx₁ ∧ dx₂`: the flux form of the field `|x₀| e₀`, which is
continuous and has a kink on the plane `x₀ = 0`. -/
def absForm (y : Space) : Form 2 := |y 0| • flux (coordVec 0)

/-- The field of forms `|x₀| dx₁ ∧ dx₂` is not differentiable at the origin: along the
`x₀`-axis its component on `(e₁, e₂)` is `|t|`. -/
theorem absForm_not_differentiableAt : ¬ DifferentiableAt ℝ absForm 0 := by
  intro h
  have hc : DifferentiableAt ℝ (fun t : ℝ => t • (coordVec 0 : Space)) 0 := by fun_prop
  have h0 : DifferentiableAt ℝ absForm ((fun t : ℝ => t • (coordVec 0 : Space)) 0) := by
    simpa using h
  have h2 : DifferentiableAt ℝ (fun t : ℝ => absForm (t • coordVec 0)) 0 :=
    DifferentiableAt.comp (g := absForm) (0 : ℝ) h0 hc
  have h3 : DifferentiableAt ℝ
      (fun t : ℝ => (flux.toContinuousLinearEquiv.symm (absForm (t • coordVec 0)) : Space)) 0 :=
    flux.toContinuousLinearEquiv.symm.differentiableAt.comp (0 : ℝ) h2
  have h4 : DifferentiableAt ℝ
      (fun t : ℝ => (flux.toContinuousLinearEquiv.symm (absForm (t • coordVec 0)) : Space) 0) 0 :=
    differentiableAt_euclidean.1 h3 0
  have e : (fun t : ℝ => (flux.toContinuousLinearEquiv.symm (absForm (t • coordVec 0)) : Space) 0)
      = fun t : ℝ => |t| := by
    funext t
    simp [absForm]
  rw [e] at h4
  exact not_differentiableAt_abs_zero h4

/-- **Regression (audit AV-M6): a "closed" lift that is a junk value.** For the field of forms
`ω = |x₀| dx₁ ∧ dx₂`, which is not differentiable at the origin, `dω = 0` and `d(⋆ω) = 0` at
the origin and `dℱ = 0` at `(0, τ)` for the lift `ℱ`. None of the three says anything about
`ω`: each exterior derivative is `0` because the Fréchet derivative of a function that is not
differentiable is `0` by convention, and the lift is not differentiable at `(0, τ)` either
(`differentiableAt_hymLift_iff`). So at such a point `extDeriv_hymLift_eq_zero_iff` reads
`True ↔ True`. The field `|x₀| e₀` is not a vacuum field near the origin (its divergence is
`sign x₀`, not `0`, off the plane `x₀ = 0`). The `C²` statements
`hymLift_closed_iff_vacuumForm` and `hymLift_closed_iff_vacuumField` are not affected: their
regularity hypothesis excludes this field on every open set meeting the plane `x₀ = 0`. -/
theorem absLift_junk_closed (τ : ℝ) :
    ¬ DifferentiableAt ℝ absForm 0 ∧ ¬ DifferentiableAt ℝ (hymLift absForm) (0, τ) ∧
      extDeriv absForm 0 = 0 ∧ extDeriv (fun y => hodge (absForm y)) 0 = 0 ∧
      extDeriv (hymLift absForm) (0, τ) = 0 := by
  have h := absForm_not_differentiableAt
  have h' : ¬ DifferentiableAt ℝ (hymLift absForm) (0, τ) :=
    fun hd => h ((differentiableAt_hymLift_iff absForm 0 τ).1 hd)
  have hz (k : ℕ) : ContinuousAlternatingMap.alternatizeUncurryFin
      (0 : Space →L[ℝ] Form k) = 0 := by
    ext v
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have h1 : extDeriv absForm 0 = 0 := by
    rw [extDeriv, fderiv_zero_of_not_differentiableAt h, hz]
  have h2 : extDeriv (fun y => hodge (absForm y)) 0 = 0 := by
    rw [extDeriv, fderiv_hodge, fderiv_zero_of_not_differentiableAt h,
      ContinuousLinearMap.comp_zero, hz]
  exact ⟨h, h', h1, h2, (extDeriv_hymLift_eq_zero_iff absForm 0 τ).2 ⟨h1, h2⟩⟩

/-- Regression (audit AV-M6): the regularity hypothesis of the `C²` iff
`hymLift_closed_iff_vacuumForm` fails for `|x₀| dx₁ ∧ dx₂` on all of space, so that theorem
does not turn the junk value of `absLift_junk_closed` into a vacuum statement. -/
theorem absForm_not_contDiffOn : ¬ ContDiffOn ℝ 2 absForm Set.univ := fun h =>
  absForm_not_differentiableAt
    ((contDiffOn_univ.1 h).differentiable (by norm_num)).differentiableAt

end PlasmaLean.Sanity.FormHYMLift
