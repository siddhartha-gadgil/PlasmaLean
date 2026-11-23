/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMEnergy
public import PlasmaLean.Theory.Fields.FormHYMComplex
public import PlasmaLean.Sanity.Forms
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Sanity checks for the Yang–Mills energy of the lift (`Theory/Fields/FormHYMEnergy`)

1. **Values of the pointwise bound.** For `F = π^*(ι_A vol) + π^*(E♭) ∧ dτ`:
   `|F|² = |A|² + |E|²` and `⟨F, ⋆F⟩ = 2 ⟨A, E⟩` (`wedgeDensity_ofParts_flux_flat`).
   * anti-self-dual, `A = e₀`, `E = -e₀` (the lift of `dx₁ ∧ dx₂`): `|F|² = 2`,
     `⟨F, ⋆F⟩ = -2`; equality in `|F|² ≥ -⟨F, ⋆F⟩`.
   * self-dual, `A = E = e₀`: `|F|² = 2`, `⟨F, ⋆F⟩ = 2`; the anti-self-dual bound is strict
     (`-2 < 2`) and the self-dual bound is an equality.
   * mixed, `A = e₀`, `E = 0` (the form `π^*(dx₁ ∧ dx₂)`): `|F|² = 1`, `⟨F, ⋆F⟩ = 0`; both
     bounds are strict.
2. **Connection, accepted.** For the constant field `B = e₂` the explicit potentials
   `A = x₀ dx₁`, `φ = x₂` give `d(π^*A - (π^*φ) dτ) = ℱ` at every point. For the hyperbolic
   vacuum field `(x, y, -2z)` the connection exists, and it can be taken with the explicit
   scalar potential `(x² + y²)/2 - z²`.
3. **Connection, rejected.** With the other sign, `π^*A + (π^*φ) dτ`, the curvature is not the
   lift: on the plane `(e₂, e_τ)` it is `1` and the lift is `-1`.
4. **Minimality, strict instance.** For the hyperbolic vacuum field and the perturbation
   `a = f dτ` with `f` a smooth bump function at the origin of `ℝ³ × ℝ`, the change of energy
   `∫ (|ℱ + da|² - |ℱ|²)` is strictly positive. The point is that `da ≠ 0` somewhere: otherwise
   `f` would be constant along the line `t ↦ (t e₀, 0)`, but it is `1` at the origin and `0`
   far away.
5. **Minimality, degenerate instance.** For `a = 0` the change of energy is `0`.

Not instantiated: a perturbation supported in a proper subregion `Ω × ℝ` with `Ω ≠ ℝ³` (the
theory statement allows it; the fixture uses `Ω = ℝ³`).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormHYMEnergy

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
  PlasmaLean.Sanity.Forms Matrix MeasureTheory
open scoped RealInnerProductSpace

/-! ### 1. Values of the pointwise bound -/

/-- `|F|² = |A|² + |E|²` for `F = π^*(ι_A vol) + π^*(E♭) ∧ dτ`. -/
theorem liftInner_self_ofParts_flux_flat (A E : Space) :
    liftInner (ofParts (flux A) (flat E)) (ofParts (flux A) (flat E)) = ‖A‖ ^ 2 + ‖E‖ ^ 2 := by
  rw [liftInner_ofParts_flux_flat, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- `⟨F, ⋆F⟩ = 2 ⟨A, E⟩` for `F = π^*(ι_A vol) + π^*(E♭) ∧ dτ`: the wedge density is twice
the product "magnetic part times electric part". -/
theorem wedgeDensity_ofParts_flux_flat (A E : Space) :
    wedgeDensity (ofParts (flux A) (flat E)) = 2 * ⟪A, E⟫ := by
  rw [wedgeDensity, liftStar_ofParts, hodge_symm_flat, hodge_flux, liftInner_ofParts_flux_flat,
    real_inner_comm E A]
  ring

/-- The unit vector `e₀` has norm one. -/
theorem norm_coordVec_zero : ‖coordVec 0‖ = 1 := by simp [coordVec]

/-- Anti-self-dual fixture (the lift of `dx₁ ∧ dx₂`): `|F|² = 2`, `⟨F, ⋆F⟩ = -2`, and the
bound `|F|² ≥ -⟨F, ⋆F⟩` is an equality. -/
theorem antiSelfDual_values :
    liftInner (hymLiftAt (flux (coordVec 0))) (hymLiftAt (flux (coordVec 0))) = 2 ∧
    wedgeDensity (hymLiftAt (flux (coordVec 0))) = -2 ∧
    liftInner (hymLiftAt (flux (coordVec 0))) (hymLiftAt (flux (coordVec 0))) =
      -wedgeDensity (hymLiftAt (flux (coordVec 0))) := by
  have e : hymLiftAt (flux (coordVec 0)) = ofParts (flux (coordVec 0)) (flat (-coordVec 0)) := by
    rw [hymLiftAt_eq_ofParts, hodge_flux, map_neg]
  rw [e, liftInner_self_ofParts_flux_flat, wedgeDensity_ofParts_flux_flat, inner_neg_right,
    real_inner_self_eq_norm_sq, norm_neg, norm_coordVec_zero]
  norm_num

/-- Self-dual fixture `π^*(dx₁ ∧ dx₂) + dx₀ ∧ dτ`: `|F|² = 2`, `⟨F, ⋆F⟩ = 2`. The
anti-self-dual bound is strict, `-⟨F, ⋆F⟩ < |F|²`, and the form is not anti-self-dual. -/
theorem selfDual_values :
    liftInner (sdLiftAt (flux (coordVec 0))) (sdLiftAt (flux (coordVec 0))) = 2 ∧
    wedgeDensity (sdLiftAt (flux (coordVec 0))) = 2 ∧
    -wedgeDensity (sdLiftAt (flux (coordVec 0))) <
      liftInner (sdLiftAt (flux (coordVec 0))) (sdLiftAt (flux (coordVec 0))) ∧
    liftStar (sdLiftAt (flux (coordVec 0))) ≠ -sdLiftAt (flux (coordVec 0)) := by
  have e : sdLiftAt (flux (coordVec 0)) = ofParts (flux (coordVec 0)) (flat (coordVec 0)) := by
    rw [sdLiftAt, hodge_flux]
  have h1 : liftInner (sdLiftAt (flux (coordVec 0))) (sdLiftAt (flux (coordVec 0))) = 2 := by
    rw [e, liftInner_self_ofParts_flux_flat, norm_coordVec_zero]; norm_num
  have h2 : wedgeDensity (sdLiftAt (flux (coordVec 0))) = 2 := by
    rw [e, wedgeDensity_ofParts_flux_flat, real_inner_self_eq_norm_sq, norm_coordVec_zero]
    norm_num
  refine ⟨h1, h2, by rw [h1, h2]; norm_num, fun h => ?_⟩
  have h3 := (liftInner_self_eq_neg_wedgeDensity_iff _).2 h
  rw [h1, h2] at h3
  norm_num at h3

/-- Mixed fixture `π^*(dx₁ ∧ dx₂)`: `|F|² = 1`, `⟨F, ⋆F⟩ = 0`. Both bounds are strict, so the
form is neither self-dual nor anti-self-dual. -/
theorem mixed_values :
    liftInner (ofParts (flux (coordVec 0)) (flat 0)) (ofParts (flux (coordVec 0)) (flat 0)) = 1 ∧
    wedgeDensity (ofParts (flux (coordVec 0)) (flat 0)) = 0 ∧
    liftStar (ofParts (flux (coordVec 0)) (flat 0)) ≠ -ofParts (flux (coordVec 0)) (flat 0) ∧
    liftStar (ofParts (flux (coordVec 0)) (flat 0)) ≠ ofParts (flux (coordVec 0)) (flat 0) := by
  have h1 : liftInner (ofParts (flux (coordVec 0)) (flat 0))
      (ofParts (flux (coordVec 0)) (flat 0)) = 1 := by
    rw [liftInner_self_ofParts_flux_flat, norm_coordVec_zero]; norm_num
  have h2 : wedgeDensity (ofParts (flux (coordVec 0)) (flat 0)) = 0 := by
    rw [wedgeDensity_ofParts_flux_flat]; simp
  refine ⟨h1, h2, fun h => ?_, fun h => ?_⟩
  · have h3 := (liftInner_self_eq_neg_wedgeDensity_iff _).2 h
    rw [h1, h2] at h3
    norm_num at h3
  · have h3 := (liftInner_self_eq_wedgeDensity_iff _).2 h
    rw [h1, h2] at h3
    norm_num at h3

/-! ### 2. and 3. The connection -/

/-- The vector potential `A = x₀ e₁` of the constant field `e₂`, as a linear map. -/
def constPotential : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 3)).smulRight (coordVec 1)

/-- `∇ × (x₀ e₁) = e₂`. -/
theorem fieldCurl_constPotential (x : Space) : fieldCurl constPotential x = coordVec 2 := by
  rw [fieldCurl, ContinuousLinearMap.fderiv]
  ext i
  fin_cases i <;> simp [curlOp, constPotential, coordVec]

/-- The scalar potential `φ = x₂` of the constant field `e₂`: `dφ = ⋆(ι_{e₂} vol)`. -/
theorem formGrad_proj_two (x : Space) :
    formGrad (fun y : Space => y 2) x = hodge (flux (coordVec 2)) := by
  have e : (fun y : Space => y 2) = ⇑(EuclideanSpace.proj (2 : Fin 3)) := rfl
  ext w
  rw [formGrad_apply, e, ContinuousLinearMap.fderiv, hodge_flux, flat_apply]
  simp [coordVec, EuclideanSpace.inner_single_left]

/-- The coordinate function `x₂` is differentiable. -/
theorem differentiableAt_proj_two (x : Space) : DifferentiableAt ℝ (fun y : Space => y 2) x :=
  (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt

/-- The 1-form `x₀ dx₁` is differentiable. -/
theorem differentiableAt_flat_constPotential (x : Space) :
    DifferentiableAt ℝ (fun y => flat (constPotential y)) x :=
  ((flat.toContinuousLinearEquiv : Space →L[ℝ] Form 1).comp constPotential).differentiableAt

/-- **Accepted, explicit**: for the constant field `e₂` the connection form
`π^*(x₀ dx₁) - x₂ dτ` has curvature the lift, at every point of `ℝ³ × ℝ`. -/
theorem const_connection (x : Space) (τ : ℝ) :
    extDeriv (liftConnection (fun y => flat (constPotential y)) fun y => y 2) (x, τ) =
      hymLift (fluxField fun _ => coordVec 2) (x, τ) := by
  have hd : formGrad (fun y : Space => y 2) x = hodge (fluxField (fun _ => coordVec 2) x) := by
    rw [fluxField_apply]
    exact formGrad_proj_two x
  have hdA : extDeriv (fun y => flat (constPotential y)) x =
      fluxField (fun _ => coordVec 2) x := by
    rw [extDeriv_flat, fieldCurl_constPotential, fluxField_apply]
  exact extDeriv_liftConnection_eq_hymLift (w := fluxField fun _ => coordVec 2)
    (differentiableAt_flat_constPotential x) (differentiableAt_proj_two x) hdA hd τ

/-- **Rejected**: with the other sign of the scalar potential, `π^*(x₀ dx₁) + x₂ dτ`, the
curvature is not the lift. On the plane `(e₂, e_τ)` it is `1`, the lift is `-1`. -/
theorem const_connection_wrong_sign (x : Space) (τ : ℝ) :
    extDeriv (liftConnection (fun y => flat (constPotential y)) fun y => -y 2) (x, τ) ≠
      hymLift (fluxField fun _ => coordVec 2) (x, τ) := by
  intro h
  rw [extDeriv_liftConnection (differentiableAt_flat_constPotential x)
    (differentiableAt_proj_two x).fun_neg, formGrad_neg, formGrad_proj_two, neg_neg,
    extDeriv_flat, fieldCurl_constPotential] at h
  have k := congrArg (fun F : LiftForm 2 => F ![(coordVec 2, 0), (0, 1)]) h
  simp only [ofParts_apply, hymLift_apply, fluxField_apply, hodge_flux, flat_apply] at k
  have z : flux (coordVec 2) ![coordVec 2, 0] = 0 :=
    (flux (coordVec 2)).map_coord_zero 1 rfl
  simp [z, coordVec] at k
  norm_num at k

/-- **Accepted**: the lift of the hyperbolic vacuum field `(x, y, -2z)` is the curvature of a
`τ`-independent connection form on `ℝ³ × ℝ`. -/
theorem hyperbolic_connection :
    ∃ (A : Space → Form 1) (φ : Space → ℝ), ContDiffOn ℝ 2 A Set.univ ∧
      ContDiffOn ℝ 2 φ Set.univ ∧ ∀ x ∈ (Set.univ : Set Space), ∀ τ : ℝ,
        extDeriv (liftConnection A φ) (x, τ) =
          hymLift (fluxField fun y => hyperbolicField y) (x, τ) :=
  hyperbolic_vacuumForm.exists_liftConnection (starConvex_univ (0 : Space))

/-- The same with the explicit scalar potential `p = (x² + y²)/2 - z²`: the scalar part of the
connection form is `-p dτ`. -/
theorem hyperbolic_connection_explicit_scalar :
    ∃ A : Space → Form 1, ∀ (x : Space) (τ : ℝ),
      extDeriv (liftConnection A hyperbolicPotential) (x, τ) =
        hymLift (fluxField fun y => hyperbolicField y) (x, τ) := by
  obtain ⟨A, hA, -, hdA⟩ := hyperbolic_vacuumForm.exists_vectorPotential
    (starConvex_univ (0 : Space))
  refine ⟨A, fun x τ => ?_⟩
  have hφ : DifferentiableAt ℝ hyperbolicPotential x := by
    have hid : DifferentiableAt ℝ (fun t : Euclid3 => t) x := differentiableAt_id
    exact (hid.inner ℝ hyperbolicField.differentiableAt).const_mul _
  exact extDeriv_liftConnection_eq_hymLift
    ((hA.contDiffAt Filter.univ_mem).differentiableAt (by norm_num)) hφ
    (hdA x (Set.mem_univ x)) (hodge_hyperbolic x).symm τ

/-! ### 4. and 5. Minimality -/

/-- A smooth bump function at the origin of `ℝ³ × ℝ`: `1` on the ball of radius `1`, `0`
outside the ball of radius `2` (for the product norm). -/
def bump : ContDiffBump (0 : LiftSpace) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The perturbation `a = f dτ` of the connection, with `f` the bump function. -/
def bumpForm (p : LiftSpace) : LiftForm 1 := bump p • dTau

/-- The perturbation is smooth, in particular of class `C¹`. -/
theorem contDiff_bumpForm : ContDiff ℝ 1 bumpForm :=
  bump.contDiff.smul contDiff_const

/-- The perturbation has compact support. -/
theorem hasCompactSupport_bumpForm : HasCompactSupport bumpForm :=
  bump.hasCompactSupport.smul_right

/-- The curvature of the perturbation on the plane `(e₀, e_τ)` is the derivative of the bump
function in the direction `e₀`. -/
theorem extDeriv_bumpForm_apply (p : LiftSpace) :
    extDeriv bumpForm p ![(coordVec 0, 0), (0, 1)] = fderiv ℝ bump p (coordVec 0, 0) := by
  have hf : HasFDerivAt bump (fderiv ℝ bump p) p :=
    (bump.contDiff (n := 1)).differentiable one_ne_zero p |>.hasFDerivAt
  have h : HasFDerivAt bumpForm ((fderiv ℝ bump p).smulRight dTau) p := hf.smul_const dTau
  rw [TauCeti.extDeriv_apply_pair, h.fderiv]
  simp

/-- **The perturbation changes the curvature**: `da ≠ 0` at some point. Otherwise the bump
function would be constant along the line `t ↦ (t e₀, 0)`, but it is `1` at the origin and `0`
at distance `2`. -/
theorem exists_extDeriv_bumpForm_ne_zero : ∃ p, extDeriv bumpForm p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz (p : LiftSpace) : fderiv ℝ bump p (coordVec 0, 0) = 0 := by
    rw [← extDeriv_bumpForm_apply, hcon p]
    rfl
  have hdiff : Differentiable ℝ bump := (bump.contDiff (n := 1)).differentiable one_ne_zero
  let e : LiftSpace := (coordVec 0, 0)
  have hg (t : ℝ) : HasDerivAt (fun r : ℝ => bump (r • e)) 0 t := by
    have h1 : HasDerivAt (fun r : ℝ => r • e) ((1 : ℝ) • e) t := (hasDerivAt_id t).smul_const e
    have h2 := (hdiff (t • e)).hasFDerivAt.comp_hasDerivAt t h1
    rw [one_smul, hz] at h2
    exact h2
  have hconst := is_const_of_deriv_eq_zero (f := fun r : ℝ => bump (r • e))
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 0 2
  have h0 : bump ((0 : ℝ) • e) = 1 := by
    rw [zero_smul]
    exact bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)
  have hn : ‖e‖ = 1 := by
    simp [e, Prod.norm_def, coordVec]
  have h2 : bump ((2 : ℝ) • e) = 0 := by
    apply bump.zero_of_le_dist
    rw [dist_zero_right, norm_smul, hn]
    simp [bump]
  simp only [h0, h2] at hconst
  exact one_ne_zero hconst

/-- **Minimality, strict instance.** For the lift `ℱ` of the hyperbolic vacuum field and the
perturbation `a = f dτ`, the change of energy is strictly positive:
`∫ (|ℱ + da|² - |ℱ|²) > 0`. The integrand is integrable although `|ℱ|²` is not. -/
theorem hyperbolic_energy_bump_pos :
    0 < ∫ p, (liftInner (hymLift (fluxField fun y => hyperbolicField y) p + extDeriv bumpForm p)
        (hymLift (fluxField fun y => hyperbolicField y) p + extDeriv bumpForm p) -
      liftInner (hymLift (fluxField fun y => hyperbolicField y) p)
        (hymLift (fluxField fun y => hyperbolicField y) p)) := by
  have hs : tsupport bumpForm ⊆ (Set.univ : Set Space) ×ˢ (Set.univ : Set ℝ) := by
    rw [Set.univ_prod_univ]
    exact Set.subset_univ _
  have h0 := hyperbolic_vacuumForm.integral_energy_hymLift_perturbation_nonneg contDiff_bumpForm
    hasCompactSupport_bumpForm hs
  have h1 := hyperbolic_vacuumForm.integral_energy_hymLift_perturbation_eq_zero_iff
    contDiff_bumpForm hasCompactSupport_bumpForm hs
  obtain ⟨p, hp⟩ := exists_extDeriv_bumpForm_ne_zero
  exact lt_of_le_of_ne h0 fun h => hp (h1.1 h.symm p)

/-- **Minimality, degenerate instance**: for the zero perturbation the change of energy
vanishes. -/
theorem hyperbolic_energy_zero :
    ∫ p, (liftInner (hymLift (fluxField fun y => hyperbolicField y) p +
          extDeriv (fun _ : LiftSpace => (0 : LiftForm 1)) p)
        (hymLift (fluxField fun y => hyperbolicField y) p +
          extDeriv (fun _ : LiftSpace => (0 : LiftForm 1)) p) -
      liftInner (hymLift (fluxField fun y => hyperbolicField y) p)
        (hymLift (fluxField fun y => hyperbolicField y) p)) = 0 := by
  have hs : tsupport (fun _ : LiftSpace => (0 : LiftForm 1)) ⊆
      (Set.univ : Set Space) ×ˢ (Set.univ : Set ℝ) := by
    rw [Set.univ_prod_univ]
    exact Set.subset_univ _
  have hc : HasCompactSupport (fun _ : LiftSpace => (0 : LiftForm 1)) :=
    HasCompactSupport.zero
  refine (hyperbolic_vacuumForm.integral_energy_hymLift_perturbation_eq_zero_iff
    contDiff_const hc hs).2 fun p => ?_
  exact image_eq_zero_of_notMem_tsupport fun h => by
    have := TauCeti.tsupport_extDeriv_subset h
    simp [tsupport] at this

end PlasmaLean.Sanity.FormHYMEnergy
