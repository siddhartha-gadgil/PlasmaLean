/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevFluxGeometry
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Change of variables and the coarea formula for the reactor Solov'ev plasma

`SolovevFluxGeometry` and `SolovevMercierCertified` left one modelling link stated but not
proved: that the coordinate volume `volS` is the Lebesgue volume (a change of variables with the
Jacobian `SolovevMercierCertified.jacobian_eq`), and the coarea formula
`d/ds ∫_{s' ≤ s} f dx = ∮_s f dS/|∇s|` identifying `V'`, `V' g`, `V' h` with derivatives of
volume integrals. This module proves both, with Mathlib's change-of-variables theorem
(`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) and Fubini/Tonelli.

## Coordinates

`cyl σ t φ = (R cos φ, R sin φ, z)`, `R = √(L² + 2σ sin t)`, `z = √2 σ cos t/R` (`L = 10`):
the meridian curve `SolovevMercierCertified.surfPt` rotated by the toroidal angle (`cyl_zero`).
`coordMap p = cyl (p 0) (p 1) (p 2)` on `Space`; box `coordDom σ₀ = (0, σ₀] × (-π, π] × (-π, π]`.

## Results

* **(a)** `injOn_coordMap`, `image_coordMap`: for `0 ≤ σ₀ ≤ 25` the map is injective on the box
  (explicit inverse `coordInv` via `Complex.arg`) and its image is the shell
  `0 < ψ̃ ≤ σ₀²`, i.e. `{ψ̃ ≤ σ₀²}` minus the magnetic axis, which is a null set
  (`volume_axisSet`).
* **(b)** `hasFDerivAt_coordMap`, `coordDeriv_det`: the Fréchet derivative is the explicit
  Jacobian matrix and `det = R · (√2 σ/R²) = √2 σ/R` (`jac`), from `jacobian_eq`.
* **(c)** `volume_shell`, `volume_label_le`: `vol{s' ≤ s} = volS(σ(s))` (Lebesgue measure);
  `hasDerivAt_volume_label`: `d/ds vol{s' ≤ s} = V'(s)`. `integral_shell`,
  `integral_label_le`: `∫_{s' ≤ s} f dx = ∫_{box} f(x(σ,t,φ)) √2σ/R`.
* **Coarea formula** `hasDerivAt_integral_label`: for continuous `f`,
  `d/ds ∫_{s' ≤ s} f dx = coareaInt f s = (√2 ψ̃_b/2) ∫∫ f(x)/R dt dφ`; for axisymmetric `f`
  this is `SolovevFluxGeometry.surfInt f s` (`hasDerivAt_integral_label_surfInt`), which is
  `∮ f dS/|∇s|` by `SolovevFluxGeometry.surfInt_eq_area`.
* `solovevFluxGeometry_coarea`: `V' = d/ds vol`, `V' g = d/ds ∫ |∇s|²`, `V' h = d/ds ∫ Δs`
  for the actual geometry `solovevFluxGeometry`, on every surface `0 < s ≤ 1`;
  `solovev_one_plasma_actual_coarea` bundles this with `solovev_one_plasma_actual`.

## Scope

All integrals are Lebesgue integrals over subsets of `Space = ℝ³`; nothing about the
transport model itself changes. `Axisymmetric f` asks `f(x(σ,t,φ)) = f(x(σ,t,0))`; it holds for
every function of `(R², z)` (`axisymmetric_of_R2z`), in particular for `|∇s|²` and `Δs`.
For non-axisymmetric `f` the formula keeps the `φ`-integral (`coareaInt`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevCoarea

open Real Set MeasureTheory WithLp
open PlasmaLean.Fields PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevMercier
open PlasmaLean.Design.SolovevMercierCertified (surfPt surfPt_on_surface jacobian_eq RS_pos')

/-- Coordinate projection `p ↦ p i` as a continuous linear map. -/
@[expose] def pr (i : Fin 3) : Space →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i

/-- The point with Solov'ev coordinates `(σ, t, φ)`: `(R cos φ, R sin φ, z)` with the meridian
curve `R = √(L² + 2σ sin t)`, `z = √2 σ cos t/R` of `SolovevMercierCertified.surfPt`. -/
@[expose] def cyl (σ t φ : ℝ) : Space :=
  toLp 2 ![RS 10 σ t * Real.cos φ, RS 10 σ t * Real.sin φ, zS 10 σ t]

/-- The coordinate map on `Space`: `p = (σ, t, φ) ↦ x(σ, t, φ)`. -/
@[expose] def coordMap (p : Space) : Space := cyl (p 0) (p 1) (p 2)

/-- `∂_σ z` of the meridian curve (as in `SolovevMercierCertified.jacobian_eq`). -/
@[expose] def zσ (σ t : ℝ) : ℝ :=
  (√2 * Real.cos t * RS 10 σ t - √2 * σ * Real.cos t * (Real.sin t / RS 10 σ t)) / RS 10 σ t ^ 2

/-- `∂_t z` of the meridian curve (as in `SolovevMercierCertified.jacobian_eq`). -/
@[expose] def zt (σ t : ℝ) : ℝ :=
  (√2 * σ * -Real.sin t * RS 10 σ t - √2 * σ * Real.cos t * (σ * Real.cos t / RS 10 σ t)) /
    RS 10 σ t ^ 2

/-- The Jacobian matrix `∂x_i/∂(σ, t, φ)_j` of the coordinate map (actual partial derivatives,
proved in `hasFDerivAt_coordMap`). -/
@[expose] def jacMatrix (p : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sin (p 1) / RS 10 (p 0) (p 1) * Real.cos (p 2),
      p 0 * Real.cos (p 1) / RS 10 (p 0) (p 1) * Real.cos (p 2),
      -(RS 10 (p 0) (p 1) * Real.sin (p 2));
    Real.sin (p 1) / RS 10 (p 0) (p 1) * Real.sin (p 2),
      p 0 * Real.cos (p 1) / RS 10 (p 0) (p 1) * Real.sin (p 2),
      RS 10 (p 0) (p 1) * Real.cos (p 2);
    zσ (p 0) (p 1), zt (p 0) (p 1), 0]

/-- The derivative of the coordinate map at `p`, as a continuous linear map (`jacMatrix p`). -/
@[expose] def coordDeriv (p : Space) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (jacMatrix p))

/-- Components of the derivative: `(Dx · v)_i = Σ_j J_ij v_j`. -/
theorem coordDeriv_apply (p v : Space) (i : Fin 3) :
    coordDeriv p v i = ∑ j, jacMatrix p i j * v j := by
  simp [coordDeriv, Matrix.mulVec, dotProduct]

/-- Fréchet derivative of `p ↦ R(σ, t)` (`σ = p 0`, `t = p 1`), `|σ| < 45`. -/
theorem hasFDerivAt_RS {p : Space} (hσ : p 0 ∈ Ioo (-45 : ℝ) 45) :
    HasFDerivAt (fun p : Space => RS 10 (p 0) (p 1))
      ((Real.sin (p 1) / RS 10 (p 0) (p 1)) • pr 0 +
        (p 0 * Real.cos (p 1) / RS 10 (p 0) (p 1)) • pr 1) p := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0
  have h1 := (Real.hasDerivAt_sin (p 1)).comp_hasFDerivAt p
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1)
  have hu := ((h0.const_mul 2).mul h1).const_add ((10:ℝ) ^ 2)
  have hpos := RS_pos' hσ (p 1)
  have hu0 : (10:ℝ) ^ 2 + 2 * p 0 * Real.sin (p 1) ≠ 0 := by
    have := SolovevMercierCertified.uS_ge hσ (p 1); unfold uS at this; linarith
  have h := hu.sqrt (by simpa [mul_assoc] using hu0)
  refine h.congr_fderiv ?_
  have hRS : √(10 ^ 2 + 2 * p 0 * Real.sin (p 1)) = RS 10 (p 0) (p 1) := rfl
  ext v
  simp only [Fin.isValue, Pi.mul_apply, Function.comp_apply, one_div, mul_inv_rev, smul_add,
    add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul,
    pr]
  rw [hRS]
  field_simp
  ring

/-- Fréchet derivative of `p ↦ z(σ, t)`, `|σ| < 45`. -/
theorem hasFDerivAt_zS {p : Space} (hσ : p 0 ∈ Ioo (-45 : ℝ) 45) :
    HasFDerivAt (fun p : Space => zS 10 (p 0) (p 1))
      (zσ (p 0) (p 1) • pr 0 + zt (p 0) (p 1) • pr 1) p := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0
  have h1 := (Real.hasDerivAt_cos (p 1)).comp_hasFDerivAt p
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1)
  have hpos := RS_pos' hσ (p 1)
  have hinv := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt p (hasFDerivAt_RS hσ)
  have h := ((h0.const_mul (√2)).mul h1).mul hinv
  have hf : (fun p : Space => zS 10 (p 0) (p 1)) =
      fun p => ((√2 * p 0) * Real.cos (p 1)) * (RS 10 (p 0) (p 1))⁻¹ := by
    funext q; simp [zS, div_eq_mul_inv]
  rw [hf]
  refine h.congr_fderiv ?_
  ext v
  simp [pr, zσ, zt]
  field_simp
  ring

/-- **(b) The coordinate map is differentiable** with derivative `coordDeriv p` (the matrix
`jacMatrix p`) wherever `|σ| < 45`. -/
theorem hasFDerivAt_coordMap {p : Space} (hσ : p 0 ∈ Ioo (-45 : ℝ) 45) :
    HasFDerivAt coordMap (coordDeriv p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
  fin_cases i
  · have h2 := (Real.hasDerivAt_cos (p 2)).comp_hasFDerivAt p
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2)
    refine ((hasFDerivAt_RS hσ).mul h2).congr_fderiv ?_
    ext v
    simp [coordDeriv_apply, Fin.sum_univ_three, jacMatrix, pr]
    ring
  · have h2 := (Real.hasDerivAt_sin (p 2)).comp_hasFDerivAt p
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2)
    refine ((hasFDerivAt_RS hσ).mul h2).congr_fderiv ?_
    ext v
    simp [coordDeriv_apply, Fin.sum_univ_three, jacMatrix, pr]
    ring
  · refine (hasFDerivAt_zS hσ).congr_fderiv ?_
    ext v
    simp [coordDeriv_apply, Fin.sum_univ_three, jacMatrix, pr]

/-- The `3 × 3` determinant expansion used in `coordDeriv_det`. -/
theorem det_alg (a b cz d R s c : ℝ) :
    a * c * (b * s) * 0 - a * c * (R * c) * d - b * c * (a * s) * 0 + b * c * (R * c) * cz +
      -(R * s) * (a * s) * d - -(R * s) * (b * s) * cz =
      -R * (s ^ 2 + c ^ 2) * (a * d - b * cz) := by
  ring

/-- The Jacobian value `√2 σ / R`. -/
@[expose] def jac (σ t : ℝ) : ℝ := √2 * σ / RS 10 σ t

/-- **(b) Jacobian determinant**: `det Dx = R · (√2 σ/R²) = √2 σ/R` (from the 2-D Jacobian
`SolovevMercierCertified.jacobian_eq` and `cos²φ + sin²φ = 1`). -/
theorem coordDeriv_det {p : Space} (hσ : 0 < p 0) (h25 : p 0 ≤ 25) :
    (coordDeriv p).det = jac (p 0) (p 1) := by
  rw [ContinuousLinearMap.det, coordDeriv, LinearMap.coe_toContinuousLinearMap,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_fin_three]
  have key := (jacobian_eq hσ h25 (p 1)).2.2.2.2
  have hR := SolovevMercierCertified.RS_pos_s hσ h25 (p 1)
  have hφ := Real.sin_sq_add_cos_sq (p 2)
  simp only [jacMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  set R := RS 10 (p 0) (p 1)
  have e : zσ (p 0) (p 1) = (√2 * Real.cos (p 1) * R -
      √2 * p 0 * Real.cos (p 1) * (Real.sin (p 1) / R)) / R ^ 2 := rfl
  have e' : zt (p 0) (p 1) = (√2 * p 0 * -Real.sin (p 1) * R -
      √2 * p 0 * Real.cos (p 1) * (p 0 * Real.cos (p 1) / R)) / R ^ 2 := rfl
  rw [e, e']
  unfold jac
  rw [det_alg, hφ, key]
  field_simp
  exact (div_self hR.ne').symm


/-! ## Injectivity and image -/

/-- The coordinate box `σ ∈ (0, σ₀]`, `t ∈ (-π, π]`, `φ ∈ (-π, π]`. -/
@[expose] def coordDom (σ₀ : ℝ) : Set Space :=
  {p | p 0 ∈ Ioc 0 σ₀ ∧ p 1 ∈ Ioc (-π) π ∧ p 2 ∈ Ioc (-π) π}

/-- The plasma shell `0 < ψ̃ ≤ σ₀²` (the region `ψ̃ ≤ σ₀²` minus the magnetic axis). -/
@[expose] def shell (σ₀ : ℝ) : Set Space := {x | 0 < psiT 10 x ∧ psiT 10 x ≤ σ₀ ^ 2}

/-- Major radius `R = √(x₀² + x₁²)`. -/
@[expose] def Rof (x : Space) : ℝ := √(R2 x)

/-- Toroidal angle `φ = arg(x₀ + i x₁) ∈ (-π, π]`. -/
@[expose] def phiOf (x : Space) : ℝ := Complex.arg ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)

/-- Mercier radius `σ = √ψ̃`. -/
@[expose] def sigOf (x : Space) : ℝ := √(psiT 10 x)

/-- Poloidal angle `t = arg(R z/√2 + i (R² - L²)/2) ∈ (-π, π]` (so `σ cos t = R z/√2`,
`σ sin t = (R² - L²)/2`). -/
@[expose] def tOf (x : Space) : ℝ :=
  Complex.arg (((Rof x * x 2 / √2 : ℝ) : ℂ) + (((R2 x - 10 ^ 2) / 2 : ℝ) : ℂ) * Complex.I)

/-- The explicit inverse `x ↦ (σ, t, φ)` of the coordinate map. -/
@[expose] def coordInv (x : Space) : Space := toLp 2 ![sigOf x, tOf x, phiOf x]

/-- First Cartesian coordinate of the coordinate point. -/
@[simp] theorem cyl_0 (σ t φ : ℝ) : cyl σ t φ 0 = RS 10 σ t * Real.cos φ := by simp [cyl]
/-- Second Cartesian coordinate of the coordinate point. -/
@[simp] theorem cyl_1 (σ t φ : ℝ) : cyl σ t φ 1 = RS 10 σ t * Real.sin φ := by simp [cyl]
/-- Third Cartesian coordinate of the coordinate point. -/
@[simp] theorem cyl_2 (σ t φ : ℝ) : cyl σ t φ 2 = zS 10 σ t := by simp [cyl]

/-- `x₀² + x₁² = R²` at the coordinate point. -/
theorem R2_cyl (σ t φ : ℝ) : R2 (cyl σ t φ) = RS 10 σ t ^ 2 := by
  simp only [R2, cyl_0, cyl_1]
  linear_combination RS 10 σ t ^ 2 * Real.cos_sq_add_sin_sq φ

/-- The coordinate point lies on the flux surface `ψ̃ = σ²`. -/
theorem psiT_cyl {σ : ℝ} (h0 : 0 ≤ σ) (h1 : 2 * σ < 10 ^ 2) (t φ : ℝ) :
    psiT 10 (cyl σ t φ) = σ ^ 2 := by
  have h := surfPt_on_surface h0 h1 t
  unfold psiT at h ⊢
  rw [SolovevMercierCertified.R2_surfPt, SolovevMercierCertified.surfPt_2] at h
  rw [R2_cyl, cyl_2]
  exact h

/-- First component of the inverse map. -/
@[simp] theorem coordInv_0 (x : Space) : coordInv x 0 = sigOf x := by simp [coordInv]
/-- Second component of the inverse map. -/
@[simp] theorem coordInv_1 (x : Space) : coordInv x 1 = tOf x := by simp [coordInv]
/-- Third component of the inverse map. -/
@[simp] theorem coordInv_2 (x : Space) : coordInv x 2 = phiOf x := by simp [coordInv]

/-- `coordInv` is a left inverse of `coordMap` on the coordinate box (`σ₀ ≤ 25`). -/
theorem coordInv_coordMap {σ₀ : ℝ} (hσ₀ : σ₀ ≤ 25) {p : Space} (hp : p ∈ coordDom σ₀) :
    coordInv (coordMap p) = p := by
  obtain ⟨⟨h0, h1⟩, ht, hφ⟩ := hp
  have hR := SolovevMercierCertified.RS_pos_s h0 (h1.trans hσ₀) (p 1)
  have hRu := SolovevMercierCertified.RS_sq_s h0 (h1.trans hσ₀) (p 1)
  have hRof : Rof (coordMap p) = RS 10 (p 0) (p 1) := by
    rw [Rof, coordMap, R2_cyl, Real.sqrt_sq hR.le]
  have h2 : √2 ≠ 0 := by positivity
  ext i
  fin_cases i
  · change sigOf (coordMap p) = p 0
    simp only [sigOf, coordMap]
    rw [psiT_cyl h0.le (by linarith) _ _, Real.sqrt_sq h0.le]
  · change tOf (coordMap p) = p 1
    simp only [tOf]
    have e : (((Rof (coordMap p) * coordMap p 2 / √2 : ℝ) : ℂ) +
        (((R2 (coordMap p) - 10 ^ 2) / 2 : ℝ) : ℂ) * Complex.I) =
        ((p 0 : ℝ) : ℂ) * (Complex.cos (p 1) + Complex.sin (p 1) * Complex.I) := by
      rw [hRof, coordMap, R2_cyl, cyl_2, hRu]
      unfold zS
      apply Complex.ext <;> simp <;> norm_num <;> field_simp
    rw [e, Complex.arg_mul_cos_add_sin_mul_I h0 ht]
  · change phiOf (coordMap p) = p 2
    simp only [phiOf]
    have e : ((coordMap p 0 : ℝ) : ℂ) + ((coordMap p 1 : ℝ) : ℂ) * Complex.I =
        ((RS 10 (p 0) (p 1) : ℝ) : ℂ) * (Complex.cos (p 2) + Complex.sin (p 2) * Complex.I) := by
      simp only [coordMap, cyl_0, cyl_1]
      apply Complex.ext <;> simp
    rw [e, Complex.arg_mul_cos_add_sin_mul_I hR hφ]


/-- `R² ≥ 0`. -/
theorem R2_nonneg (x : Space) : 0 ≤ R2 x := by unfold R2; positivity

/-- In the shell (`σ₀ ≤ 25`), the major radius is positive. -/
theorem R2_pos_of_shell {σ₀ : ℝ} (hσ₀ : σ₀ ≤ 25) (h0 : 0 ≤ σ₀) {x : Space} (hx : x ∈ shell σ₀) :
    0 < R2 x := by
  rcases (R2_nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    have := hx.2
    unfold psiT at this
    rw [← h] at this
    nlinarith

/-- `coordInv` maps the shell into the coordinate box. -/
theorem coordInv_mem {σ₀ : ℝ} (h0 : 0 ≤ σ₀) {x : Space} (hx : x ∈ shell σ₀) :
    coordInv x ∈ coordDom σ₀ := by
  refine ⟨⟨?_, ?_⟩, ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩⟩
  · rw [coordInv_0]; exact Real.sqrt_pos.2 hx.1
  · rw [coordInv_0, sigOf, ← Real.sqrt_sq h0]; exact Real.sqrt_le_sqrt hx.2

/-- `coordInv` is a right inverse of `coordMap` on the shell. -/
theorem coordMap_coordInv {σ₀ : ℝ} (hσ₀ : σ₀ ≤ 25) (h0 : 0 ≤ σ₀) {x : Space}
    (hx : x ∈ shell σ₀) : coordMap (coordInv x) = x := by
  have hR2 := R2_pos_of_shell hσ₀ h0 hx
  have hRof : 0 < Rof x := Real.sqrt_pos.2 hR2
  have hRsq : Rof x ^ 2 = R2 x := Real.sq_sqrt hR2.le
  set σ := sigOf x with hσdef
  set t := tOf x with htdef
  have hσsq : σ ^ 2 = psiT 10 x := Real.sq_sqrt hx.1.le
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h20 : 0 < √2 := by positivity
  set u := Rof x * x 2 / √2
  set w := (R2 x - 10 ^ 2) / 2
  have hnorm : ‖((u : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I‖ = σ := by
    rw [Complex.norm_add_mul_I, hσdef, sigOf]
    congr 1
    simp only [u, w, psiT]
    rw [div_pow, mul_pow, h2, hRsq]
    ring
  have hc : σ * Real.cos t = u := by
    have := Complex.norm_mul_cos_arg (((u : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I)
    have hre : (((u : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I).re = u := by simp
    rw [hnorm, hre] at this
    exact this
  have hs : σ * Real.sin t = w := by
    have := Complex.norm_mul_sin_arg (((u : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I)
    have him : (((u : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I).im = w := by simp
    rw [hnorm, him] at this
    exact this
  have hRS : RS 10 σ t = Rof x := by
    unfold RS uS Rof
    congr 1
    rw [mul_assoc, hs]
    simp only [w]
    ring
  have hnorm2 : ‖((x 0 : ℝ) : ℂ) + ((x 1 : ℝ) : ℂ) * Complex.I‖ = Rof x := by
    rw [Complex.norm_add_mul_I]; rfl
  ext i
  fin_cases i
  · change RS 10 σ t * Real.cos (phiOf x) = x 0
    have := Complex.norm_mul_cos_arg (((x 0 : ℝ) : ℂ) + ((x 1 : ℝ) : ℂ) * Complex.I)
    rw [hnorm2] at this
    rw [hRS, phiOf]
    simpa using this
  · change RS 10 σ t * Real.sin (phiOf x) = x 1
    have := Complex.norm_mul_sin_arg (((x 0 : ℝ) : ℂ) + ((x 1 : ℝ) : ℂ) * Complex.I)
    rw [hnorm2] at this
    rw [hRS, phiOf]
    simpa using this
  · change zS 10 σ t = x 2
    unfold zS
    rw [hRS, mul_assoc, hc]
    simp only [u]
    field_simp

/-- **(a) Image**: the coordinate box is mapped onto the shell `0 < ψ̃ ≤ σ₀²`. -/
theorem image_coordMap {σ₀ : ℝ} (h0 : 0 ≤ σ₀) (hσ₀ : σ₀ ≤ 25) :
    coordMap '' coordDom σ₀ = shell σ₀ := by
  ext x
  constructor
  · rintro ⟨p, ⟨⟨hp0, hp1⟩, -, -⟩, rfl⟩
    refine ⟨?_, ?_⟩ <;> rw [coordMap, psiT_cyl hp0.le (by linarith) _ _]
    · positivity
    · exact pow_le_pow_left₀ hp0.le hp1 2
  · intro hx
    exact ⟨coordInv x, coordInv_mem h0 hx, coordMap_coordInv hσ₀ h0 hx⟩

/-- **(a) Injectivity** on the coordinate box. -/
theorem injOn_coordMap {σ₀ : ℝ} (hσ₀ : σ₀ ≤ 25) : InjOn coordMap (coordDom σ₀) := by
  intro p hp q hq h
  rw [← coordInv_coordMap hσ₀ hp, h, coordInv_coordMap hσ₀ hq]


/-! ## Volume -/

/-- The coordinate box is measurable. -/
theorem measurableSet_coordDom (σ₀ : ℝ) : MeasurableSet (coordDom σ₀) := by
  have hc : ∀ i : Fin 3, Measurable fun p : Space => p i := fun i =>
    (PiLp.continuous_apply 2 _ i).measurable
  exact ((hc 0) measurableSet_Ioc).inter
    (((hc 1) measurableSet_Ioc).inter ((hc 2) measurableSet_Ioc))

/-- Derivative of the coordinate map within the box. -/
theorem hasFDerivWithinAt_coordMap {σ₀ : ℝ} (hσ₀ : σ₀ ≤ 25) {p : Space} (hp : p ∈ coordDom σ₀) :
    HasFDerivWithinAt coordMap (coordDeriv p) (coordDom σ₀) p :=
  (hasFDerivAt_coordMap ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩).hasFDerivWithinAt

/-- The identification `Space ≃ ℝ × ℝ × ℝ`, `p ↦ (p 0, p 1, p 2)`. -/
@[expose] def toTriple : Space ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow))

/-- `toTriple p = (p 0, p 1, p 2)`. -/
theorem toTriple_apply (p : Space) : toTriple p = (p 0, p 1, p 2) := rfl

/-- `toTriple` maps Lebesgue measure on `Space` to Lebesgue measure on `ℝ × ℝ × ℝ`. -/
theorem measurePreserving_toTriple : MeasurePreserving toTriple := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  exact (h3.comp h2).comp h1

/-- Measurability of the Jacobian. -/
theorem measurable_jac : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (jac q.1 q.2) := by
  unfold jac RS uS; fun_prop

/-- Continuity in `t` of the Jacobian for `|σ| < 45`. -/
theorem continuous_jac {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) : Continuous (jac σ) :=
  continuous_const.div continuous_RS fun t => (RS_pos' hσ t).ne'

/-- `∫_{-π}^{π} √2 σ/R dt = √2 σ P(σ)`. -/
theorem integral_jac (σ : ℝ) :
    ∫ t in Ioc (-π) π, jac σ t = √2 * σ * SolovevMercierCertified.Pint σ := by
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), SolovevMercierCertified.Pint,
    ← intervalIntegral.integral_const_mul]
  unfold jac
  simp [div_eq_mul_inv]

/-- The Jacobian integrated over the coordinate box (Tonelli) is `volS σ₀`. -/
theorem lintegral_box {σ₀ : ℝ} (h0 : 0 ≤ σ₀) (hσ₀ : σ₀ ≤ 25) :
    ∫⁻ p in coordDom σ₀, ENNReal.ofReal (jac (p 0) (p 1)) =
      ENNReal.ofReal (SolovevMercierCertified.volS σ₀) := by
  have hD : coordDom σ₀ = toTriple ⁻¹' (Ioc 0 σ₀ ×ˢ (Ioc (-π) π ×ˢ Ioc (-π) π)) := by
    ext p; simp [coordDom, toTriple_apply]
  rw [hD]
  refine (measurePreserving_toTriple.setLIntegral_comp_preimage_emb toTriple.measurableEmbedding
    (fun q : ℝ × ℝ × ℝ => ENNReal.ofReal (jac q.1 q.2.1)) _).trans ?_
  have hm : Measurable fun q : ℝ × ℝ × ℝ => ENNReal.ofReal (jac q.1 q.2.1) :=
    measurable_jac.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
  have hpi : (0 : ℝ) ≤ π - -π := by linarith [Real.pi_pos]
  have inner : EqOn
      (fun x => ∫⁻ y in Ioc (-π) π ×ˢ Ioc (-π) π, ENNReal.ofReal (jac (x, y).1 (x, y).2.1))
      (fun x => ENNReal.ofReal (2 * π * √2 * (x * SolovevMercierCertified.Pint x))) (Ioc 0 σ₀) := by
    intro x hx
    have hxI : x ∈ Ioo (-45 : ℝ) 45 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hm2 : Measurable fun y : ℝ × ℝ => ENNReal.ofReal (jac x y.1) :=
      measurable_jac.comp (measurable_const.prodMk measurable_fst)
    simp only
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hm2.aemeasurable]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioc]
    rw [lintegral_mul_const _ ((continuous_jac hxI).measurable.ennreal_ofReal),
      ← ofReal_integral_eq_lintegral_ofReal
        ((continuous_jac hxI).integrableOn_Ioc) ?_, integral_jac x, ← ENNReal.ofReal_mul
        (by have := (SolovevMercierCertified.Pint_pos hxI); have := hx.1; positivity)]
    · congr 1; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
      have := RS_pos' hxI t; have := hx.1; unfold jac; positivity
  rw [setLIntegral_congr_fun measurableSet_Ioc inner]
  have hcont : ContinuousOn (fun x => 2 * π * √2 * (x * SolovevMercierCertified.Pint x))
      (Icc 0 σ₀) :=
    (continuousOn_const.mul (continuousOn_id.mul SolovevMercierCertified.continuousOn_Pint)).mono
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [← ofReal_integral_eq_lintegral_ofReal ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self)]
  · rw [SolovevMercierCertified.volS, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le h0]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxI : x ∈ Ioo (-45 : ℝ) 45 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have := SolovevMercierCertified.Pint_pos hxI; have := hx.1
    positivity

/-- **(c) Volume of the shell** `0 < ψ̃ ≤ σ₀²` equals `volS σ₀`. -/
theorem volume_shell {σ₀ : ℝ} (h0 : 0 ≤ σ₀) (hσ₀ : σ₀ ≤ 25) :
    volume (shell σ₀) = ENNReal.ofReal (SolovevMercierCertified.volS σ₀) := by
  rw [← image_coordMap h0 hσ₀, ← setLIntegral_one,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_coordDom σ₀)
      (fun p hp => hasFDerivWithinAt_coordMap hσ₀ hp) (injOn_coordMap hσ₀), ← lintegral_box h0 hσ₀]
  refine setLIntegral_congr_fun (measurableSet_coordDom σ₀) fun p hp => ?_
  have hp0 := hp.1.1
  have hp1 := hp.1.2
  rw [coordDeriv_det hp0 (by linarith), mul_one, abs_of_nonneg]
  have := RS_pos' (σ := p 0) ⟨by linarith, by linarith⟩ (p 1)
  unfold jac; positivity


/-! ## The magnetic axis is null; the plasma `{s ≤ s₀}` -/

open PlasmaLean.Design.SolovevOnePlasma (psiB psiB_pos label)
open PlasmaLean.Design.SolovevFluxGeometry (sig sig_sq sig_nonneg sig_pos psiB_eq Vp surfInt)

/-- The magnetic axis `ψ̃ = 0` (the circle `R = L`, `z = 0`). -/
@[expose] def axisSet : Set Space := {x | psiT 10 x = 0}

/-- `ψ̃ ≥ 0`. -/
theorem psiT_nonneg (x : Space) : 0 ≤ psiT 10 x := by
  unfold psiT; have := R2_nonneg x; positivity

/-- **The magnetic axis is a Lebesgue null set** (it lies in the plane `z = 0`). -/
theorem volume_axisSet : volume axisSet = 0 := by
  let S : Submodule ℝ Space := LinearMap.ker (pr 2 : Space →ₗ[ℝ] ℝ)
  have hS : S ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single 2 (1 : ℝ) : Space) ∈ S := h ▸ Submodule.mem_top
    simp [S, pr] at this
  refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_submodule volume S hS)
  have hx' : psiT 10 x = 0 := hx
  unfold psiT at hx'
  have h1 : 0 ≤ R2 x * x 2 ^ 2 / 2 := by have := R2_nonneg x; positivity
  have h2 : 0 ≤ (R2 x - 10 ^ 2) ^ 2 / 4 := by positivity
  have hR : R2 x = 10 ^ 2 := by nlinarith
  have hz : x 2 ^ 2 = 0 := by rw [hR] at h1 hx'; nlinarith
  change pr 2 x = 0
  simpa [pr] using hz

/-- `sig s ≤ 25` iff `s ≤ 12/11`. -/
theorem sig_le_25 {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 12 / 11) : sig s ≤ 25 := by
  have h := sig_sq hs
  have := sig_nonneg s
  rw [psiB_eq] at h
  nlinarith

/-- The plasma `{label ≤ s}` is the shell `0 < ψ̃ ≤ σ(s)²` plus the axis. -/
theorem label_set_eq {s : ℝ} (hs : 0 ≤ s) :
    {x : Space | label x ≤ s} = shell (sig s) ∪ axisSet := by
  ext x
  simp only [mem_ofPred_eq, label, shell, axisSet, mem_union, sig_sq hs]
  rw [div_le_iff₀ psiB_pos]
  have := psiT_nonneg x
  constructor
  · intro h
    rcases this.lt_or_eq with h' | h'
    · exact Or.inl ⟨h', by linarith⟩
    · exact Or.inr h'.symm
  · rintro (h | h)
    · linarith [h.2]
    · rw [h]; exact mul_nonneg hs psiB_pos.le

/-- The plasma `{s' ≤ s}` and the shell agree up to a null set. -/
theorem label_set_ae_eq {s : ℝ} (hs : 0 ≤ s) :
    {x : Space | label x ≤ s} =ᵐ[volume] shell (sig s) := by
  rw [label_set_eq hs]
  exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 volume_axisSet)

/-- **(c) The Lebesgue volume of the plasma `{s' ≤ s}` is `volS(σ(s))`**. -/
theorem volume_label_le {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 12 / 11) :
    volume {x : Space | label x ≤ s} = ENNReal.ofReal (SolovevMercierCertified.volS (sig s)) := by
  rw [measure_congr (label_set_ae_eq hs), volume_shell (sig_nonneg s) (sig_le_25 hs hs')]

/-- `volS σ ≥ 0` for `0 ≤ σ ≤ 25`. -/
theorem volS_nonneg {σ : ℝ} (h0 : 0 ≤ σ) (h25 : σ ≤ 25) : 0 ≤ SolovevMercierCertified.volS σ := by
  unfold SolovevMercierCertified.volS
  have : 0 ≤ ∫ x in (0 : ℝ)..σ, x * SolovevMercierCertified.Pint x :=
    intervalIntegral.integral_nonneg h0 fun x hx => mul_nonneg hx.1
      (SolovevMercierCertified.Pint_pos ⟨by linarith [hx.1], by linarith [hx.2]⟩).le
  positivity

/-- Real-valued plasma volume. -/
theorem volumeReal_label_le {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 12 / 11) :
    (volume {x : Space | label x ≤ s}).toReal = SolovevMercierCertified.volS (sig s) := by
  rw [volume_label_le hs hs', ENNReal.toReal_ofReal (volS_nonneg (sig_nonneg s) (sig_le_25 hs hs'))]

/-- **`V'(s)` is the derivative of the Lebesgue volume of `{s' ≤ s}`**. -/
theorem hasDerivAt_volume_label {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    HasDerivAt (fun s => (volume {x : Space | label x ≤ s}).toReal) (Vp s) s := by
  refine (SolovevFluxGeometry.hasDerivAt_volume hs).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs.1 (by linarith [hs.2] : s < 12 / 11)] with x hx
  exact volumeReal_label_le hx.1.le hx.2.le

/-- **Change of variables** for integrals over the shell. -/
theorem integral_shell (f : Space → ℝ) {σ₀ : ℝ} (h0 : 0 ≤ σ₀) (hσ₀ : σ₀ ≤ 25) :
    ∫ x in shell σ₀, f x = ∫ p in coordDom σ₀, jac (p 0) (p 1) * f (coordMap p) := by
  rw [← image_coordMap h0 hσ₀, integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_coordDom σ₀) (fun p hp => hasFDerivWithinAt_coordMap hσ₀ hp)
    (injOn_coordMap hσ₀)]
  refine setIntegral_congr_fun (measurableSet_coordDom σ₀) fun p hp => ?_
  have hp0 := hp.1.1
  have hp1 := hp.1.2
  have := RS_pos' (σ := p 0) ⟨by linarith, by linarith⟩ (p 1)
  simp only [smul_eq_mul]
  rw [coordDeriv_det hp0 (by linarith), abs_of_nonneg (by unfold jac; positivity)]

/-- Change of variables for integrals over the plasma `{s' ≤ s}`. -/
theorem integral_label_le (f : Space → ℝ) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 12 / 11) :
    ∫ x in {x : Space | label x ≤ s}, f x =
      ∫ p in coordDom (sig s), jac (p 0) (p 1) * f (coordMap p) := by
  rw [setIntegral_congr_set (label_set_ae_eq hs), integral_shell f (sig_nonneg s)
    (sig_le_25 hs hs')]


/-! ## The coarea formula -/

/-- Clamp of `σ` to `[-30, 30]` (used only to get globally continuous integrands). -/
@[expose] def clamp (σ : ℝ) : ℝ := max (-30) (min σ 30)

/-- The clamp lies in `(-45, 45)`. -/
theorem clamp_mem (σ : ℝ) : clamp σ ∈ Ioo (-45 : ℝ) 45 := by
  unfold clamp; constructor
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · exact max_lt (by norm_num) (lt_of_le_of_lt (min_le_right _ _) (by norm_num))

/-- The clamp is the identity on `[0, 25]`. -/
theorem clamp_eq {σ : ℝ} (h0 : 0 ≤ σ) (h25 : σ ≤ 25) : clamp σ = σ := by
  unfold clamp; rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/-- The clamp is continuous. -/
theorem continuous_clamp : Continuous clamp := by unfold clamp; fun_prop

/-- `(σ, t, φ) ↦ x(clamp σ, t, φ)` is continuous. -/
theorem continuous_cyl_clamp : Continuous fun q : ℝ × ℝ × ℝ => cyl (clamp q.1) q.2.1 q.2.2 := by
  have hR : Continuous fun q : ℝ × ℝ × ℝ => RS 10 (clamp q.1) q.2.1 := by
    unfold RS uS; have := continuous_clamp; fun_prop
  have hz : Continuous fun q : ℝ × ℝ × ℝ => zS 10 (clamp q.1) q.2.1 := by
    unfold zS
    exact (by have := continuous_clamp; fun_prop : Continuous fun q : ℝ × ℝ × ℝ =>
      √2 * clamp q.1 * Real.cos q.2.1).div hR fun q => (RS_pos' (clamp_mem q.1) q.2.1).ne'
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact hR.mul (by fun_prop)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact hR.mul (by fun_prop)
  · simpa using hz


/-- Globally continuous version of the integrand `J · f ∘ x` (agrees with it for `0 ≤ σ ≤ 25`). -/
@[expose] def Gc (f : Space → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  jac (clamp q.1) q.2.1 * f (cyl (clamp q.1) q.2.1 q.2.2)

/-- `Gc f` is continuous for continuous `f`. -/
theorem continuous_Gc {f : Space → ℝ} (hf : Continuous f) : Continuous (Gc f) := by
  have hR : Continuous fun q : ℝ × ℝ × ℝ => RS 10 (clamp q.1) q.2.1 := by
    unfold RS uS; have := continuous_clamp; fun_prop
  have hj : Continuous fun q : ℝ × ℝ × ℝ => jac (clamp q.1) q.2.1 := by
    unfold jac
    exact (by have := continuous_clamp; fun_prop : Continuous fun q : ℝ × ℝ × ℝ =>
      √2 * clamp q.1).div hR fun q => (RS_pos' (clamp_mem q.1) q.2.1).ne'
  exact hj.mul (hf.comp continuous_cyl_clamp)

/-- `Φ(σ) = ∫∫ J f dt dφ` over the surface `σ` (with the clamp). -/
@[expose] def Phi (f : Space → ℝ) (σ : ℝ) : ℝ :=
  ∫ t in (-π)..π, ∫ φ in (-π)..π, Gc f (σ, t, φ)

/-- `Φ` is continuous for continuous `f` (parametric integrals). -/
theorem continuous_Phi {f : Space → ℝ} (hf : Continuous f) : Continuous (Phi f) := by
  have h1 : Continuous fun x : ℝ × ℝ => ∫ φ in (-π)..π, Gc f (x.1, x.2, φ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : ℝ × ℝ) φ => Gc f (x.1, x.2, φ))
      ((continuous_Gc hf).comp (by fun_prop)) _ _
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun σ t => ∫ φ in (-π)..π, Gc f (σ, t, φ)) (h1.comp (by fun_prop)) _ _

/-- **Fubini on the coordinate box**: `∫_{box} J f = ∫₀^{σ₀} Φ(σ) dσ`. -/
theorem integral_coordDom_eq {f : Space → ℝ} (hf : Continuous f) {σ₀ : ℝ} (h0 : 0 ≤ σ₀)
    (hσ₀ : σ₀ ≤ 25) :
    ∫ p in coordDom σ₀, jac (p 0) (p 1) * f (coordMap p) = ∫ σ in (0 : ℝ)..σ₀, Phi f σ := by
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  rw [setIntegral_congr_fun (measurableSet_coordDom σ₀) (g := fun p => Gc f (toTriple p))
    (fun p hp => by
      simp only [Gc, toTriple_apply, coordMap]
      rw [clamp_eq hp.1.1.le (hp.1.2.trans hσ₀)])]
  have hD : coordDom σ₀ = toTriple ⁻¹' (Ioc 0 σ₀ ×ˢ (Ioc (-π) π ×ˢ Ioc (-π) π)) := by
    ext p; simp [coordDom, toTriple_apply]
  rw [hD, measurePreserving_toTriple.setIntegral_preimage_emb toTriple.measurableEmbedding]
  have hint : IntegrableOn (Gc f) (Ioc 0 σ₀ ×ˢ (Ioc (-π) π ×ˢ Ioc (-π) π)) :=
    ((continuous_Gc hf).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).mono_set
      (prod_mono Ioc_subset_Icc_self (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint, intervalIntegral.integral_of_le h0]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  have hint2 : IntegrableOn (fun y : ℝ × ℝ => Gc f (x, y)) (Ioc (-π) π ×ˢ Ioc (-π) π) :=
    (((continuous_Gc hf).comp (Continuous.prodMk_right x)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [Measure.volume_eq_prod] at hint2
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint2, Phi, intervalIntegral.integral_of_le hpi]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [intervalIntegral.integral_of_le hpi]

/-- `∫_{s' ≤ s} f dx = ∫₀^{σ(s)} Φ(σ) dσ` for continuous `f`. -/
theorem integral_label_eq_Phi {f : Space → ℝ} (hf : Continuous f) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ 12 / 11) :
    ∫ x in {x : Space | label x ≤ s}, f x = ∫ σ in (0 : ℝ)..sig s, Phi f σ := by
  rw [integral_label_le f hs hs', integral_coordDom_eq hf (sig_nonneg s) (sig_le_25 hs hs')]

/-- The toroidally integrated surface integral `∮ f dS/|∇s|`:
`(√2 ψ̃_b/2) ∫∫ f(x(σ(s), t, φ))/R dt dφ`. -/
@[expose] def coareaInt (f : Space → ℝ) (s : ℝ) : ℝ :=
  √2 * psiB / 2 * ∫ t in (-π)..π, ∫ φ in (-π)..π, f (cyl (sig s) t φ) / RS 10 (sig s) t

/-- `Φ(σ) = √2 σ ∫∫ f(x)/R dt dφ` for `0 ≤ σ ≤ 25`. -/
theorem Phi_eq (f : Space → ℝ) {σ : ℝ} (h0 : 0 ≤ σ) (h25 : σ ≤ 25) :
    Phi f σ = √2 * σ * ∫ t in (-π)..π, ∫ φ in (-π)..π, f (cyl σ t φ) / RS 10 σ t := by
  unfold Phi Gc
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [clamp_eq h0 h25, jac]
  ring

/-- **Coarea formula** for the reactor Solov'ev plasma: for continuous `f`,
`d/ds ∫_{s' ≤ s} f dx = ∮_s f dS/|∇s|` (in the coordinates `(t, φ)`). -/
theorem hasDerivAt_integral_label {f : Space → ℝ} (hf : Continuous f) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    HasDerivAt (fun s => ∫ x in {x : Space | label x ≤ s}, f x) (coareaInt f s) s := by
  have hF := ((continuous_Phi hf).integral_hasStrictDerivAt 0 (sig s)).hasDerivAt
  have hσ := sig_pos hs.1
  have hsig : HasDerivAt sig (psiB / (2 * sig s)) s := by
    have h1 : HasDerivAt (fun s => psiB * s) psiB s := by
      simpa using (hasDerivAt_id s).const_mul psiB
    exact h1.sqrt (mul_pos psiB_pos hs.1).ne'
  refine ((hF.comp s hsig).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hs.1 (by linarith [hs.2] : s < 12 / 11)] with x hx
    exact integral_label_eq_Phi hf hx.1.le hx.2.le
  · rw [Phi_eq f hσ.le (sig_le_25 hs.1.le (by linarith [hs.2])), coareaInt]
    field_simp


/-! ## Axisymmetric integrands: the coarea integral is `surfInt` -/

/-- `f` is axisymmetric along the coordinate surfaces: `f(x(σ, t, φ)) = f(x(σ, t, 0))`. -/
@[expose] def Axisymmetric (f : Space → ℝ) : Prop := ∀ σ t φ, f (cyl σ t φ) = f (surfPt σ t)

/-- A function of `(R², z)` is axisymmetric. -/
theorem axisymmetric_of_R2z {f : Space → ℝ} (g : ℝ → ℝ → ℝ) (hf : ∀ x, f x = g (R2 x) (x 2)) :
    Axisymmetric f := fun σ t φ => by
  rw [hf, hf, R2_cyl, cyl_2, SolovevMercierCertified.R2_surfPt, SolovevMercierCertified.surfPt_2]

/-- For axisymmetric `f`, the coarea integral is `SolovevFluxGeometry.surfInt`. -/
theorem coareaInt_eq_surfInt {f : Space → ℝ} (hf : Axisymmetric f) (s : ℝ) :
    coareaInt f s = surfInt f s := by
  unfold coareaInt surfInt
  have e : ∀ t, ∫ φ in (-π)..π, f (cyl (sig s) t φ) / RS 10 (sig s) t =
      2 * π * (f (surfPt (sig s) t) / RS 10 (sig s) t) := fun t => by
    have hf' : ∀ φ, f (cyl (sig s) t φ) = f (surfPt (sig s) t) := fun φ => hf _ _ φ
    simp only [hf']
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **Coarea formula, axisymmetric form**: `d/ds ∫_{s' ≤ s} f dx = surfInt f s`
(`= ∮ f dS/|∇s|`, `SolovevFluxGeometry.surfInt_eq_area`). -/
theorem hasDerivAt_integral_label_surfInt {f : Space → ℝ} (hf : Continuous f)
    (hax : Axisymmetric f) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    HasDerivAt (fun s => ∫ x in {x : Space | label x ≤ s}, f x) (surfInt f s) s :=
  coareaInt_eq_surfInt hax s ▸ hasDerivAt_integral_label hf hs

/-- `R²` is continuous. -/
theorem continuous_R2 : Continuous R2 := by
  unfold R2
  have := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
  have := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  fun_prop

/-- `z` is continuous. -/
theorem continuous_x2 : Continuous fun x : Space => x 2 := PiLp.continuous_apply 2 _ 2

open PlasmaLean.Design.SolovevFluxGeometry (gradSqS lapS lapPsiT VG VH gS hS Vp_pos
  solovevFluxGeometry)

/-- `|∇s|² = (R²(z² + R² - L²)² + (R² z)²)/ψ̃_b²`. -/
theorem gradSqS_eq (x : Space) : gradSqS x =
    (R2 x * (x 2 ^ 2 + R2 x - 10 ^ 2) ^ 2 + (R2 x * x 2) ^ 2) / psiB ^ 2 := by
  unfold gradSqS
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [psiTGrad, R2]
  ring

/-- `|∇s|²` is continuous. -/
theorem continuous_gradSqS : Continuous gradSqS := by
  rw [show gradSqS = fun x => (R2 x * (x 2 ^ 2 + R2 x - 10 ^ 2) ^ 2 + (R2 x * x 2) ^ 2) / psiB ^ 2
    from funext gradSqS_eq]
  have := continuous_R2; have := continuous_x2; fun_prop

/-- `|∇s|²` is axisymmetric. -/
theorem axisymmetric_gradSqS : Axisymmetric gradSqS :=
  axisymmetric_of_R2z (fun r z => (r * (z ^ 2 + r - 10 ^ 2) ^ 2 + (r * z) ^ 2) / psiB ^ 2)
    gradSqS_eq

/-- `Δs` is continuous. -/
theorem continuous_lapS : Continuous lapS := by
  unfold lapS lapPsiT; have := continuous_R2; have := continuous_x2; fun_prop

/-- `Δs` is axisymmetric. -/
theorem axisymmetric_lapS : Axisymmetric lapS :=
  axisymmetric_of_R2z (fun r z => (2 * z ^ 2 + 5 * r - 2 * 10 ^ 2) / psiB) fun _ => rfl

/-- **The actual Solov'ev flux geometry is derived from Lebesgue integrals over the plasma**:
for `0 < s ≤ 1`,
* `V'(s) = d/ds vol{s' ≤ s}`,
* `V'(s) g(s) = d/ds ∫_{s' ≤ s} |∇s|² dx`,
* `V'(s) h(s) = d/ds ∫_{s' ≤ s} Δs dx`,
* and for every continuous axisymmetric `f`, `d/ds ∫_{s' ≤ s} f dx = surfInt f s`,
so `g = ⟨|∇s|²⟩`, `h = ⟨Δs⟩` are the flux-surface averages `(d/ds ∫ f)/(d/ds vol)`. -/
theorem solovevFluxGeometry_coarea {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    HasDerivAt (fun s => (volume {x : Space | label x ≤ s}).toReal)
      (solovevFluxGeometry.Vp s) s ∧
    HasDerivAt (fun s => ∫ x in {x : Space | label x ≤ s}, gradSqS x)
      (solovevFluxGeometry.Vp s * solovevFluxGeometry.g s) s ∧
    HasDerivAt (fun s => ∫ x in {x : Space | label x ≤ s}, lapS x)
      (solovevFluxGeometry.Vp s * solovevFluxGeometry.h s) s ∧
    (∀ f : Space → ℝ, Continuous f → Axisymmetric f →
      HasDerivAt (fun s => ∫ x in {x : Space | label x ≤ s}, f x) (surfInt f s) s) := by
  have hV := (Vp_pos hs.1.le (by linarith [hs.2])).ne'
  refine ⟨hasDerivAt_volume_label hs, ?_, ?_,
    fun f hf hax => hasDerivAt_integral_label_surfInt hf hax hs⟩
  · have e : solovevFluxGeometry.Vp s * solovevFluxGeometry.g s = surfInt gradSqS s := by
      change Vp s * (VG s / Vp s) = VG s
      field_simp
    rw [e]
    exact hasDerivAt_integral_label_surfInt continuous_gradSqS axisymmetric_gradSqS hs
  · have e : solovevFluxGeometry.Vp s * solovevFluxGeometry.h s = surfInt lapS s := by
      change Vp s * (VH s / Vp s) = VH s
      field_simp
    rw [e]
    exact hasDerivAt_integral_label_surfInt continuous_lapS axisymmetric_lapS hs


/-! ## Sanity checks -/

/-- At toroidal angle `0` the coordinate point is the meridian point `surfPt`. -/
theorem cyl_zero (σ t : ℝ) : cyl σ t 0 = surfPt σ t := by
  ext i; fin_cases i <;> simp [cyl, surfPt]

/-- `f = 1`: the coarea integral is `V'`. -/
theorem coareaInt_one (s : ℝ) : coareaInt (fun _ => 1) s = Vp s :=
  coareaInt_eq_surfInt (fun _ _ _ => rfl) s

/-- Degenerate case: the plasma `{s' ≤ 0}` (the magnetic axis) has volume zero. -/
theorem volume_label_le_zero : volume {x : Space | label x ≤ 0} = 0 := by
  rw [volume_label_le le_rfl (by norm_num), SolovevFluxGeometry.sig, mul_zero, Real.sqrt_zero,
    SolovevMercierCertified.volS, intervalIntegral.integral_same, mul_zero, ENNReal.ofReal_zero]

/-- The Jacobian is positive off the axis. -/
theorem jac_pos {σ t : ℝ} (h0 : 0 < σ) (h25 : σ ≤ 25) : 0 < jac σ t := by
  have := RS_pos' (σ := σ) ⟨by linarith, by linarith⟩ t
  unfold jac; positivity

/-! ## `solovev_one_plasma` on the actual geometry, with the coarea link -/

section actual

open PlasmaLean.Fusion PlasmaLean.Kinetic PlasmaLean.Design.SolovevOnePlasma
  PlasmaLean.Design.SolovevBand PlasmaLean.Design.SolovevAlpha PlasmaLean.Transport

/-- **`solovev_one_plasma_actual` with the geometry fully derived**: the conclusion of
`SolovevFluxGeometry.solovev_one_plasma_actual` together with `solovevFluxGeometry_coarea`
on every surface `0 < s ≤ 1`, i.e. the `V'`, `V' g`, `V' h` of the transport equation are the
`s`-derivatives of the Lebesgue volume and of the Lebesgue integrals of `|∇s|²` and `Δs` over
the plasma `{s' ≤ s}` (change of variables + coarea formula, proved here). -/
theorem solovev_one_plasma_actual_coarea {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    ((∀ x : Space, label x ≤ 1 →
      ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
        (ofLp (gradient (offsetPressure μ₀ 40000) x))) ∧
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
      e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → label (x 0) ≤ 3 / 11 →
      ∀ t, label (x t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ},
      8 / 5 ≤ χ₀ → χ₀ ≤ 33 / 20 → ∀ {Tedge : ℝ → ℝ} {u : RadialField},
      (∀ τ, 0 ≤ τ → ClassicalRadialSolution (solCoeffs solovevFluxGeometry sv χ₀) Tedge τ u) →
      (∀ s ∈ Icc (0 : ℝ) 1, Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ Tsup s) →
      (∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub s ≤ u.T s t ∧ u.T s t ≤ Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ x : Space, label x ≤ 1 → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤
          reactorPressure μ₀ x + 40000))) ∧
    (∀ s ∈ Ioc (0 : ℝ) 1,
      HasDerivAt (fun s => (volume {x : Space | label x ≤ s}).toReal)
        (solovevFluxGeometry.Vp s) s ∧
      HasDerivAt (fun s => ∫ x in {x : Space | label x ≤ s}, gradSqS x)
        (solovevFluxGeometry.Vp s * solovevFluxGeometry.g s) s ∧
      HasDerivAt (fun s => ∫ x in {x : Space | label x ≤ s}, lapS x)
        (solovevFluxGeometry.Vp s * solovevFluxGeometry.h s) s) :=
  ⟨SolovevFluxGeometry.solovev_one_plasma_actual hμ1 hμ2, fun _ hs =>
    let h := solovevFluxGeometry_coarea hs
    ⟨h.1, h.2.1, h.2.2.1⟩⟩

end actual

end PlasmaLean.Design.SolovevCoarea
