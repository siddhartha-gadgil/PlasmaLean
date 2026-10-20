/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevMercier
public import PlasmaLean.Design.SolovevMercierQuadrature
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Certified Mercier stability of the reactor Solov'ev equilibrium (whole plasma)

For the reactor Solov'ev equilibrium of `SolovevAlpha` (`A = 7/4 T`, `L = 10 m`,
`F = 50 T m`, `ψ̃ = R²z²/2 + (R² - L²)²/4`, plasma `ψ̃ ≤ L⁴/16`) we compute the flux-surface
data entering the general Mercier index `MercierGeneral.mercierIndex` (Landreman–Jorge 2020,
eq. (3.1), a SUPPLIED formula) on EVERY flux surface `ψ̃ = s²`, `0 < s ≤ 25`, and prove

  `reactor_mercier_stable : ∀ μ₀ > 0, ∀ s ∈ (0, 25], MercierStable (reactorSurfaceData μ₀ s)`,

i.e. `D_Merc > 0` on the whole plasma except the magnetic axis itself (`s = 0`, where the
flux-surface integrals are singular and the index is not defined).

## How the surface data are defined (`reactorSurfaceData`)

Everything is computed from the actual field `SolovevAlpha.reactorField`, the actual Ampère
current `Solovev.current` and the actual pressure `SolovevAlpha.reactorPressure`; the surface
is parametrized exactly by the meridian curve `surfPt s t = (R(t), 0, z(t))`,
`R² = L² + 2 s sin t`, `z = √2 s cos t / R` of `SolovevMercier` (`surfPt_on_surface`:
`ψ̃ = s²`). Labels:

* enclosed volume `volS s = 2π √2 ∫₀ˢ σ P(σ) dσ`, toroidal flux `2π · fluxS s` with
  `fluxS s = (F √2 / 2π) ∫₀ˢ σ Q(σ) dσ`, and Boozer `I = μ₀ I_tor/2π` with
  `currS s = (1/2π) ∫₀ˢ σ (-3 c √2) P(σ) dσ`, where `P(σ) = ∫ R⁻¹ dt`, `Q(σ) = ∫ R⁻³ dt`,
  `c = A/L²`. These are the area integrals `∫∫ R dR dz`, `∫∫ (F/R) dR dz`,
  `∫∫ μ₀J_φ dR dz` (`μ₀ J_φ = -3cR`, from `Solovev.field_curl`) written in the coordinates
  `(σ, t) ↦ (R, z)`, whose Jacobian `|∂(R,z)/∂(σ,t)| = √2 σ / R²` is proved in
  `jacobian_eq` (the change-of-variables formula itself is the standard one, not re-proved);
* `ψ` = `fluxS` (so `2πψ` is the toroidal flux), `' = d/dψ` via the chain rule in `s`:
  `V'' = (d/ds (V_s/ψ_s))/ψ_s` (`VppS`), `μ₀ p' = μ₀ (dp/ds)/ψ_s` (`muPprimeS`, with `p` the
  actual pressure on the surface), `ι' = (dι/ds)/ψ_s` (`iotaPrimeS`, `ι = 1/q` with the true
  field-line safety factor `SolovevMercier.qS`), `I' = (dI/ds)/ψ_s` (`Iprime`); every `d/ds`
  is Lean's `deriv`, and the closed forms are PROVED (FTC and differentiation under the
  integral sign, `hasDerivAt_Pint`, `hasDerivAt_Qint`);
* surface integrals `∫ f dS/|∇ψ|³` with `dS = 2π R |∂_t (R, z)| dt` (surface of revolution;
  `|∂_t(R,z)|` uses Lean's `deriv` of the explicit curve), `|∇ψ| = (dψ/dψ̃) |∇ψ̃|`
  (`psiC`, actual gradient `Solovev.psiTGrad`), and `Ξ = μ₀ J - I' B` (`Xi`);
* signs `s_G = +1` (`G = F > 0`) and `s_ψ = +1` (`ψ > 0`).

## Proof

`well_term_eq` and `intXi2_eq` reduce `s_ψ μ₀ p' V''` and `∫|Ξ|²/|∇ψ|³` EXACTLY (no
approximation) to the normalized integrals of `SolovevMercierQuadrature` at `ε = s/50`:

  `s_ψ μ₀ p' V'' = (294/125000) π⁴ (3 Pn S5n - Qn S3n) / Qn⁴`,
  `∫|Ξ|²/|∇ψ|³ = (98/125000) π⁴ IPhi / Qn³`,

so the dominant-well hypothesis of `MercierGeneral.mercierIndex_pos_of_well` is exactly
`SolovevMercierQuadrature.WellDominant (s/50)`, certified by validated quadrature for every
`ε ∈ (0, 1/2]` (`normalized_well_dominance`). With `intB2_pos` this gives `D_Merc > 0`.
As a by-product `reactor_Vpp_neg`: `V'' < 0` on every surface (a genuine magnetic well).

## Scope and trust

* The Mercier formula is the supplied interface of `MercierGeneral` (its derivation from
  `δW` is not formalized); Mercier stability is a NECESSARY condition for ideal-MHD
  stability (local interchange only: no ballooning, global, resistive or kinetic claim).
* The identification of `volS`, `fluxS`, `currS` with the physical enclosed volume, flux and
  current uses the 2-D change of variables with the proved Jacobian (`jacobian_eq`). For the
  volume this is now proved in `SolovevCoarea` (`volume_label_le`); for `fluxS`, `currS` the
  same `integral_shell` applies but has not been instantiated.
* The numerical part is fully rigorous: fixed-point interval arithmetic with outward
  rounding, kernel-checked (`decide +kernel` per `ε`-cell), uniform in `ε` on each cell.
* Certified margin: `3(3 Pn S5n - Qn S3n) / (Qn IPhi) ≥ 1.03` on every cell (true ratio
  `≈ 1.41` near the axis, `≈ 1.74` at the edge; the margin lost is quadrature over-estimate).
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevMercierCertified

open Real Set MeasureTheory intervalIntegral Filter Topology
open PlasmaLean.Fields PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevMercier
open PlasmaLean.Design.SolovevAlpha PlasmaLean.Stability.MercierGeneral
open PlasmaLean.Certificates.ValidatedQuadrature WithLp
open PlasmaLean.Design.SolovevMercierQuadrature (Pn Qn S3n S5n IPhi Phi rhoN sigN Gn
  WellDominant fP fQ fS3 fS5 normalized_well_dominance Gn_pos continuousOn_fP continuousOn_fQ
  continuousOn_fS3 continuousOn_fS5)

/-! ## The meridian parametrization of a flux surface -/

/-- The meridian point `(R(t), 0, z(t))` of the flux surface `ψ̃ = s²` (toroidal angle `0`). -/
@[expose] def surfPt (s t : ℝ) : Space := toLp 2 ![RS 10 s t, 0, zS 10 s t]

/-- First coordinate of the surface point. -/
theorem surfPt_0 (s t : ℝ) : surfPt s t 0 = RS 10 s t := by simp [surfPt]
/-- Second coordinate of the surface point. -/
theorem surfPt_1 (s t : ℝ) : surfPt s t 1 = 0 := by simp [surfPt]
/-- Third coordinate of the surface point. -/
theorem surfPt_2 (s t : ℝ) : surfPt s t 2 = zS 10 s t := by simp [surfPt]

/-- `R² = x₀² + x₁²` at the surface point. -/
theorem R2_surfPt (s t : ℝ) : R2 (surfPt s t) = RS 10 s t ^ 2 := by
  simp [R2, surfPt_0, surfPt_1]

/-- `R(t) = 10 √(1 + ε sin t)`, `ε = s/50`. -/
theorem RS_eq (s t : ℝ) : RS 10 s t = 10 * √(1 + s / 50 * Real.sin t) := by
  unfold RS uS
  rw [show (10 : ℝ) ^ 2 + 2 * s * Real.sin t = 10 ^ 2 * (1 + s / 50 * Real.sin t) by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- On the range `|σ| < 45` the major radius stays above `3` (`R² ≥ 10`). -/
theorem uS_ge {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) (t : ℝ) : 10 ≤ uS 10 σ t := by
  unfold uS
  have h1 := Real.neg_one_le_sin t
  have h2 := Real.sin_le_one t
  nlinarith [mul_nonneg (show 0 ≤ σ + 45 by linarith [hσ.1]) (show 0 ≤ 1 + Real.sin t by linarith),
    mul_nonneg (show 0 ≤ 45 - σ by linarith [hσ.2]) (show 0 ≤ 1 - Real.sin t by linarith)]

/-- `R > 3` on `|σ| < 45`. -/
theorem RS_gt {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) (t : ℝ) : 3 < RS 10 σ t := by
  unfold RS
  rw [show (3 : ℝ) = √(3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [uS_ge hσ t])

/-- `R > 0` on `|σ| < 45`. -/
theorem RS_pos' {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) (t : ℝ) : 0 < RS 10 σ t :=
  lt_trans (by norm_num) (RS_gt hσ t)

/-- Plasma labels lie in the differentiability range. -/
theorem mem_Ioo_of {s : ℝ} (hs : 0 < s) (hs' : s < 45) : s ∈ Ioo (-45 : ℝ) 45 :=
  ⟨by linarith, hs'⟩

/-- The meridian curve lies on the flux surface `ψ̃ = s²`. -/
theorem surfPt_on_surface {s : ℝ} (hs : 0 ≤ s) (h : 2 * s < 10 ^ 2) (t : ℝ) :
    psiT 10 (surfPt s t) = s ^ 2 := by
  have hR := RS_pos hs h t
  have hR2 := RS_sq hs h t
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hct := Real.sin_sq_add_cos_sq t
  unfold psiT
  rw [R2_surfPt, surfPt_2, zS]
  unfold uS at hR2
  field_simp
  rw [hR2]
  linear_combination (4 * s ^ 2 * Real.cos t ^ 2) * h2 + 8 * s ^ 2 * hct

/-! ## The surface integrals `P(s) = ∫ R⁻¹`, `Q(s) = ∫ R⁻³` and their derivatives -/

/-- `P(s) = ∫_{-π}^{π} R(t)⁻¹ dt`. -/
@[expose] def Pint (s : ℝ) : ℝ := ∫ t in (-π)..π, (RS 10 s t)⁻¹

/-- `Q(s) = ∫_{-π}^{π} R(t)⁻³ dt`. -/
@[expose] def Qint (s : ℝ) : ℝ := ∫ t in (-π)..π, (RS 10 s t ^ 3)⁻¹

/-- Normalization `P(s) = Pn(s/50)/10`. -/
theorem Pint_eq (s : ℝ) : Pint s = Pn (s / 50) / 10 := by
  unfold Pint Pn fP
  rw [← intervalIntegral.integral_div]
  congr 1; funext t
  rw [RS_eq, mul_inv]; ring

/-- Normalization `Q(s) = Qn(s/50)/1000`. -/
theorem Qint_eq (s : ℝ) : Qint s = Qn (s / 50) / 1000 := by
  unfold Qint Qn fQ
  rw [← intervalIntegral.integral_div]
  congr 1; funext t
  rw [RS_eq, mul_pow, mul_inv]; norm_num; ring

/-- Derivative in `σ` of `R(σ, t)`. -/
theorem hasDerivAt_RS_param {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) (t : ℝ) :
    HasDerivAt (fun σ => RS 10 σ t) (Real.sin t / RS 10 σ t) σ := by
  have hu : HasDerivAt (fun σ => uS 10 σ t) (2 * Real.sin t) σ := by
    have := ((hasDerivAt_id σ).const_mul (2 * Real.sin t)).const_add ((10 : ℝ) ^ 2)
    convert this using 1
    · funext x; simp [uS]; ring
    · ring
  have h := hu.sqrt (by linarith [uS_ge hσ t])
  have hR := RS_pos' hσ t
  have e : 2 * Real.sin t / (2 * √(uS 10 σ t)) = Real.sin t / RS 10 σ t := by
    unfold RS; field_simp
  rw [e] at h
  exact h

/-- Derivative in `σ` of `R⁻¹`. -/
theorem hasDerivAt_invRS {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) (t : ℝ) :
    HasDerivAt (fun σ => (RS 10 σ t)⁻¹) (-(Real.sin t * (RS 10 σ t ^ 3)⁻¹)) σ := by
  have hR := RS_pos' hσ t
  have h := (hasDerivAt_RS_param hσ t).inv hR.ne'
  convert h using 1
  field_simp

/-- Derivative in `σ` of `R⁻³`. -/
theorem hasDerivAt_invRS3 {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) (t : ℝ) :
    HasDerivAt (fun σ => (RS 10 σ t ^ 3)⁻¹) (-(3 * Real.sin t * (RS 10 σ t ^ 5)⁻¹)) σ := by
  have hR := RS_pos' hσ t
  have hp : HasDerivAt (fun σ => RS 10 σ t ^ 3)
      (3 * RS 10 σ t ^ 2 * (Real.sin t / RS 10 σ t)) σ := by
    simpa using (hasDerivAt_RS_param hσ t).fun_pow 3
  have h := hp.inv (pow_pos hR 3).ne'
  convert h using 1
  field_simp

/-- Continuity in `t` of `R⁻ᵏ`. -/
theorem continuous_invRSpow {σ : ℝ} (hσ : σ ∈ Ioo (-45 : ℝ) 45) (k : ℕ) :
    Continuous (fun t => (RS 10 σ t ^ k)⁻¹) :=
  (continuous_RS.pow k).inv₀ fun t => (pow_pos (RS_pos' hσ t) k).ne'

/-- Differentiation under the integral sign on `|σ| < 45` with a uniform derivative bound. -/
theorem hasDerivAt_param_integral {F F' : ℝ → ℝ → ℝ} {s0 M : ℝ}
    (hs0 : s0 ∈ Ioo (-45 : ℝ) 45) (hF : ∀ σ ∈ Ioo (-45 : ℝ) 45, Continuous (F σ))
    (hF' : Continuous (F' s0))
    (hd : ∀ t, ∀ σ ∈ Ioo (-45 : ℝ) 45, HasDerivAt (fun σ => F σ t) (F' σ t) σ)
    (hb : ∀ t, ∀ σ ∈ Ioo (-45 : ℝ) 45, |F' σ t| ≤ M) :
    HasDerivAt (fun σ => ∫ t in (-π)..π, F σ t) (∫ t in (-π)..π, F' s0 t) s0 := by
  have hs : Ioo (-45 : ℝ) 45 ∈ 𝓝 s0 := Ioo_mem_nhds hs0.1 hs0.2
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => M) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with σ hσ using (hF σ hσ).aestronglyMeasurable
  · exact (hF s0 hs0).intervalIntegrable _ _
  · exact hF'.aestronglyMeasurable
  · exact ae_of_all _ (fun t _ σ hσ => by rw [Real.norm_eq_abs]; exact hb t σ hσ)
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun t _ σ hσ => hd t σ hσ)

/-- `dP/ds = -∫ sin t R⁻³ dt` (differentiation under the integral sign). -/
theorem hasDerivAt_Pint {s : ℝ} (hs : s ∈ Ioo (-45 : ℝ) 45) :
    HasDerivAt Pint (∫ t in (-π)..π, -(Real.sin t * (RS 10 s t ^ 3)⁻¹)) s := by
  have h := hasDerivAt_param_integral (F := fun σ t => (RS 10 σ t)⁻¹)
    (F' := fun σ t => -(Real.sin t * (RS 10 σ t ^ 3)⁻¹)) (M := 1) hs
    (fun σ hσ => by simpa using continuous_invRSpow hσ 1)
    ((Real.continuous_sin.mul (continuous_invRSpow hs 3)).neg)
    (fun t σ hσ => hasDerivAt_invRS hσ t)
    (fun t σ hσ => by
      have hR := RS_gt hσ t
      have h3 : 1 ≤ RS 10 σ t ^ 3 := one_le_pow₀ (by linarith)
      rw [abs_neg, abs_mul]
      have : |(RS 10 σ t ^ 3)⁻¹| ≤ 1 := by
        rw [abs_of_pos (inv_pos.2 (by linarith))]; exact inv_le_one_of_one_le₀ h3
      calc |Real.sin t| * |(RS 10 σ t ^ 3)⁻¹| ≤ 1 * 1 :=
            mul_le_mul (Real.abs_sin_le_one t) this (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num)
  exact h

/-- `dQ/ds = -3 ∫ sin t R⁻⁵ dt`. -/
theorem hasDerivAt_Qint {s : ℝ} (hs : s ∈ Ioo (-45 : ℝ) 45) :
    HasDerivAt Qint (∫ t in (-π)..π, -(3 * Real.sin t * (RS 10 s t ^ 5)⁻¹)) s := by
  have h := hasDerivAt_param_integral (F := fun σ t => (RS 10 σ t ^ 3)⁻¹)
    (F' := fun σ t => -(3 * Real.sin t * (RS 10 σ t ^ 5)⁻¹)) (M := 3) hs
    (fun σ hσ => continuous_invRSpow hσ 3)
    (((continuous_const.mul Real.continuous_sin).mul (continuous_invRSpow hs 5)).neg)
    (fun t σ hσ => hasDerivAt_invRS3 hσ t)
    (fun t σ hσ => by
      have hR := RS_gt hσ t
      have h5 : 1 ≤ RS 10 σ t ^ 5 := one_le_pow₀ (by linarith)
      rw [abs_neg, abs_mul, abs_mul]
      have : |(RS 10 σ t ^ 5)⁻¹| ≤ 1 := by
        rw [abs_of_pos (inv_pos.2 (by linarith))]; exact inv_le_one_of_one_le₀ h5
      calc |(3 : ℝ)| * |Real.sin t| * |(RS 10 σ t ^ 5)⁻¹| ≤ 3 * 1 * 1 := by
            gcongr
            · norm_num
            · exact Real.abs_sin_le_one t
        _ = 3 := by norm_num)
  exact h

/-- Normalization of `dP/ds`: `-∫ sin t R⁻³ = ε S3n(ε)/1000`, `ε = s/50`. -/
theorem dPint_eq {s : ℝ} (hs : 0 < s) :
    ∫ t in (-π)..π, -(Real.sin t * (RS 10 s t ^ 3)⁻¹) = s / 50 * S3n (s / 50) / 1000 := by
  have hε : s / 50 ≠ 0 := by positivity
  unfold S3n fS3
  rw [mul_div_cancel₀ _ hε, ← intervalIntegral.integral_div]
  congr 1; funext t
  rw [RS_eq, mul_pow, mul_inv]; norm_num; ring

/-- Normalization of `dQ/ds`: `-3 ∫ sin t R⁻⁵ = 3 ε S5n(ε)/10⁵`. -/
theorem dQint_eq {s : ℝ} (hs : 0 < s) :
    ∫ t in (-π)..π, -(3 * Real.sin t * (RS 10 s t ^ 5)⁻¹) =
      3 * (s / 50 * S5n (s / 50)) / 100000 := by
  have hε : s / 50 ≠ 0 := by positivity
  unfold S5n fS5
  rw [mul_div_cancel₀ _ hε, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_div]
  congr 1; funext t
  rw [RS_eq, mul_pow, mul_inv]; norm_num; ring

/-- `P` is continuous on `|s| < 45`. -/
theorem continuousOn_Pint : ContinuousOn Pint (Ioo (-45 : ℝ) 45) :=
  continuousOn_of_forall_continuousAt fun _ hx => (hasDerivAt_Pint hx).continuousAt

/-- `Q` is continuous on `|s| < 45`. -/
theorem continuousOn_Qint : ContinuousOn Qint (Ioo (-45 : ℝ) 45) :=
  continuousOn_of_forall_continuousAt fun _ hx => (hasDerivAt_Qint hx).continuousAt

/-- `Q > 0`. -/
theorem Qint_pos {s : ℝ} (hs : s ∈ Ioo (-45 : ℝ) 45) : 0 < Qint s := by
  unfold Qint
  exact intervalIntegral_pos_of_pos_on ((continuous_invRSpow hs 3).intervalIntegrable _ _)
    (fun t _ => inv_pos.2 (pow_pos (RS_pos' hs t) 3)) (by linarith [Real.pi_pos])

/-- `P > 0`. -/
theorem Pint_pos {s : ℝ} (hs : s ∈ Ioo (-45 : ℝ) 45) : 0 < Pint s := by
  unfold Pint
  have := (continuous_invRSpow hs 1).intervalIntegrable (μ := volume) (-π) π
  simp only [pow_one] at this
  exact intervalIntegral_pos_of_pos_on this (fun t _ => inv_pos.2 (RS_pos' hs t))
    (by linarith [Real.pi_pos])

/-! ## Volume, toroidal flux and toroidal current as functions of the label `s` -/

/-- Enclosed volume `V(s) = 2π ∫∫ R dR dz = 2π √2 ∫₀ˢ σ P(σ) dσ`
(coordinates `(σ, t)`, `R dR dz = √2 σ R⁻¹ dσ dt`). -/
@[expose] def volS (s : ℝ) : ℝ := 2 * π * √2 * ∫ σ in (0 : ℝ)..s, σ * Pint σ

/-- Toroidal-flux label `ψ(s) = (1/2π) ∫∫ (F/R) dR dz = (F √2/2π) ∫₀ˢ σ Q(σ) dσ`
(`2πψ` = toroidal flux; `dR dz = √2 σ R⁻² dσ dt`). -/
@[expose] def fluxS (s : ℝ) : ℝ := 50 * √2 / (2 * π) * ∫ σ in (0 : ℝ)..s, σ * Qint σ

/-- Boozer `I(s) = (1/2π) ∫∫ μ₀ J_φ dR dz` with `μ₀ J_φ = -3 c R`, `c = A/L² = 7/400`:
`I = -(21 √2/(800 π)) ∫₀ˢ σ P(σ) dσ`. -/
@[expose] def currS (s : ℝ) : ℝ := -(21 * √2 / (800 * π)) * ∫ σ in (0 : ℝ)..s, σ * Pint σ

/-- Fundamental theorem of calculus for primitives of functions continuous on `|σ| < 45`. -/
theorem hasDerivAt_primitive {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-45 : ℝ) 45)) {s : ℝ}
    (hs : 0 < s) (hs' : s < 45) : HasDerivAt (fun u => ∫ σ in (0 : ℝ)..u, f σ) (f s) s := by
  have hsub : uIcc 0 s ⊆ Ioo (-45 : ℝ) 45 := by
    rw [uIcc_of_le hs.le]; intro x hx; constructor <;> linarith [hx.1, hx.2]
  have hsI := mem_Ioo_of hs hs'
  exact intervalIntegral.integral_hasDerivAt_right ((hf.mono hsub).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter isOpen_Ioo s hsI) (hf.continuousAt (Ioo_mem_nhds hsI.1 hsI.2))

/-- `dV/ds = 2π √2 s P(s)`. -/
theorem deriv_volS {s : ℝ} (hs : 0 < s) (hs' : s < 45) :
    deriv volS s = 2 * π * √2 * (s * Pint s) :=
  ((hasDerivAt_primitive (continuousOn_id.mul continuousOn_Pint) hs hs').const_mul _).deriv

/-- `dψ/ds = (F √2/2π) s Q(s)`. -/
theorem deriv_fluxS {s : ℝ} (hs : 0 < s) (hs' : s < 45) :
    deriv fluxS s = 50 * √2 / (2 * π) * (s * Qint s) :=
  ((hasDerivAt_primitive (continuousOn_id.mul continuousOn_Qint) hs hs').const_mul _).deriv

/-- `dI/ds = -(21 √2/(800 π)) s P(s)`. -/
theorem deriv_currS {s : ℝ} (hs : 0 < s) (hs' : s < 45) :
    deriv currS s = -(21 * √2 / (800 * π)) * (s * Pint s) :=
  ((hasDerivAt_primitive (continuousOn_id.mul continuousOn_Pint) hs hs').const_mul _).deriv

/-- `dψ/ds > 0`: the label `ψ` increases outward. -/
theorem deriv_fluxS_pos {s : ℝ} (hs : 0 < s) (hs' : s < 45) : 0 < deriv fluxS s := by
  rw [deriv_fluxS hs hs']
  have := Qint_pos (mem_Ioo_of hs hs')
  have := Real.pi_pos
  positivity

/-! ## The magnetic-well term `s_ψ μ₀ p' V''` -/

/-- `d²V/dψ²`, by the chain rule in the label `s`: `(d/ds (V_s/ψ_s)) / ψ_s`. -/
@[expose] def VppS (s : ℝ) : ℝ :=
  deriv (fun σ => deriv volS σ / deriv fluxS σ) s / deriv fluxS s

/-- `μ₀ dp/dψ = μ₀ (dp/ds)/ψ_s`, with `p` the actual reactor pressure on the surface. -/
@[expose] def muPprimeS (μ₀ s : ℝ) : ℝ :=
  μ₀ * deriv (fun σ => reactorPressure μ₀ (surfPt σ 0)) s / deriv fluxS s

/-- `V_s/ψ_s = (4π²/F) P/Q` near every plasma label. -/
theorem ratio_eventually {s : ℝ} (hs : 0 < s) (hs' : s < 45) :
    (fun σ => deriv volS σ / deriv fluxS σ) =ᶠ[𝓝 s]
      fun σ => 4 * π ^ 2 / 50 * (Pint σ / Qint σ) := by
  filter_upwards [Ioo_mem_nhds hs hs'] with σ hσ
  rw [deriv_volS hσ.1 hσ.2, deriv_fluxS hσ.1 hσ.2]
  have := Qint_pos (mem_Ioo_of hσ.1 hσ.2)
  have := hσ.1
  have := Real.pi_pos
  field_simp
  ring

/-- `d/ds (V_s/ψ_s)` by differentiation under the integral sign, normalized. -/
theorem deriv_ratio {s : ℝ} (hs : 0 < s) (hs' : s < 45) :
    deriv (fun σ => deriv volS σ / deriv fluxS σ) s =
      4 * π ^ 2 / 50 * ((s / 50 * S3n (s / 50) / 1000 * Qint s -
        Pint s * (3 * (s / 50 * S5n (s / 50)) / 100000)) / Qint s ^ 2) := by
  have hsI := mem_Ioo_of hs hs'
  rw [(ratio_eventually hs hs').deriv_eq]
  have h := ((hasDerivAt_Pint hsI).div (hasDerivAt_Qint hsI) (Qint_pos hsI).ne').const_mul
    (4 * π ^ 2 / 50)
  rw [dPint_eq hs, dQint_eq hs] at h
  exact h.deriv

/-- The actual pressure on the surface is `p₀ (1 - 16 s²/L⁴)` near every plasma label. -/
theorem pressure_eventually {μ₀ s : ℝ} (hμ : μ₀ ≠ 0) (hs : 0 < s) (hs' : s < 45) :
    (fun σ => reactorPressure μ₀ (surfPt σ 0)) =ᶠ[𝓝 s]
      fun σ => 147 / (256 * μ₀) * (1 - 16 * σ ^ 2 / 10 ^ 4) := by
  filter_upwards [Ioo_mem_nhds hs hs'] with σ hσ
  rw [reactorPressure_eq μ₀ hμ, surfPt_on_surface hσ.1.le (by linarith [hσ.2])]

/-- `μ₀ dp/ds = -147 s/80000` (`= -6 c² s`). -/
theorem mu_deriv_pressure {μ₀ s : ℝ} (hμ : μ₀ ≠ 0) (hs : 0 < s) (hs' : s < 45) :
    μ₀ * deriv (fun σ => reactorPressure μ₀ (surfPt σ 0)) s = -(147 * s / 80000) := by
  rw [(pressure_eventually hμ hs hs').deriv_eq]
  have h : HasDerivAt (fun σ : ℝ => 147 / (256 * μ₀) * (1 - 16 * σ ^ 2 / 10 ^ 4))
      (147 / (256 * μ₀) * (-(16 * (2 * s) / 10 ^ 4))) s := by
    have := (((hasDerivAt_pow 2 s).const_mul 16).div_const (10 ^ 4)).const_sub 1
    have := this.const_mul (147 / (256 * μ₀))
    convert this using 1
    simp
  rw [h.deriv]
  field_simp
  ring

/-- **The well term in normalized form** (`ε = s/50`):
`s_ψ μ₀ p' V'' = (294/125000) π⁴ (3 Pn S5n - Qn S3n) / Qn⁴`. -/
theorem well_term_eq {μ₀ s : ℝ} (hμ : 0 < μ₀) (hs : 0 < s) (hs' : s < 45) :
    1 * muPprimeS μ₀ s * VppS s =
      294 / 125000 * π ^ 4 * (3 * Pn (s / 50) * S5n (s / 50) - Qn (s / 50) * S3n (s / 50)) /
        Qn (s / 50) ^ 4 := by
  unfold muPprimeS VppS
  rw [mul_div_assoc', mu_deriv_pressure hμ.ne' hs hs', deriv_ratio hs hs', deriv_fluxS hs hs',
    Pint_eq, Qint_eq]
  have hQ : 0 < Qn (s / 50) := by
    have := Qint_pos (mem_Ioo_of hs hs'); rw [Qint_eq] at this; linarith
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h20 : 0 < √2 := by positivity
  have := Real.pi_pos
  field_simp
  rw [h2]
  ring

/-! ## The surface integrals `∫ (·) dS/|∇ψ|³` -/

open scoped RealInnerProductSpace

/-- `dψ/dψ̃` on the surface `ψ̃ = s²` (so `|∇ψ| = psiC s · |∇ψ̃|`). -/
@[expose] def psiC (s : ℝ) : ℝ := deriv fluxS s / (2 * s)

/-- `I'(ψ) = (dI/ds)/(dψ/ds)`. -/
@[expose] def Iprime (s : ℝ) : ℝ := deriv currS s / deriv fluxS s

/-- `Ξ = μ₀ J - I' B` at the surface point, with the actual Ampère current and field. -/
@[expose] def Xi (μ₀ s t : ℝ) : Space :=
  μ₀ • current μ₀ (7 / 4) 10 50 (surfPt s t) - Iprime s • reactorField (surfPt s t)

/-- The weight `dS/|∇ψ|³` per unit `t` (integrated over the toroidal angle):
`2π R |∂_t (R, z)| / (psiC · |∇ψ̃|)³`. -/
@[expose] def wSurf (s t : ℝ) : ℝ :=
  2 * π * RS 10 s t * √(deriv (RS 10 s) t ^ 2 + deriv (zS 10 s) t ^ 2) /
    (psiC s * ‖psiTGrad 10 (surfPt s t)‖) ^ 3

/-- `∫ |Ξ|² dS/|∇ψ|³`. -/
@[expose] def intXi2S (μ₀ s : ℝ) : ℝ := ∫ t in (-π)..π, ‖Xi μ₀ s t‖ ^ 2 * wSurf s t

/-- `∫ B² dS/|∇ψ|³`. -/
@[expose] def intB2S (s : ℝ) : ℝ := ∫ t in (-π)..π, ‖reactorField (surfPt s t)‖ ^ 2 * wSurf s t

/-- `∫ B·Ξ dS/|∇ψ|³`. -/
@[expose] def intBXiS (μ₀ s : ℝ) : ℝ :=
  ∫ t in (-π)..π, ⟪reactorField (surfPt s t), Xi μ₀ s t⟫ * wSurf s t

/-- `dψ/dψ̃ = √2 Qn/(80π)`. -/
theorem psiC_eq {s : ℝ} (hs : 0 < s) (hs' : s < 45) :
    psiC s = √2 * Qn (s / 50) / (80 * π) := by
  unfold psiC
  rw [deriv_fluxS hs hs', Qint_eq]
  have := Real.pi_pos
  field_simp
  ring

/-- `Qn > 0` on plasma labels. -/
theorem Qn_pos {s : ℝ} (hs : 0 < s) (hs' : s < 45) : 0 < Qn (s / 50) := by
  have := Qint_pos (mem_Ioo_of hs hs'); rw [Qint_eq] at this; linarith

/-- `dψ/dψ̃ > 0`. -/
theorem psiC_pos {s : ℝ} (hs : 0 < s) (hs' : s < 45) : 0 < psiC s := by
  rw [psiC_eq hs hs']
  have := Qn_pos hs hs'
  have := Real.pi_pos
  positivity

/-- `I' = -(21/200) ρ`, `ρ = Pn/Qn`. -/
theorem Iprime_eq {s : ℝ} (hs : 0 < s) (hs' : s < 45) :
    Iprime s = -(21 / 200) * rhoN (s / 50) := by
  unfold Iprime rhoN
  rw [deriv_currS hs hs', deriv_fluxS hs hs', Pint_eq, Qint_eq]
  have := Qn_pos hs hs'
  have := Real.pi_pos
  have h20 : 0 < √2 := by positivity
  field_simp
  ring

/-- `Qn - Pn = ε² S3n`, hence `σ = ε S3n/Qn = (1 - ρ)/ε`. -/
theorem sigN_eq {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) : sigN ε = (1 - rhoN ε) / ε := by
  have hI1 : IntervalIntegrable (fun t => fQ ε (Real.sin t)) volume (-π) π :=
    ((continuousOn_fQ hε.le hε').comp_continuous Real.continuous_sin
      (fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩)).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t => fP ε (Real.sin t)) volume (-π) π :=
    ((continuousOn_fP hε.le hε').comp_continuous Real.continuous_sin
      (fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩)).intervalIntegrable _ _
  have hQ : Qn ε - Pn ε = ε * (ε * S3n ε) := by
    unfold Qn Pn S3n
    rw [mul_div_cancel₀ _ hε.ne', ← intervalIntegral.integral_sub hI1 hI2,
      ← intervalIntegral.integral_const_mul]
    congr 1; funext t
    unfold fQ fP fS3
    have hv : 0 < 1 + ε * Real.sin t := by
      nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
    have ha := Real.sqrt_pos.2 hv
    have ha2 := Real.sq_sqrt hv.le
    field_simp
    nlinarith [ha2]
  have hQpos : 0 < Qn ε := by
    have := Qn_pos (s := 50 * ε) (by linarith) (by linarith)
    rwa [show 50 * ε / 50 = ε by ring] at this
  unfold sigN rhoN
  field_simp
  linarith

section geometry

variable {s : ℝ} (hs : 0 < s) (hs' : s ≤ 25) (t : ℝ)
include hs hs'

/-- `R > 0` on plasma surfaces. -/
theorem RS_pos_s : 0 < RS 10 s t := RS_pos hs.le (by linarith) t

/-- `R² = 100 + 2 s sin t`. -/
theorem RS_sq_s : RS 10 s t ^ 2 = 100 + 2 * s * Real.sin t := by
  rw [RS_sq hs.le (by linarith) t]; unfold uS; norm_num

/-- Derivative in `t` of `R`. -/
theorem hasDerivAt_RS_t : HasDerivAt (RS 10 s) (s * Real.cos t / RS 10 s t) t := by
  have hu : HasDerivAt (uS 10 s) (2 * s * Real.cos t) t :=
    ((Real.hasDerivAt_sin t).const_mul (2 * s)).const_add (10 ^ 2)
  have h := hu.sqrt (uS_pos hs.le (by linarith) t).ne'
  have hR := RS_pos_s hs hs' t
  have e : 2 * s * Real.cos t / (2 * √(uS 10 s t)) = s * Real.cos t / RS 10 s t := by
    unfold RS; field_simp
  rw [e] at h
  exact h

/-- Derivative in `t` of `z`. -/
theorem hasDerivAt_zS_t : HasDerivAt (zS 10 s)
    ((√2 * s * -Real.sin t * RS 10 s t - √2 * s * Real.cos t * (s * Real.cos t / RS 10 s t)) /
      RS 10 s t ^ 2) t := by
  exact ((Real.hasDerivAt_cos t).const_mul (√2 * s)).div (hasDerivAt_RS_t hs hs' t)
    (RS_pos_s hs hs' t).ne'

omit hs hs' in
/-- `|∇ψ̃|²` at the surface point, explicitly. -/
theorem normsq_psiTGrad : ‖psiTGrad 10 (surfPt s t)‖ ^ 2 =
    RS 10 s t ^ 2 * (zS 10 s t ^ 2 + RS 10 s t ^ 2 - 10 ^ 2) ^ 2 +
      (RS 10 s t ^ 2 * zS 10 s t) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [psiTGrad, surfPt_0, surfPt_1, surfPt_2, R2_surfPt]
  ring

/-- `|∇ψ̃|² = 10⁴ s² G(ε, sin t)/R²` (`ε = s/50`). -/
theorem normsq_psiTGrad_eq : ‖psiTGrad 10 (surfPt s t)‖ ^ 2 =
    10000 * s ^ 2 * Gn (s / 50) (Real.sin t) / RS 10 s t ^ 2 := by
  rw [normsq_psiTGrad t]
  have hR := RS_pos_s hs hs' t
  have hRu := RS_sq_s hs hs' t
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := Real.sin_sq_add_cos_sq t
  unfold zS Gn
  field_simp
  grind

/-- `|∇ψ̃|² > 0` on plasma surfaces (no X-point inside the plasma). -/
theorem G2_pos : 0 < ‖psiTGrad 10 (surfPt s t)‖ ^ 2 := by
  rw [normsq_psiTGrad_eq hs hs' t]
  have := Gn_pos (ε := s / 50) (y := Real.sin t) (by positivity) (by linarith)
    ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have := RS_pos_s hs hs' t
  positivity

/-- Arclength: `R'² + z'² = |∇ψ̃|²/(2R⁴)`. -/
theorem arclength_sq : deriv (RS 10 s) t ^ 2 + deriv (zS 10 s) t ^ 2 =
    ‖psiTGrad 10 (surfPt s t)‖ ^ 2 / (2 * RS 10 s t ^ 4) := by
  rw [(hasDerivAt_RS_t hs hs' t).deriv, (hasDerivAt_zS_t hs hs' t).deriv,
    normsq_psiTGrad t]
  have hR := RS_pos_s hs hs' t
  have hRu := RS_sq_s hs hs' t
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold zS
  field_simp
  grind

/-- The surface weight in closed form: `dS/|∇ψ|³ = 2π/(√2 R psiC³ |∇ψ̃|²) dt`. -/
theorem wSurf_eq : wSurf s t =
    2 * π / (√2 * RS 10 s t * psiC s ^ 3 * ‖psiTGrad 10 (surfPt s t)‖ ^ 2) := by
  unfold wSurf
  have hR := RS_pos_s hs hs' t
  have hG := G2_pos hs hs' t
  set G := ‖psiTGrad 10 (surfPt s t)‖ with hGdef
  have hG0 : 0 < G := by
    have hne : G ≠ 0 := by rintro h0; rw [h0] at hG; norm_num at hG
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h20 : 0 < √2 := by positivity
  have hsq : √(deriv (RS 10 s) t ^ 2 + deriv (zS 10 s) t ^ 2) = G / (√2 * RS 10 s t ^ 2) := by
    rw [arclength_sq hs hs' t, ← hGdef]
    rw [show G ^ 2 / (2 * RS 10 s t ^ 4) = (G / (√2 * RS 10 s t ^ 2)) ^ 2 by
      rw [div_pow, mul_pow, h2]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  have := psiC_pos hs (by linarith : s < 45)
  field_simp

/-- `|Ξ|²` at the surface point: `(I'² c² |∇ψ̃|² + (3cR² + F I')²)/R²`, `c = 7/400`. -/
theorem Xi_normsq {μ₀ : ℝ} (hμ : μ₀ ≠ 0) : ‖Xi μ₀ s t‖ ^ 2 =
    (Iprime s ^ 2 * (7 / 400) ^ 2 * ‖psiTGrad 10 (surfPt s t)‖ ^ 2 +
      (3 * (7 / 400) * RS 10 s t ^ 2 + 50 * Iprime s) ^ 2) / RS 10 s t ^ 2 := by
  have hR := RS_pos_s hs hs' t
  have hx : R2 (surfPt s t) ≠ 0 := by rw [R2_surfPt]; positivity
  have hcur : μ₀ • current μ₀ (7 / 4) 10 50 (surfPt s t) =
      toLp 2 ![3 * ((7 / 4) / 10 ^ 2) * surfPt s t 1,
        -(3 * ((7 / 4) / 10 ^ 2) * surfPt s t 0), 0] := by
    rw [current, smul_smul, mul_inv_cancel₀ hμ, one_smul, field_curl _ _ _ hx]
  rw [normsq_psiTGrad t, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [Xi, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hcur, reactorField]
  rw [congrFun (field_coords _ _ _).1, congrFun (field_coords _ _ _).2.1,
    congrFun (field_coords _ _ _).2.2]
  simp [surfPt_0, surfPt_1, surfPt_2, R2_surfPt]
  field_simp
  ring

/-- `|B|²` at the surface point: `(c² |∇ψ̃|² + F²)/R²`. -/
theorem B_normsq : ‖reactorField (surfPt s t)‖ ^ 2 =
    ((7 / 400) ^ 2 * ‖psiTGrad 10 (surfPt s t)‖ ^ 2 + 2500) / RS 10 s t ^ 2 := by
  have hR := RS_pos_s hs hs' t
  rw [normsq_psiTGrad t, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [reactorField]
  rw [congrFun (field_coords _ _ _).1, congrFun (field_coords _ _ _).2.1,
    congrFun (field_coords _ _ _).2.2]
  simp [surfPt_0, surfPt_1, surfPt_2, R2_surfPt]
  field_simp
  ring

/-- **Jacobian of the surface coordinates** `(σ, t) ↦ (R, z)` used for `volS`, `fluxS`,
`currS`: `∂_σR ∂_t z - ∂_t R ∂_σ z = -√2 σ / R²`, so `dR dz = (√2 σ / R²) dσ dt`
(the partial derivatives are the actual ones, proved here). -/
theorem jacobian_eq : HasDerivAt (fun σ => RS 10 σ t) (Real.sin t / RS 10 s t) s ∧
    HasDerivAt (RS 10 s) (s * Real.cos t / RS 10 s t) t ∧
    HasDerivAt (fun σ => zS 10 σ t)
      ((√2 * Real.cos t * RS 10 s t - √2 * s * Real.cos t * (Real.sin t / RS 10 s t)) /
        RS 10 s t ^ 2) s ∧
    HasDerivAt (zS 10 s)
      ((√2 * s * -Real.sin t * RS 10 s t - √2 * s * Real.cos t * (s * Real.cos t / RS 10 s t)) /
        RS 10 s t ^ 2) t ∧
    Real.sin t / RS 10 s t *
        ((√2 * s * -Real.sin t * RS 10 s t - √2 * s * Real.cos t * (s * Real.cos t / RS 10 s t)) /
          RS 10 s t ^ 2) -
      s * Real.cos t / RS 10 s t *
        ((√2 * Real.cos t * RS 10 s t - √2 * s * Real.cos t * (Real.sin t / RS 10 s t)) /
          RS 10 s t ^ 2) = -(√2 * s / RS 10 s t ^ 2) := by
  have hsI := mem_Ioo_of hs (by linarith : s < 45)
  have hR := RS_pos_s hs hs' t
  have h1 : HasDerivAt (fun σ => √2 * σ * Real.cos t) (√2 * Real.cos t) s := by
    simpa using ((hasDerivAt_id s).const_mul (√2)).mul_const (Real.cos t)
  refine ⟨hasDerivAt_RS_param hsI t, hasDerivAt_RS_t hs hs' t,
    h1.div (hasDerivAt_RS_param hsI t) hR.ne', hasDerivAt_zS_t hs hs' t, ?_⟩
  have hcs := Real.sin_sq_add_cos_sq t
  field_simp
  grind

end geometry

/-- The rational identity behind `integrand_Xi` (`q = √2`, `P = π`, `g = G(ε, sin t)`). -/
theorem xi_algebra (R s q P ρ Qn g : ℝ) (hR : 0 < R) (hs : 0 < s) (hq : q ^ 2 = 2) (hq0 : 0 < q)
    (hP : 0 < P) (hQ : 0 < Qn) (hg : 0 < g) :
    ((-(21 / 200) * ρ) ^ 2 * (7 / 400) ^ 2 * (10000 * s ^ 2 * g / R ^ 2) +
        (3 * (7 / 400) * R ^ 2 + 50 * (-(21 / 200) * ρ)) ^ 2) / R ^ 2 *
      (2 * P / (q * R * (q * Qn / (80 * P)) ^ 3 * (10000 * s ^ 2 * g / R ^ 2))) =
    98 / 125000 * P ^ 4 *
      ((441 / 400 * ρ ^ 2 + 36 * ((R ^ 2 / 100 - ρ) / (s / 50)) ^ 2 * (R ^ 2 / 100 * g⁻¹)) *
        (R ^ 2 / 100 * (R / 10))⁻¹) / Qn ^ 3 := by
  field_simp
  grind

/-- **Pointwise reduction of the `|Ξ|²` integrand** to the normalized `Phi` (`ε = s/50`):
`|Ξ|² dS/|∇ψ|³ = (98/125000) π⁴ Phi(ρ, σ, ε, sin t) / Qn³ dt`. -/
theorem integrand_Xi {μ₀ s : ℝ} (hμ : μ₀ ≠ 0) (hs : 0 < s) (hs' : s ≤ 25) (t : ℝ) :
    ‖Xi μ₀ s t‖ ^ 2 * wSurf s t = 98 / 125000 * π ^ 4 *
      Phi (rhoN (s / 50)) (sigN (s / 50)) (s / 50) (Real.sin t) / Qn (s / 50) ^ 3 := by
  have hs45 : s < 45 := by linarith
  have hR := RS_pos_s hs hs' t
  have hRu := RS_sq_s hs hs' t
  rw [Xi_normsq hs hs' t hμ, wSurf_eq hs hs' t, normsq_psiTGrad_eq hs hs' t, Iprime_eq hs hs45,
    psiC_eq hs hs45, sigN_eq (by positivity) (by linarith)]
  unfold Phi
  have hv2 : √(1 + s / 50 * Real.sin t) = RS 10 s t / 10 := by rw [RS_eq]; ring
  have hv1 : 1 + s / 50 * Real.sin t = RS 10 s t ^ 2 / 100 := by rw [hRu]; ring
  have hy : Real.sin t + (1 - rhoN (s / 50)) / (s / 50) =
      (RS 10 s t ^ 2 / 100 - rhoN (s / 50)) / (s / 50) := by
    rw [hRu]; field_simp; ring
  rw [hv2, hy, hv1]
  exact xi_algebra (RS 10 s t) s (√2) π (rhoN (s / 50)) (Qn (s / 50)) (Gn (s / 50) (Real.sin t))
    hR hs (Real.sq_sqrt (by norm_num)) (by positivity) Real.pi_pos (Qn_pos hs hs45)
    (Gn_pos (by positivity) (by linarith) ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩)

/-- **`∫|Ξ|²/|∇ψ|³` in normalized form**: `(98/125000) π⁴ IPhi(ε)/Qn(ε)³`, `ε = s/50`. -/
theorem intXi2_eq {μ₀ s : ℝ} (hμ : μ₀ ≠ 0) (hs : 0 < s) (hs' : s ≤ 25) :
    intXi2S μ₀ s = 98 / 125000 * π ^ 4 * IPhi (s / 50) / Qn (s / 50) ^ 3 := by
  unfold intXi2S IPhi
  rw [intervalIntegral.integral_congr (g := fun t => 98 / 125000 * π ^ 4 / Qn (s / 50) ^ 3 *
    Phi (rhoN (s / 50)) (sigN (s / 50)) (s / 50) (Real.sin t))
    (fun t _ => by rw [integrand_Xi hμ hs hs' t]; ring), intervalIntegral.integral_const_mul]
  ring

/-- Closed form of the `B²` integrand: `(2π/(√2 psiC³)) (c²/R³ + 1/(4 s² G R))`. -/
theorem integrand_B {s : ℝ} (hs : 0 < s) (hs' : s ≤ 25) (t : ℝ) :
    ‖reactorField (surfPt s t)‖ ^ 2 * wSurf s t = 2 * π / (√2 * psiC s ^ 3) *
      ((7 / 400) ^ 2 * (RS 10 s t ^ 3)⁻¹ +
        (4 * s ^ 2 * Gn (s / 50) (Real.sin t) * RS 10 s t)⁻¹) := by
  have hR := RS_pos_s hs hs' t
  have hG := Gn_pos (ε := s / 50) (y := Real.sin t) (by positivity) (by linarith)
    ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have hc := psiC_pos hs (by linarith : s < 45)
  rw [B_normsq hs hs' t, wSurf_eq hs hs' t, normsq_psiTGrad_eq hs hs' t]
  field_simp
  ring

/-- `∫ B²/|∇ψ|³ > 0`. -/
theorem intB2_pos {s : ℝ} (hs : 0 < s) (hs' : s ≤ 25) : 0 < intB2S s := by
  unfold intB2S
  have hc := psiC_pos hs (by linarith : s < 45)
  have hGpos : ∀ t, 0 < Gn (s / 50) (Real.sin t) := fun t =>
    Gn_pos (by positivity) (by linarith) ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have hRpos := RS_pos_s hs hs'
  rw [intervalIntegral.integral_congr (fun t _ => integrand_B hs hs' t)]
  have hcont : Continuous (fun t => 2 * π / (√2 * psiC s ^ 3) *
      ((7 / 400) ^ 2 * (RS 10 s t ^ 3)⁻¹ +
        (4 * s ^ 2 * Gn (s / 50) (Real.sin t) * RS 10 s t)⁻¹)) := by
    refine continuous_const.mul (Continuous.add (continuous_const.mul
      ((continuous_RS.pow 3).inv₀ fun t => (pow_pos (hRpos t) 3).ne'))
      (Continuous.inv₀ ?_ fun t => (by have := hGpos t; have := hRpos t; positivity)))
    exact (continuous_const.mul (by unfold Gn; fun_prop)).mul continuous_RS
  refine intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) (fun t _ => ?_)
    (by linarith [Real.pi_pos])
  have := hGpos t
  have := hRpos t
  have := Real.pi_pos
  positivity

/-! ## The Mercier surface data and the main theorem -/

/-- The rotational transform `ι = 1/q` with the true field-line safety factor. -/
@[expose] def iotaS (s : ℝ) : ℝ := (qS (7 / 4) 10 50 s)⁻¹

/-- `ι' = (dι/ds)/(dψ/ds)`. -/
@[expose] def iotaPrimeS (s : ℝ) : ℝ := deriv iotaS s / deriv fluxS s

/-- **The exact Mercier surface data of the reactor Solov'ev equilibrium** on the flux surface
`ψ̃ = s²` (toroidal-flux label `ψ = fluxS`, `s_G = s_ψ = +1`). -/
@[expose] def reactorSurfaceData (μ₀ s : ℝ) : MercierSurfaceData where
  sG := 1
  sψ := 1
  iotaPrime := iotaPrimeS s
  muPprime := muPprimeS μ₀ s
  Vpp := VppS s
  intBXi := intBXiS μ₀ s
  intXi2 := intXi2S μ₀ s
  intB2 := intB2S s

/-- **Magnetic well dominates on every surface**: `∫|Ξ|²/|∇ψ|³ < s_ψ μ₀ p' V''` for
`0 < s ≤ 25`, i.e. exactly `WellDominant (s/50)` after the reductions. -/
theorem reactor_well_dominates {μ₀ s : ℝ} (hμ : 0 < μ₀) (hs : 0 < s) (hs' : s ≤ 25) :
    intXi2S μ₀ s < 1 * muPprimeS μ₀ s * VppS s := by
  rw [intXi2_eq hμ.ne' hs hs', well_term_eq hμ hs (by linarith)]
  have hW := normalized_well_dominance (s / 50) (by positivity) (by linarith)
  unfold WellDominant at hW
  have hQ := Qn_pos hs (by linarith : s < 45)
  have hπ := Real.pi_pos
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h4 : (0 : ℝ) < π ^ 4 * Qn (s / 50) ^ 3 := by positivity
  nlinarith [mul_lt_mul_of_pos_left hW h4]

/-- **Certified Mercier stability of the reactor Solov'ev equilibrium**: for every `μ₀ > 0`
and every flux surface `ψ̃ = s²` of the plasma, `0 < s ≤ 25` (`0 < ψ̃ ≤ L⁴/16`), the general
Mercier index (Landreman–Jorge eq. (3.1), supplied formula) is positive. -/
theorem reactor_mercier_stable {μ₀ : ℝ} (hμ : 0 < μ₀) {s : ℝ} (hs : 0 < s) (hs' : s ≤ 25) :
    MercierStable (reactorSurfaceData μ₀ s) :=
  mercierIndex_pos_of_well (intB2_pos hs hs') (reactor_well_dominates hμ hs hs')

/-- The magnetic well is genuine: `V'' < 0` (with `p' < 0`) on every surface. -/
theorem reactor_Vpp_neg {s : ℝ} (hs : 0 < s) (hs' : s ≤ 25) : VppS s < 0 := by
  have hμ : (0 : ℝ) < 1 := one_pos
  have h1 := reactor_well_dominates hμ hs hs'
  have hX : 0 ≤ intXi2S 1 s := by
    rw [intXi2_eq one_ne_zero hs hs']
    have hQ := Qn_pos hs (by linarith : s < 45)
    have : 0 ≤ IPhi (s / 50) := by
      unfold IPhi
      refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun t _ => ?_)
      have hv : 1 / 2 ≤ 1 + s / 50 * Real.sin t := by
        nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
      have hG := Gn_pos (ε := s / 50) (y := Real.sin t) (by positivity) (by linarith)
        ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
      unfold Phi
      have : 0 < √(1 + s / 50 * Real.sin t) := Real.sqrt_pos.2 (by linarith)
      have : 0 < 1 + s / 50 * Real.sin t := by linarith
      positivity
    have := Real.pi_pos
    positivity
  have hmu : muPprimeS 1 s < 0 := by
    unfold muPprimeS
    rw [mu_deriv_pressure one_ne_zero hs (by linarith)]
    have := deriv_fluxS_pos hs (by linarith : s < 45)
    apply div_neg_of_neg_of_pos _ this
    linarith
  nlinarith

end PlasmaLean.Design.SolovevMercierCertified
