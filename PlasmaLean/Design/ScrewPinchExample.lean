/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Equilibrium.ScrewPinch
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A Suydam-stable screw pinch at reactor-relevant parameters

An exact polynomial screw-pinch equilibrium (see `PlasmaLean.Equilibrium.ScrewPinch`)
with minor radius `a = 1 m` and periodic length `2πR₀`, `R₀ = 4 m` (aspect ratio 4). All
coefficients are exact rationals; the permeability `μ₀ > 0` is a parameter.

* axial field `Bz² = S(r) = 25 - 2r² + (5/2)r⁴ - r⁶/3` T², so `Bz(0) = 5 T`;
* azimuthal field `Bθ(r) = r - r³/2` T (peaked current, `Bθ(a) = 0.5 T`);
* pressure `p(r) = (1 - r⁴)/(2μ₀)` Pa, vanishing at the edge.

Checked consequences:

* `balance`: the cylindrical radial force balance holds identically, with `Bz² ≥ 22 T²`;
* `suydam_margin`: on every surface `0 < r ≤ 1`, the shear stabilization exceeds the
  pressure drive by at least 25% (relative Suydam margin `κ = 1/4`);
* `safetyFactor_ge`: `q ≥ 5/4` everywhere and `q(a) > 5/2` (Kruskal–Shafranov sanity);
* `shear_pos`: positive magnetic shear `q' > 0` at every surface;
* `beta_eq`: volume-averaged `β = 2/75 ≈ 2.7%`;
* with `μ₀` within `[1.2566, 1.2567] × 10⁻⁶` (true for `4π × 10⁻⁷`, `classical_mu0`):
  peak pressure `≈ 0.398 MPa` (12.4–12.5 keV at `n = 10²⁰ m⁻³`, `peak_temperature`),
  and plasma current `≈ 2.5 MA` (`plasma_current`).

Scope and honesty: this is a straight-cylinder screw pinch whose rotational transform
comes from a 2.5 MA plasma current. It is NOT a stellarator, it has no toroidal
curvature or coil geometry, and the density is a supplied illustrative value. Suydam's
criterion is a NECESSARY condition for ideal-MHD stability against localized
interchanges; it does not certify stability against kinks or other global modes,
free-boundary, resistive or kinetic instabilities. The example demonstrates the
exact-certificate route for a local stability criterion at realistic magnitudes.
-/
public section

noncomputable section
namespace PlasmaLean.Design.ScrewPinchExample
open Set PlasmaLean.Equilibrium.ScrewPinch

/-- Pressure `p(r) = (1 - r⁴)/(2μ₀)` in Pa. -/
@[expose] def pressure (μ₀ r : ℝ) : ℝ := 1 / (2 * μ₀) * (1 - r ^ 4)

/-- Pressure derivative `p'(r) = -2 r³/μ₀`. -/
@[expose] def pressure' (μ₀ r : ℝ) : ℝ := -(2 / μ₀) * r ^ 3

/-- Azimuthal field `Bθ(r) = r - r³/2` in T. -/
@[expose] def Bθ (r : ℝ) : ℝ := r - r ^ 3 / 2

/-- Derivative of the azimuthal field. -/
@[expose] def Bθ' (r : ℝ) : ℝ := 1 - 3 * r ^ 2 / 2

/-- Squared axial field `S = Bz²` in T². -/
@[expose] def S (r : ℝ) : ℝ := 25 - 2 * r ^ 2 + 5 / 2 * r ^ 4 - r ^ 6 / 3

/-- Derivative of the squared axial field. -/
@[expose] def S' (r : ℝ) : ℝ := -4 * r + 10 * r ^ 3 - 2 * r ^ 5

/-- `pressure'` is the actual derivative of `pressure`. -/
theorem pressure_hasDerivAt (μ₀ r : ℝ) : HasDerivAt (pressure μ₀) (pressure' μ₀ r) r := by
  have := ((hasDerivAt_pow 4 r).const_sub 1).const_mul (1 / (2 * μ₀))
  convert this using 1
  · rfl
  · simp only [pressure']; push_cast; ring

/-- `Bθ'` is the actual derivative of `Bθ`. -/
theorem Bθ_hasDerivAt (r : ℝ) : HasDerivAt Bθ (Bθ' r) r := by
  have := (hasDerivAt_id' r).sub ((hasDerivAt_pow 3 r).div_const 2)
  convert this using 1
  · rfl
  · simp only [Bθ']; push_cast; ring

/-- `S'` is the actual derivative of `S`. -/
theorem S_hasDerivAt (r : ℝ) : HasDerivAt S (S' r) r := by
  have := ((((hasDerivAt_pow 2 r).const_mul 2).const_sub 25).add
    ((hasDerivAt_pow 4 r).const_mul (5 / 2))).sub ((hasDerivAt_pow 6 r).div_const 3)
  convert this using 1
  · rfl
  · simp only [S']; push_cast; ring

/-- The squared axial field stays above `22 T²` on the plasma radius. -/
theorem S_ge {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 22 ≤ S r := by
  unfold S
  have hu : r ^ 2 ≤ 1 := by nlinarith
  nlinarith [pow_nonneg h0 4, pow_le_one₀ h0 h1 (n := 6), sq_nonneg (r ^ 2)]

/-- On-axis field strength `Bz(0) = 5 T`. -/
theorem axis_field : Real.sqrt (S 0) = 5 := by
  rw [show S 0 = 5 ^ 2 by norm_num [S]]; exact Real.sqrt_sq (by norm_num)

/-- Edge values: zero pressure and `Bθ(a) = 1/2 T`. -/
theorem edge_values (μ₀ : ℝ) : pressure μ₀ 1 = 0 ∧ Bθ 1 = 1 / 2 := by
  norm_num [pressure, Bθ]

/-- The azimuthal field is positive off the axis within the plasma. -/
theorem Bθ_pos {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : 0 < Bθ r := by
  unfold Bθ; nlinarith [mul_pos h0 h0, pow_pos h0 3]

/-- The exact profiles satisfy the cylindrical radial force balance on `(0, 1]`. -/
theorem balance {μ₀ : ℝ} (hμ : 0 < μ₀) :
    RadialBalance μ₀ 1 (pressure μ₀) Bθ S (pressure' μ₀) Bθ' S' where
  permeability_pos := hμ
  radius_pos := one_pos
  pressure_deriv r _ := pressure_hasDerivAt μ₀ r
  poloidal_deriv r _ := Bθ_hasDerivAt r
  axial_deriv r _ := S_hasDerivAt r
  axial_pos r hr := lt_of_lt_of_le (by norm_num) (S_ge hr.1.le hr.2)
  balance r hr := by
    have := hr.1.ne'
    unfold pressure' Bθ Bθ' S'
    field_simp
    ring

/-- `μ₀ p'` is independent of `μ₀`. -/
theorem mu_pressure' {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (r : ℝ) : μ₀ * pressure' μ₀ r = -2 * r ^ 3 := by
  unfold pressure'; field_simp

/-- Exact Suydam certificate: after clearing denominators and the margin, the
remainder is `r⁶ H(r²)`, `H(u) = 116 + 2896u - 980u² + …`, which is ≥ 116 on `[0, 1]`. -/
theorem suydam_certificate {μ₀ r : ℝ} (hμ : μ₀ ≠ 0) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    16 * r ^ 4 * S r * Bθ r ^ 2 ≤
      suydamNumerator Bθ S Bθ' S' r ^ 2 + 32 * r * S r * Bθ r ^ 2 * (μ₀ * pressure' μ₀ r) := by
  rw [mu_pressure' hμ]
  set u := r ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg r
  have hu1 : u ≤ 1 := by nlinarith
  have key : suydamNumerator Bθ S Bθ' S' r ^ 2 + 32 * r * S r * Bθ r ^ 2 * (-2 * r ^ 3) -
      16 * r ^ 4 * S r * Bθ r ^ 2 = u ^ 3 * (116 + 2896 * u - 980 * u ^ 2 + 796 / 3 * u ^ 3 -
        202 / 3 * u ^ 4 + 16 / 3 * u ^ 5 + 1 / 9 * u ^ 6) := by
    simp only [suydamNumerator, S, S', Bθ, Bθ', hu]; ring
  have hH : 0 ≤ 116 + 2896 * u - 980 * u ^ 2 + 796 / 3 * u ^ 3 - 202 / 3 * u ^ 4 +
      16 / 3 * u ^ 5 + 1 / 9 * u ^ 6 := by
    have a1 : 0 ≤ u * (2896 - 980 * u) := mul_nonneg hu0 (by linarith)
    have a2 : 0 ≤ u ^ 3 * (796 / 3 - 202 / 3 * u) := mul_nonneg (pow_nonneg hu0 3) (by linarith)
    nlinarith [pow_nonneg hu0 5, pow_nonneg hu0 6]
  nlinarith [mul_nonneg (pow_nonneg hu0 3) hH]

/-- Relative Suydam margin `1/4`: on every surface the shear term is at least `5/4` of
the pressure drive `-p'`. -/
theorem suydam_margin {μ₀ : ℝ} (hμ : 0 < μ₀) :
    SuydamMarginOn (1 / 4) μ₀ 1 (pressure' μ₀) Bθ S Bθ' S' := by
  unfold SuydamMarginOn
  intro r hr
  have hS : 0 < S r := lt_of_lt_of_le (by norm_num) (S_ge hr.1.le hr.2)
  have hB := Bθ_pos hr.1 hr.2
  have h := suydam_margin_of_polynomial hμ hr.1 hS hB.ne'
    (suydam_certificate hμ.ne' hr.1.le hr.2)
  convert h using 1
  unfold pressure'
  field_simp
  ring

/-- Suydam's criterion holds on every surface of the example. -/
theorem suydam_stable {μ₀ : ℝ} (hμ : 0 < μ₀) :
    SuydamStableOn μ₀ 1 (pressure' μ₀) Bθ S Bθ' S' :=
  (suydam_margin hμ).stable (by norm_num) (fun r hr => by
    unfold pressure'
    have := pow_pos hr.1 3
    have : 0 < 2 / μ₀ := by positivity
    nlinarith)

/-- Safety factor with `R₀ = 4 m`: `q ≥ 5/4` on every surface. -/
theorem safetyFactor_ge {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : 5 / 4 ≤ safetyFactor 4 Bθ S r := by
  have hB := Bθ_pos h0 h1
  unfold safetyFactor
  rw [le_div_iff₀ (by positivity)]
  have hS : (5 / 4 * (4 * (1 - r ^ 2 / 2))) ^ 2 ≤ S r := by
    unfold S
    have hu1 : r ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg r, pow_nonneg (sq_nonneg r) 3, mul_nonneg (sq_nonneg r) (sub_nonneg.2 hu1)]
  have hq : 5 / 4 * (4 * (1 - r ^ 2 / 2)) ≤ Real.sqrt (S r) :=
    Real.le_sqrt_of_sq_le hS
  have : 4 * Bθ r = r * (4 * (1 - r ^ 2 / 2)) := by unfold Bθ; ring
  rw [this]
  nlinarith

/-- Kruskal–Shafranov sanity at the edge: `q(a) > 5/2 > 1`. -/
theorem edge_safetyFactor : 5 / 2 < safetyFactor 4 Bθ S 1 := by
  unfold safetyFactor
  have e : S 1 = 151 / 6 := by norm_num [S]
  have hb : Bθ 1 = 1 / 2 := by norm_num [Bθ]
  rw [e, hb]
  have : (5 : ℝ) < Real.sqrt (151 / 6) := Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-- Positive magnetic shear on every surface: `q'/q > 0`. -/
theorem shear_pos {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : 0 < shearRatio Bθ S Bθ' S' r := by
  have hS : 0 < S r := lt_of_lt_of_le (by norm_num) (S_ge h0.le h1)
  have hB := Bθ_pos h0 h1
  have e : shearRatio Bθ S Bθ' S' r = suydamNumerator Bθ S Bθ' S' r / (2 * r * S r * Bθ r) := by
    unfold shearRatio suydamNumerator
    field_simp
  rw [e]
  apply div_pos _ (by positivity)
  have hu1 : r ^ 2 ≤ 1 := by nlinarith
  have hu0 := sq_nonneg r
  have key : suydamNumerator Bθ S Bθ' S' r = r ^ 3 * (46 + 8 * r ^ 2 - 2 * (r ^ 2) ^ 2 +
      (r ^ 2) ^ 3 / 3) := by
    simp only [suydamNumerator, S, S', Bθ, Bθ']; ring
  rw [key]
  apply mul_pos (pow_pos h0 3)
  nlinarith [pow_nonneg hu0 3]

/-- Volume-averaged beta `2 μ₀ ⟨p⟩ / Bz(0)²` with `⟨p⟩ = 2 ∫₀¹ r p dr`. -/
@[expose] def beta (μ₀ : ℝ) : ℝ := 2 * μ₀ * (2 * ∫ r in (0 : ℝ)..1, r * pressure μ₀ r) / S 0

/-- The volume-averaged beta is exactly `2/75 ≈ 2.7%`, independent of `μ₀ ≠ 0`. -/
theorem beta_eq {μ₀ : ℝ} (hμ : μ₀ ≠ 0) : beta μ₀ = 2 / 75 := by
  have hI : ∫ r in (0 : ℝ)..1, r * pressure μ₀ r = 1 / (6 * μ₀) := by
    have e : (fun r => r * pressure μ₀ r) = fun r => 1 / (2 * μ₀) * (r ^ 1 - r ^ 5) := by
      funext r; unfold pressure; ring
    rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (intervalIntegral.intervalIntegrable_pow 1) (intervalIntegral.intervalIntegrable_pow 5),
      integral_pow, integral_pow]
    field_simp
    norm_num
  unfold beta
  rw [hI]
  norm_num [S]
  field_simp
  norm_num

/-- Supplied permeability envelope (SI): `1.2566e-6 ≤ μ₀ ≤ 1.2567e-6` H/m. -/
@[expose] def MuBounds (μ₀ : ℝ) : Prop := 1.2566e-6 ≤ μ₀ ∧ μ₀ ≤ 1.2567e-6

/-- The classical value `4π × 10⁻⁷` lies in the envelope. -/
theorem classical_mu0 : MuBounds (4 * Real.pi * 1e-7) := by
  constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4]

/-- Peak pressure lies between 0.3978 and 0.3979 MPa. -/
theorem peak_pressure {μ₀ : ℝ} (h : MuBounds μ₀) :
    397800 < pressure μ₀ 0 ∧ pressure μ₀ 0 < 397900 := by
  obtain ⟨h1, h2⟩ := h
  have hμ : 0 < μ₀ := lt_of_lt_of_le (by norm_num) h1
  unfold pressure
  constructor
  · rw [show (1 - (0 : ℝ) ^ 4) = 1 by norm_num, mul_one, lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [show (1 - (0 : ℝ) ^ 4) = 1 by norm_num, mul_one, div_lt_iff₀ (by positivity)]
    nlinarith

/-- Equivalent temperature: with supplied `n = 10²⁰ m⁻³` (electrons and ions, `p = 2nT`)
and `e = 1.6022e-19` J/eV, the peak temperature is between 12.4 and 12.5 keV. -/
theorem peak_temperature {μ₀ : ℝ} (h : MuBounds μ₀) :
    2 * 1e20 * 1.6022e-19 * 12.4e3 < pressure μ₀ 0 ∧
      pressure μ₀ 0 < 2 * 1e20 * 1.6022e-19 * 12.5e3 := by
  obtain ⟨h1, h2⟩ := peak_pressure h
  constructor <;> norm_num <;> linarith

/-- Total plasma current `I = 2π a Bθ(a)/μ₀` lies between 2.49 and 2.51 MA. -/
theorem plasma_current {μ₀ : ℝ} (h : MuBounds μ₀) :
    2.49e6 < 2 * Real.pi * 1 * Bθ 1 / μ₀ ∧ 2 * Real.pi * 1 * Bθ 1 / μ₀ < 2.51e6 := by
  obtain ⟨h1, h2⟩ := h
  have hμ : 0 < μ₀ := lt_of_lt_of_le (by norm_num) h1
  have hb : Bθ 1 = 1 / 2 := by norm_num [Bθ]
  rw [hb]
  constructor
  · rw [lt_div_iff₀ hμ]; nlinarith [Real.pi_gt_d4]
  · rw [div_lt_iff₀ hμ]; nlinarith [Real.pi_lt_d4]

end PlasmaLean.Design.ScrewPinchExample
