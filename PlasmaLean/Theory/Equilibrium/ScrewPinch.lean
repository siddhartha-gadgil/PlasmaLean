/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.Suydam
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Cylindrical screw-pinch equilibria and the Suydam criterion

A screw pinch is a straight periodic cylinder (length `2πR₀`, the usual large-aspect-ratio
model of a torus) with profiles depending only on the radius `r`: pressure `p(r)`,
azimuthal field `Bθ(r)` and axial field `Bz(r)`. It is NOT a stellarator: here the field
line twist comes from a plasma current, whereas a stellarator produces rotational
transform with external three-dimensional coils. The screw pinch is the standard
testbed for localized interchange stability.

**Supplied reduced law.** `RadialBalance` is the radial component of static force balance
`J × B = ∇p` combined with Ampère's law in cylindrical symmetry (Freidberg, *Ideal MHD*,
2014, ch. 5):

  d/dr (p + (Bθ² + Bz²)/(2μ₀)) + Bθ²/(μ₀ r) = 0.

We write `S = Bz²` to avoid square roots. The derivation from the three-dimensional
`ForceBalance` kernel is not formalized here; the law is an explicit hypothesis.

**Suydam criterion.** With safety factor `q = r Bz/(R₀ Bθ)`, Suydam's (1958) necessary
condition for stability against localized interchanges is

  r Bz² (q'/q)² / (8 μ₀) + p' ≥ 0.

`suydamQuantity` is its left side, using the closed form `q'/q = 1/r + S'/(2S) - Bθ'/Bθ`
(`safetyFactor_hasDerivAt`). `suydam_polynomial_form` clears denominators, which makes
exact certificates for polynomial profiles straightforward.

**Link to the localized form.** `localF`, `localG` are the coefficients of the model
form `∫ (F x² ξ'² + G ξ²)` of `PlasmaLean.Stability.suydamForm`, up to the positive
weight `c` (in Newcomb's reduction `c = Bθ²/B²`). `local_criterion` shows
`F + 4G = 8c · suydamQuantity`, so the Hardy-inequality theorems give stability of the
model localized form when the criterion holds (`localized_stable`) and an explicit
unstable localized mode in every neighbourhood of the surface when it fails
(`localized_unstable`). The asymptotic reduction of the full δW to this form is not
formalized.

Scope: Suydam is a NECESSARY local condition for ideal-MHD stability. Satisfying it
does not certify stability against global (kink), free-boundary, resistive or kinetic
modes.
-/
public section

noncomputable section
namespace PlasmaLean.Equilibrium.ScrewPinch
open Set PlasmaLean.Stability

/-- Supplied cylindrical radial force balance on `(0, a]`, with explicit derivatives.
`S = Bz²` is the squared axial field; SI units. -/
structure RadialBalance (μ₀ a : ℝ) (p Bθ S p' Bθ' S' : ℝ → ℝ) : Prop where
  permeability_pos : 0 < μ₀
  radius_pos : 0 < a
  pressure_deriv : ∀ r ∈ Ioc 0 a, HasDerivAt p (p' r) r
  poloidal_deriv : ∀ r ∈ Ioc 0 a, HasDerivAt Bθ (Bθ' r) r
  axial_deriv : ∀ r ∈ Ioc 0 a, HasDerivAt S (S' r) r
  axial_pos : ∀ r ∈ Ioc 0 a, 0 < S r
  balance : ∀ r ∈ Ioc 0 a,
    p' r + (2 * Bθ r * Bθ' r + S' r) / (2 * μ₀) + Bθ r ^ 2 / (μ₀ * r) = 0

/-- Characterization: the balance law says the total (kinetic plus magnetic) pressure
decreases at the rate of the azimuthal-field tension `Bθ²/(μ₀ r)`. -/
theorem RadialBalance.total_pressure_deriv {μ₀ a : ℝ} {p Bθ S p' Bθ' S' : ℝ → ℝ}
    (h : RadialBalance μ₀ a p Bθ S p' Bθ' S') {r : ℝ} (hr : r ∈ Ioc 0 a) :
    HasDerivAt (fun r => p r + (Bθ r ^ 2 + S r) / (2 * μ₀)) (-(Bθ r ^ 2 / (μ₀ * r))) r := by
  have hd := (h.pressure_deriv r hr).add
    ((((h.poloidal_deriv r hr).pow 2).add (h.axial_deriv r hr)).div_const (2 * μ₀))
  convert hd using 1
  have := h.balance r hr
  norm_num
  linarith

/-- Sanity (theta pinch): without azimuthal field, total pressure is constant in `r`. -/
theorem RadialBalance.theta_pinch {μ₀ a : ℝ} {p S p' Bθ' S' : ℝ → ℝ}
    (h : RadialBalance μ₀ a p (fun _ => 0) S p' Bθ' S') {r : ℝ} (hr : r ∈ Ioc 0 a) :
    HasDerivAt (fun r => p r + ((0 : ℝ) ^ 2 + S r) / (2 * μ₀)) 0 r := by
  simpa using h.total_pressure_deriv hr

/-- The squared axial field has derivative `2 Bz Bz'`, so `S = Bz²` loses nothing. -/
theorem axial_sq_deriv {Bz : ℝ → ℝ} {Bz' r : ℝ} (h : HasDerivAt Bz Bz' r) :
    HasDerivAt (fun r => Bz r ^ 2) (2 * Bz r * Bz') r := by
  convert h.fun_pow 2 using 1
  simp

/-- Sanity: a uniform axial field with constant pressure and no current is an equilibrium. -/
theorem uniform_balance {μ₀ a p₀ S₀ : ℝ} (hμ : 0 < μ₀) (ha : 0 < a) (hS : 0 < S₀) :
    RadialBalance μ₀ a (fun _ => p₀) (fun _ => 0) (fun _ => S₀)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) where
  permeability_pos := hμ
  radius_pos := ha
  pressure_deriv _ _ := hasDerivAt_const _ _
  poloidal_deriv _ _ := hasDerivAt_const _ _
  axial_deriv _ _ := hasDerivAt_const _ _
  axial_pos _ _ := hS
  balance _ _ := by simp

/-- Safety factor `q = r Bz / (R₀ Bθ)` with `Bz = √S`. -/
@[expose] def safetyFactor (R₀ : ℝ) (Bθ S : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * Real.sqrt (S r) / (R₀ * Bθ r)

/-- Logarithmic shear `q'/q`, written through `S = Bz²`. -/
@[expose] def shearRatio (Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) : ℝ :=
  1 / r + S' r / (2 * S r) - Bθ' r / Bθ r

/-- Characterizing property: `shearRatio` is the logarithmic derivative of the actual
safety factor, `q' = q · shearRatio`. -/
theorem safetyFactor_hasDerivAt {R₀ : ℝ} {Bθ S Bθ' S' : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hR : R₀ ≠ 0) (hS : 0 < S r) (hB : Bθ r ≠ 0) (dS : HasDerivAt S (S' r) r)
    (dB : HasDerivAt Bθ (Bθ' r) r) :
    HasDerivAt (safetyFactor R₀ Bθ S)
      (safetyFactor R₀ Bθ S r * shearRatio Bθ S Bθ' S' r) r := by
  have hsq := Real.sqrt_pos.mpr hS
  have hd := ((hasDerivAt_id' r).mul (dS.sqrt hS.ne')).div (dB.const_mul R₀)
    (mul_ne_zero hR hB)
  convert hd using 1
  · rfl
  have e : Real.sqrt (S r) ^ 2 = S r := Real.sq_sqrt hS.le
  unfold safetyFactor shearRatio
  simp only [Pi.mul_apply]
  field_simp
  linear_combination (Bθ r * r * S' r) * e

/-- The safety factor is nonzero away from the axis when the fields are nonzero. -/
theorem safetyFactor_ne_zero {R₀ : ℝ} {Bθ S : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0) (hR : R₀ ≠ 0)
    (hS : 0 < S r) (hB : Bθ r ≠ 0) : safetyFactor R₀ Bθ S r ≠ 0 := by
  unfold safetyFactor
  exact div_ne_zero (mul_ne_zero hr (Real.sqrt_pos.mpr hS).ne') (mul_ne_zero hR hB)

/-- Zero shear ratio is exactly a stationary safety factor (shearless surface). -/
theorem shearRatio_eq_zero_iff {R₀ : ℝ} {Bθ S Bθ' S' : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hR : R₀ ≠ 0) (hS : 0 < S r) (hB : Bθ r ≠ 0) (dS : HasDerivAt S (S' r) r)
    (dB : HasDerivAt Bθ (Bθ' r) r) :
    deriv (safetyFactor R₀ Bθ S) r = 0 ↔ shearRatio Bθ S Bθ' S' r = 0 := by
  rw [(safetyFactor_hasDerivAt hr hR hS hB dS dB).deriv, mul_eq_zero]
  simp [safetyFactor_ne_zero hr hR hS hB]

/-- Suydam quantity `r Bz² (q'/q)²/(8μ₀) + p'`; nonnegativity is Suydam's criterion. -/
@[expose] def suydamQuantity (μ₀ : ℝ) (p' Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * S r * shearRatio Bθ S Bθ' S' r ^ 2 / (8 * μ₀) + p' r

/-- Polynomial numerator of the shear: `2 r S Bθ · (q'/q) = N`. -/
@[expose] def suydamNumerator (Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * S r * Bθ r + r * S' r * Bθ r - 2 * r * S r * Bθ' r

/-- Suydam's criterion holds on every surface of `(0, a]`. -/
@[expose] def SuydamStableOn (μ₀ a : ℝ) (p' Bθ S Bθ' S' : ℝ → ℝ) : Prop :=
  ∀ r ∈ Ioc 0 a, 0 ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r

/-- Relative margin `κ`: the shear term exceeds the pressure drive `-p'` by the factor
`1 + κ` on every surface of `(0, a]`. -/
@[expose] def SuydamMarginOn (κ μ₀ a : ℝ) (p' Bθ S Bθ' S' : ℝ → ℝ) : Prop :=
  ∀ r ∈ Ioc 0 a, κ * -p' r ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r

/-- A nonnegative relative margin with nonincreasing pressure implies Suydam stability. -/
theorem SuydamMarginOn.stable {κ μ₀ a : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (h : SuydamMarginOn κ μ₀ a p' Bθ S Bθ' S') (hκ : 0 ≤ κ)
    (hp : ∀ r ∈ Ioc 0 a, p' r ≤ 0) : SuydamStableOn μ₀ a p' Bθ S Bθ' S' := fun r hr =>
  le_trans (mul_nonneg hκ (neg_nonneg.mpr (hp r hr))) (h r hr)

/-- Clearing denominators: `32 μ₀ r S Bθ² · suydamQuantity = N² + 32 r S Bθ² (μ₀ p')`. -/
theorem suydam_polynomial_form {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : μ₀ ≠ 0)
    (hr : r ≠ 0) (hS : S r ≠ 0) (hB : Bθ r ≠ 0) :
    32 * μ₀ * r * S r * Bθ r ^ 2 * suydamQuantity μ₀ p' Bθ S Bθ' S' r =
      suydamNumerator Bθ S Bθ' S' r ^ 2 + 32 * r * S r * Bθ r ^ 2 * (μ₀ * p' r) := by
  unfold suydamQuantity shearRatio suydamNumerator
  field_simp
  ring

/-- Exact certificate route with margin: a lower bound `m` on the cleared polynomial
gives `suydamQuantity ≥ m / (32 μ₀ r S Bθ²)`. -/
theorem suydam_margin_of_polynomial {μ₀ r m : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀)
    (hr : 0 < r) (hS : 0 < S r) (hB : Bθ r ≠ 0)
    (h : m ≤ suydamNumerator Bθ S Bθ' S' r ^ 2 + 32 * r * S r * Bθ r ^ 2 * (μ₀ * p' r)) :
    m / (32 * μ₀ * r * S r * Bθ r ^ 2) ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  have hpos : 0 < 32 * μ₀ * r * S r * Bθ r ^ 2 := by
    have := pow_pos (abs_pos.mpr hB) 2
    rw [sq_abs] at this
    positivity
  rw [div_le_iff₀ hpos, mul_comm, suydam_polynomial_form hμ.ne' hr.ne' hS.ne' hB]
  exact h

/-- Exact certificate route: nonnegativity of the cleared polynomial is Suydam. -/
theorem suydam_of_polynomial {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀)
    (hr : 0 < r) (hS : 0 < S r) (hB : Bθ r ≠ 0)
    (h : 0 ≤ suydamNumerator Bθ S Bθ' S' r ^ 2 + 32 * r * S r * Bθ r ^ 2 * (μ₀ * p' r)) :
    0 ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  simpa using suydam_margin_of_polynomial hμ hr hS hB h

/-- Sanity: a nondecreasing pressure (no drive) satisfies Suydam. -/
theorem suydam_of_pressure_nondecreasing {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hr : 0 ≤ r) (hS : 0 ≤ S r) (hp : 0 ≤ p' r) :
    0 ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  unfold suydamQuantity
  positivity

/-- Sanity: a flat pressure profile satisfies Suydam. -/
theorem suydam_of_flat_pressure {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hr : 0 ≤ r) (hS : 0 ≤ S r) (hp : p' r = 0) :
    0 ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r :=
  suydam_of_pressure_nondecreasing hμ hr hS hp.ge

/-- Sanity: the uniform-field equilibrium is Suydam stable. -/
theorem uniform_suydam {μ₀ a S₀ : ℝ} (hμ : 0 < μ₀) (hS : 0 < S₀) :
    SuydamStableOn μ₀ a (fun _ => 0) (fun _ => 0) (fun _ => S₀) (fun _ => 0) (fun _ => 0) :=
  fun _ hr => suydam_of_flat_pressure hμ hr.1.le hS.le rfl

/-- Sanity: on a shearless surface any outward pressure decrease violates Suydam. -/
theorem suydam_fails_shearless {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hsh : shearRatio Bθ S Bθ' S' r = 0) (hp : p' r < 0) :
    suydamQuantity μ₀ p' Bθ S Bθ' S' r < 0 := by
  simp [suydamQuantity, hsh, hp]

/-! ## Coefficients of the localized form -/

/-- Shear coefficient of the localized form, with positive weight `c`. -/
@[expose] def localF (μ₀ c : ℝ) (Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) : ℝ :=
  c * r * S r * shearRatio Bθ S Bθ' S' r ^ 2 / μ₀

/-- Pressure-drive coefficient of the localized form, with positive weight `c`. -/
@[expose] def localG (c : ℝ) (p' : ℝ → ℝ) (r : ℝ) : ℝ := 2 * c * p' r

/-- The localized-form criterion `F + 4G ≥ 0` is Suydam's criterion, scaled by `8c`. -/
theorem local_criterion {μ₀ c r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : μ₀ ≠ 0) :
    localF μ₀ c Bθ S Bθ' S' r + 4 * localG c p' r =
      8 * c * suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  unfold localF localG suydamQuantity
  field_simp
  ring

/-- The shear coefficient is nonnegative. -/
theorem localF_nonneg {μ₀ c r : ℝ} {Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hS : 0 ≤ S r) : 0 ≤ localF μ₀ c Bθ S Bθ' S' r := by
  unfold localF
  positivity

/-- Sufficiency: where Suydam holds, the model localized energy is nonnegative for every
admissible displacement vanishing at the endpoints. -/
theorem localized_stable {μ₀ c r x₀ x₁ : ℝ} {p' Bθ S Bθ' S' ξ ξ' : ℝ → ℝ} (hμ : 0 < μ₀)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hS : 0 ≤ S r)
    (hsu : 0 ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r) (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0) :
    0 ≤ suydamForm (localF μ₀ c Bθ S Bθ' S' r) (localG c p' r) x₀ x₁ ξ ξ' := by
  refine suydamForm_nonneg (localF_nonneg hμ hc hr hS) ?_ hle hξ h₀ h₁
  rw [local_criterion hμ.ne']
  positivity

/-- Necessity: where Suydam fails, every neighbourhood `(0, ε)` of the resonant surface
carries an admissible localized displacement with negative model energy. -/
theorem localized_unstable {μ₀ c r ε : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀)
    (hc : 0 < c) (hr : 0 ≤ r) (hS : 0 ≤ S r)
    (hsu : suydamQuantity μ₀ p' Bθ S Bθ' S' r < 0) (hε : 0 < ε) :
    ∃ x₀ x₁ : ℝ, ∃ ξ ξ' : ℝ → ℝ, 0 < x₀ ∧ x₀ ≤ x₁ ∧ x₁ < ε ∧ C1On ξ ξ' x₀ x₁ ∧
      ξ x₀ = 0 ∧ ξ x₁ = 0 ∧
      suydamForm (localF μ₀ c Bθ S Bθ' S' r) (localG c p' r) x₀ x₁ ξ ξ' < 0 := by
  set F := localF μ₀ c Bθ S Bθ' S' r
  set G := localG c p' r
  have hcrit : F + 4 * G < 0 := by
    rw [local_criterion hμ.ne']
    exact mul_neg_of_pos_of_neg (by positivity) hsu
  have hF : 0 ≤ F := localF_nonneg hμ hc.le hr hS
  rcases hF.eq_or_lt with hF0 | hFpos
  · -- Shearless surface: compare with an auxiliary positive shear `F₁ = -G`.
    have hG : G < 0 := by linarith
    obtain ⟨x₀, x₁, ξ, ξ', h0, hle, h1, hC, e0, e1, hneg⟩ :=
      suydam_unstable_near_resonance (F := -G) (G := G) (by linarith) (by linarith) hε
    refine ⟨x₀, x₁, ξ, ξ', h0, hle, h1, hC, e0, e1, ?_⟩
    rw [suydamForm_eq hC] at hneg ⊢
    have hw : 0 ≤ ∫ x in x₀..x₁, x ^ 2 * ξ' x ^ 2 :=
      intervalIntegral.integral_nonneg hle (fun x _ => by positivity)
    rw [← hF0]
    nlinarith
  · exact suydam_unstable_near_resonance hFpos hcrit hε

end PlasmaLean.Equilibrium.ScrewPinch
