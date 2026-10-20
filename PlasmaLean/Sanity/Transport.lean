/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Transport
public import PlasmaLean.Theory.Transport.Comparison
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp

/-!
# Sanity checks for the radial heat transport kernel

Checks for `PlasmaLean.Kernel.Transport`:

* the expanded operator agrees with the divergence form `(1/V')(V' D f')' + R`
  (`op_divergence_form`);
* with `V'` constant, `D` uniform and `R = 0` the kernel equation is the classical heat equation
  (`op_uniform`, `heat_equation_of_uniform`);
* a constant profile at a zero of `R` is a steady classical solution (`constField_solution`);
* a pointwise maximum principle: at a point with zero slope and nonpositive curvature (e.g. an
  interior spatial maximum, or the axis), `R ≤ 0` forces `∂ₜT ≤ 0` (`rate_nonpos_of_max`,
  `axis_rate_nonpos`). This is a weaker, honest substitute for "the maximum does not
  increase", whose proof needs the comparison theory;
* the separable modes `modeField` (aliases of `PlasmaLean.Transport.modeField`, defined in the
  theory layer `PlasmaLean.Theory.Transport.Comparison`, which this module imports; the theory
  layer does not import any sanity module);
* non-vacuity: the decaying cosine mode `e^{−π²t/4} cos(πψ/2)` is a `RadialHeatTransport`
  instance with zero edge data (`cosMode_radialHeatTransport`).
-/

public section

noncomputable section

namespace PlasmaLean.Transport.Sanity

open Set Real

/-- The expanded kernel operator is the divergence form: `(V' D f')' = V' (N[f] − R)`. -/
theorem op_divergence_form (c : RadialCoefficients) {f f' f'' : ℝ → ℝ} {ψ : ℝ}
    (hV : HasDerivAt c.Vp (c.dVp ψ) ψ) (hD : HasDerivAt c.D (c.dD ψ) ψ)
    (hf : HasDerivAt f' (f'' ψ) ψ) (hpos : c.Vp ψ ≠ 0) :
    HasDerivAt (fun x => c.Vp x * c.D x * f' x)
      (c.Vp ψ * (c.op ψ (f ψ) (f' ψ) (f'' ψ) - c.R ψ (f ψ))) ψ := by
  convert (hV.mul hD).mul hf using 1
  unfold RadialCoefficients.op
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- With `V'' = 0`, `D' = 0` and `R = 0` at `ψ`, the operator is `D ∂ψψ`. -/
theorem op_uniform (c : RadialCoefficients) {ψ u uψ uψψ : ℝ} (hdV : c.dVp ψ = 0)
    (hdD : c.dD ψ = 0) (hR : c.R ψ u = 0) : c.op ψ u uψ uψψ = c.D ψ * uψψ := by
  simp [RadialCoefficients.op, hdV, hdD, hR]

/-- Uniform diffusivity `κ`, constant volume derivative and no sources: a kernel solution
satisfies the classical heat equation `∂ₜT = κ ∂ψψT`. -/
theorem heat_equation_of_uniform {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ κ : ℝ}
    {u : RadialField} [hu : ClassicalRadialSolution c Tedge τ u]
    (hdV : ∀ ψ, c.dVp ψ = 0) (hD : ∀ ψ, c.D ψ = κ) (hdD : ∀ ψ, c.dD ψ = 0)
    (hR : ∀ ψ v, c.R ψ v = 0) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.Tt ψ t = κ * u.Tψψ ψ t := by
  intro ψ hψ t ht
  rw [ClassicalRadialSolution.pde (c := c) (τ := τ) (u := u) Tedge ψ hψ t ht,
    op_uniform c (hdV ψ) (hdD ψ) (hR ψ _), hD]

/-- The constant field with value `T₀` and vanishing derivatives. -/
@[expose] def constField (T₀ : ℝ) : RadialField :=
  ⟨fun _ _ => T₀, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- A constant profile at a zero of the net source (heating balances losses) is a steady
classical solution with constant edge data. -/
theorem constField_solution (c : RadialCoefficients) {T₀ τ : ℝ} (hτ : 0 ≤ τ)
    (hR : ∀ ψ ∈ Icc (0 : ℝ) 1, c.R ψ T₀ = 0) :
    ClassicalRadialSolution c (fun _ => T₀) τ (constField T₀) where
  tau_nonneg := hτ
  regular :=
    { cont := continuousOn_const
      deriv_ψ := fun _ _ _ _ => hasDerivWithinAt_const _ _ _
      deriv_ψψ := fun _ _ _ _ => hasDerivWithinAt_const _ _ _
      deriv_t := fun _ _ _ _ => hasDerivWithinAt_const _ _ _ }
  pde := fun ψ hψ _ _ => by simp [constField, RadialCoefficients.op, hR ψ hψ]
  axis := fun _ _ => rfl
  edge := fun _ _ => rfl

/-- Pointwise maximum principle: where the slope vanishes and the curvature is nonpositive,
`D ≥ 0` and `R ≤ 0` force the temperature not to increase. -/
theorem rate_nonpos_of_max {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ} {u : RadialField}
    [hu : ClassicalRadialSolution c Tedge τ u] {ψ t : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc 0 τ) (hD : 0 ≤ c.D ψ) (hR : c.R ψ (u.T ψ t) ≤ 0)
    (hslope : u.Tψ ψ t = 0) (hcurv : u.Tψψ ψ t ≤ 0) : u.Tt ψ t ≤ 0 := by
  rw [ClassicalRadialSolution.pde (c := c) (τ := τ) (u := u) Tedge ψ hψ t ht]
  unfold RadialCoefficients.op
  rw [hslope, mul_zero, add_zero]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hD hcurv]

/-- At the magnetic axis the slope vanishes by the no-flux condition, so nonpositive curvature
and `R ≤ 0` give `∂ₜT(0,t) ≤ 0`. -/
theorem axis_rate_nonpos {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ} {u : RadialField}
    [hu : ClassicalRadialSolution c Tedge τ u] {t : ℝ} (ht : t ∈ Icc 0 τ) (hD : 0 ≤ c.D 0)
    (hR : c.R 0 (u.T 0 t) ≤ 0) (hcurv : u.Tψψ 0 t ≤ 0) : u.Tt 0 t ≤ 0 :=
  rate_nonpos_of_max (Tedge := Tedge) ⟨le_rfl, zero_le_one⟩ ht hD hR
    (ClassicalRadialSolution.axis (c := c) (Tedge := Tedge) (τ := τ) (u := u) t ht) hcurv

/-- Unit coefficients: `V' = 1`, `D = 1`, no sources, floor `Dmin = 1`. -/
@[expose] def unitCoefficients : RadialCoefficients :=
  ⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => 0, fun _ _ => 0, 1⟩

/-- The unit coefficients satisfy the transport laws. -/
instance : TransportLaws unitCoefficients where
  Vp_pos := fun _ _ => one_pos
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  D_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  Dmin_pos := one_pos
  D_lower := fun _ _ => le_rfl
  R_cont := continuousOn_const

/-- The separable mode `a + b e^{μt} cos(kψ)` with its exact partial derivatives. This is a
name-preserving alias of `PlasmaLean.Transport.modeField`, which now lives in
`PlasmaLean.Theory.Transport.Comparison` so that the theory layer does not import this sanity
module. -/
abbrev modeField (a b μ k : ℝ) : RadialField := Transport.modeField a b μ k

/-- The separable mode is regular on every rectangle (alias of
`PlasmaLean.Transport.modeField_regular`). -/
theorem modeField_regular (a b μ k τ : ℝ) : (modeField a b μ k).Regular τ :=
  Transport.modeField_regular a b μ k τ

/-- **Non-vacuity.** The decaying cosine mode `e^{−π²t/4} cos(πψ/2)` solves the unit-coefficient
problem with axis no-flux and zero edge data. -/
instance cosMode_radialHeatTransport {τ : ℝ} [Fact (0 ≤ τ)] :
    RadialHeatTransport unitCoefficients (fun _ => 0) τ (modeField 0 1 (-(π ^ 2 / 4)) (π / 2)) where
  tau_nonneg := Fact.out
  regular := modeField_regular _ _ _ _ _
  pde := fun ψ _ t _ => by
    simp only [modeField, Transport.modeField, unitCoefficients, RadialCoefficients.op]
    ring
  axis := fun t _ => by simp [modeField, Transport.modeField]
  edge := fun t _ => by simp [modeField, Transport.modeField, cos_pi_div_two]

end PlasmaLean.Transport.Sanity
