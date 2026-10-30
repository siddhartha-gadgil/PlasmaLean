/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevAlpha
public import PlasmaLean.Design.HelicalReactorScale
public import PlasmaLean.Design.LandremanEquilibrium
public import PlasmaLean.Design.LandremanFamily2MercierStable

/-!
# Force balance with the actual pressure gradient (audit finding E-1)

The kernel law `ForceBalance B J g` (`J × B = g`) holds for every `B`, `J` when `g := J × B`
(`Sanity.Audit.forceBalance_of_cross`), so a force-balance claim has content only when `g` is
identified with the gradient of a pressure. The analytic equilibria state force balance with a
named vector field `pressureGrad …` and prove separately that it is the Fréchet derivative of the
pressure (`pressure_hasFDerivAt`). This module composes the two, restating each force-balance
theorem with `g = ∇p` written as Mathlib's `gradient` of the explicit pressure function, so that
the statement itself carries the identification:

* `solovev_force_balance_gradient`, `solovev_reactor_force_balance_gradient` (Solov'ev,
  `Design/Solovev`, `Design/SolovevAlpha`);
* `helical_force_balance_gradient`, `helical_scaled_force_balance_gradient` (helical,
  `Design/HelicalEquilibrium`, `Design/HelicalReactorScale`);
* `landreman1_force_balance_gradient`, `landreman1_force_balance_SI_gradient` (Landreman
  family 1), `landreman2_force_balance_gradient`, `landreman2_force_balance_SI_gradient`
  (family 2), and `family2_lam200_force_balance_gradient` (the certified `λ = 200` member of
  `Design/LandremanFamily2MercierStable`).

In every case `J = (∇ × B)/μ₀` is the actual Ampère current (by definition of `current`,
`currentSI`, `physCurrent`). The Solov'ev band designs (`Design/SolovevBand*`,
`SolovevCoarea`, `SolovevFluxGeometry`, `SolovevOnePlasma`) already state force balance with
`gradient (offsetPressure μ₀ Δ) x`, and `Design/ValidatedSlabEquilibrium` with
`deriv p` of its explicit pressure, so they need no companion here.
-/

public section
noncomputable section

namespace PlasmaLean.Design.ForceBalanceGradient
open PlasmaLean.Fields WithLp

/-- If `f` has Fréchet derivative `⟪v, ·⟫` at `x`, then its (Mathlib) gradient at `x` is `v`. -/
theorem gradient_eq_of_hasFDerivAt {f : Space → ℝ} {v x : Space}
    (h : HasFDerivAt f (innerSL ℝ v) x) : gradient f x = v := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  have e : InnerProductSpace.toDual ℝ Space v = innerSL ℝ v := by
    ext w; simp [InnerProductSpace.toDual_apply_apply]
  rw [e]
  exact h

/-! ## Solov'ev -/

/-- **Solov'ev force balance with `∇p`.** Off the vertical axis, `J × B = ∇p` with the Ampère
current and the gradient of the pressure `p = p₀ − (3c²/μ₀) ψ̃`, for every `p₀`. -/
theorem solovev_force_balance_gradient (μ₀ p₀ A L F : ℝ) (hμ : μ₀ ≠ 0) {x : Space}
    (hx : Solovev.R2 x ≠ 0) :
    ForceBalance (ofLp (Solovev.field A L F x)) (ofLp (Solovev.current μ₀ A L F x))
      (ofLp (gradient (Solovev.pressure μ₀ p₀ A L) x)) := by
  rw [gradient_eq_of_hasFDerivAt (Solovev.pressure_hasFDerivAt μ₀ p₀ A L x)]
  exact Solovev.force_balance μ₀ A L F hμ hx

/-- **Reactor Solov'ev force balance with `∇p`** (`reactorPressure`). -/
theorem solovev_reactor_force_balance_gradient (μ₀ : ℝ) (hμ : μ₀ ≠ 0) {x : Space}
    (hx : Solovev.R2 x ≠ 0) :
    ForceBalance (ofLp (SolovevAlpha.reactorField x))
      (ofLp (Solovev.current μ₀ (7 / 4) 10 50 x))
      (ofLp (gradient (SolovevAlpha.reactorPressure μ₀) x)) := by
  rw [gradient_eq_of_hasFDerivAt (SolovevAlpha.reactor_pressure_hasFDerivAt μ₀ x)]
  exact SolovevAlpha.reactor_force_balance μ₀ hμ hx

/-! ## Helical -/

/-- **Helical force balance with `∇p`** at every point, for the pressure
`p = (p₀ − 4ψ)/μ₀` and every `p₀`. -/
theorem helical_force_balance_gradient (μ₀ p₀ a : ℝ) (x : Space) :
    ForceBalance (ofLp (HelicalEquilibrium.eqField a x))
      (ofLp (HelicalEquilibrium.current μ₀ a x))
      (ofLp (gradient (HelicalEquilibrium.pressure μ₀ p₀ a) x)) := by
  rw [gradient_eq_of_hasFDerivAt (HelicalEquilibrium.pressure_hasFDerivAt μ₀ p₀ a x)]
  exact HelicalEquilibrium.force_balance μ₀ a x

/-- **Reactor-scale helical force balance with `∇p`** (`physPressure`), at every point. -/
theorem helical_scaled_force_balance_gradient (μ₀ p₀ Bu L : ℝ) (X : Space) :
    ForceBalance (ofLp (HelicalReactorScale.physField Bu L X))
      (ofLp (HelicalReactorScale.physCurrent μ₀ Bu L X))
      (ofLp (gradient (HelicalReactorScale.physPressure μ₀ p₀ Bu L) X)) := by
  rw [gradient_eq_of_hasFDerivAt (HelicalReactorScale.physPressure_hasFDerivAt μ₀ p₀ Bu L X)]
  exact HelicalReactorScale.scaled_force_balance μ₀ Bu L X

/-! ## Landreman family 1 -/

/-- **Landreman family 1 force balance with `∇p`** on `𝒰`, for `p = (p_a − 2ψ)/μ₀`. -/
theorem landreman1_force_balance_gradient {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (μ₀ pa : ℝ)
    {x : Space} (hx : x ∈ LandremanEquilibrium.U a b) :
    ForceBalance (ofLp (LandremanEquilibrium.field a b x))
      (ofLp (LandremanEquilibrium.current μ₀ a b x))
      (ofLp (gradient (LandremanEquilibrium.pressure μ₀ pa a b) x)) := by
  rw [gradient_eq_of_hasFDerivAt (LandremanEquilibrium.pressure_hasFDerivAt μ₀ pa a b hx)]
  exact LandremanEquilibrium.force_balance ha hb μ₀ hx

/-- **Landreman family 1 SI force balance with `∇p`**, at every `x` with `x/L ∈ 𝒰`. -/
theorem landreman1_force_balance_SI_gradient {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (μ₀ B₀ L pa : ℝ) {x : Space} (hx : L⁻¹ • x ∈ LandremanEquilibrium.U a b) :
    ForceBalance (ofLp (LandremanEquilibrium.fieldSI B₀ L a b x))
      (ofLp (LandremanEquilibrium.currentSI μ₀ B₀ L a b x))
      (ofLp (gradient (LandremanEquilibrium.pressureSI μ₀ B₀ L pa a b) x)) := by
  rw [gradient_eq_of_hasFDerivAt
    (LandremanEquilibrium.pressureSI_hasFDerivAt μ₀ B₀ L pa a b hx)]
  exact LandremanEquilibrium.force_balance_SI ha hb μ₀ B₀ L hx

/-! ## Landreman family 2 -/

/-- **Landreman family 2 force balance with `∇p`** on `𝒰`, for `p = (p_a − ψ/λ²)/μ₀`. -/
theorem landreman2_force_balance_gradient {ε S lam : ℝ} (hl : lam ≠ 0) (μ₀ pa : ℝ)
    {x : Space} (hx : x ∈ LandremanFamily2.U ε) :
    ForceBalance (ofLp (LandremanFamily2.field ε S lam x))
      (ofLp (LandremanFamily2.current μ₀ ε S lam x))
      (ofLp (gradient (LandremanFamily2.pressure μ₀ pa ε S lam) x)) := by
  rw [gradient_eq_of_hasFDerivAt (LandremanFamily2.pressure_hasFDerivAt μ₀ pa ε S lam hx)]
  exact LandremanFamily2.force_balance hl μ₀ hx

/-- **Landreman family 2 SI force balance with `∇p`**, at every `x` with `x/L ∈ 𝒰`. -/
theorem landreman2_force_balance_SI_gradient {ε S lam : ℝ} (hl : lam ≠ 0) (μ₀ B₀ L pa : ℝ)
    {x : Space} (hx : L⁻¹ • x ∈ LandremanFamily2.U ε) :
    ForceBalance (ofLp (LandremanFamily2.fieldSI B₀ L ε S lam x))
      (ofLp (LandremanFamily2.currentSI μ₀ B₀ L ε S lam x))
      (ofLp (gradient (LandremanFamily2.pressureSI μ₀ B₀ L pa ε S lam) x)) := by
  rw [gradient_eq_of_hasFDerivAt
    (LandremanFamily2.pressureSI_hasFDerivAt μ₀ B₀ L pa ε S lam hx)]
  exact LandremanFamily2.force_balance_SI hl μ₀ B₀ L hx

/-- **The certified `λ = 200` member with `∇p`** (companion of
`LandremanFamily2Cert.family2_lam200_equilibrium`): on the smooth region,
`J × B = ∇p` for the same pressure `p = (81/200 − ψ)/(λ² μ₀)` whose positivity inside the
plasma and vanishing on its boundary that theorem proves. -/
theorem family2_lam200_force_balance_gradient (μ₀ : ℝ) {x : Space}
    (hx : x ∈ LandremanFamily2.U (1 / 4)) :
    ForceBalance (ofLp (LandremanFamily2.field (1 / 4) 4 200 x))
      (ofLp (LandremanFamily2.current μ₀ (1 / 4) 4 200 x))
      (ofLp (gradient (LandremanFamily2.pressure μ₀ ((81 / 200) / 200 ^ 2) (1 / 4) 4 200) x)) :=
  landreman2_force_balance_gradient (by norm_num) μ₀ _ hx

end PlasmaLean.Design.ForceBalanceGradient
