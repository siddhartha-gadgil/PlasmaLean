/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevAlpha
public import PlasmaLean.Theory.Stability.MercierGeneral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Safety factor and Mercier stability of the reactor-scale Solov'ev equilibrium

For the Solov'ev family `ψ̃ = R² z²/2 + (R² - L²)²/4` of `PlasmaLean.Design.Solovev` we
construct the **exact field lines** on every flux surface `ψ̃ = c = s²` with `2s < L²`:

  `R(t)² = u(t) = L² + 2 s sin t`,  `z(t) = √2 s cos t / R(t)`,
  `φ(t) = -(F L²/(√2 A)) ∫₀ᵗ R(τ)⁻³ dτ`.

Proved (rigorous, standard axioms):

* `lineS_on_surface`: the curve lies on the flux surface, `ψ̃ = s²`;
* `lineS_fieldLine`: it is a reparametrized field line of the actual Solov'ev field,
  `X'(t) = λ(t) B(X(t))` with `λ = -L²/(√2 A R) ≠ 0` (no flux-coordinate or coarea identity is
  assumed);
* `RS_periodic`, `zS_periodic`, `phiS_winding`: after one poloidal circuit (`t ↦ t + 2π`) the
  poloidal position `(R, z)` returns and the toroidal angle has decreased by exactly
  `2π q(s)`, where
  `qS A L F s = (F L²/(√2 A)) (1/2π) ∫_{-π}^{π} (L² + 2 s sin t)^{-3/2} dt`.
  So `qS` IS the safety factor (toroidal turns per poloidal turn of the actual field lines),
  linking the on-axis formula of `SolovevAlpha.reactor_q0_formula_bounds` to the true definition;
* `qS_zero`: on the axis limit `s = 0`, `q = F/(√2 A L)`;
* `qS_ge_axis`: `q(s) ≥ q(0)` on EVERY surface (tangent-line convexity bound
  `u^{-3/2} ≥ L^{-3} - 3 s sin t/L⁵`, integrated);
* reactor instance (`A = 7/4 T`, `L = 10 m`, `F = 50 T m`): `reactor_q_axis` gives
  `q(0) ∈ [2.02, 2.021]` and `reactor_q_ge` gives `q ≥ 2.02 > 1` on every flux surface of the
  plasma `0 ≤ ψ̃ ≤ L⁴/16` (`s ≤ 25`).

**Mercier, large-aspect-ratio form (supplied formula).** `reactor_mercierTokamak` only records
the SIGN of the Shafranov–Yurchenko expression `Mercier.mercierTokamakQ`: it is `≥ 0` whenever
`q ≥ 1` and `p' ≤ 0`, whatever the shear. Here `q` is the true safety factor (`q ≥ 2.02` is
proved for the field), but the effective cylindrical profiles `Bθ, S, p'` and the radius
labelling are arbitrary inputs, NOT derived from the Solov'ev field. Caveat: that formula is a
circular, large-aspect-ratio asymptotic; this plasma has aspect ratio ≈ 3.9 and elongation
`√2` on axis, so this is only an indicative check.

**Mercier, exact axisymmetric index: numerical finding, NOT certified.** Untrusted oracle
`scripts/solovev_mercier_oracle.py` evaluates the general index
(`MercierGeneral.mercierIndex`, Landreman–Jorge eq. (3.1)) using the exact parametrization
above, for which `dl/|∇ψ̃| = dt/(√2 u)` (implied by `lineS_fieldLine`), with `μ₀J·B = 3AF/L²`
constant. Results (toroidal-flux label): `D_Merc > 0` on all tested surfaces
`ψ̃ ∈ {1, 5, 25, 100, 200, 400, 625}` (`D_Merc ≈ 4.6e-4 … 6.0e-7`, `∝ 1/ψ̃` near the axis);
`q` rises from 2.021 to 2.649 at the edge; `V'' < 0` (magnetic well); and the well alone
dominates, `μ₀p'V'' / ∫|Ξ|²/|∇ψ|³ ≈ 1.41` (axis) to `1.74` (edge), which is exactly the
hypothesis of `MercierGeneral.mercierIndex_pos_of_well`. `oracle_edge_stable` records that the
rounded edge numbers satisfy it (a fixture showing how the certificate would close; the
surface integrals are NOT rigorously enclosed here — that needs validated quadrature in `t`
and a derivative-under-the-integral bound for `V''`).

Not done: ballooning on a chosen surface (the line-certificate coefficients need the same
surface integrands with rigorous bounds).

Scope: ideal local interchange (necessary condition) only; static axisymmetric equilibrium;
the field lines are explicit, so no existence assumption is needed for them.
-/

public section
noncomputable section
namespace PlasmaLean.Design.SolovevMercier
open Set Real PlasmaLean.Fields PlasmaLean.Design.Solovev PlasmaLean.Stability.MercierGeneral
  WithLp

/-! ## Explicit flux-surface field lines -/

/-- `u(t) = R(t)² = L² + 2 s sin t`. -/
@[expose] def uS (L s t : ℝ) : ℝ := L ^ 2 + 2 * s * Real.sin t

/-- Major radius along the line, `R(t) = √u(t)`. -/
@[expose] def RS (L s t : ℝ) : ℝ := Real.sqrt (uS L s t)

/-- Height along the line, `z(t) = √2 s cos t / R(t)`. -/
@[expose] def zS (L s t : ℝ) : ℝ := Real.sqrt 2 * s * Real.cos t / RS L s t

/-- Toroidal winding rate constant `F L²/(√2 A)`. -/
@[expose] def rateS (A L F : ℝ) : ℝ := F * L ^ 2 / (Real.sqrt 2 * A)

/-- Toroidal angle along the line, `φ(t) = -(F L²/(√2 A)) ∫₀ᵗ R⁻³`. -/
@[expose] def phiS (A L F s t : ℝ) : ℝ :=
  -(rateS A L F * ∫ τ in (0 : ℝ)..t, (RS L s τ ^ 3)⁻¹)

/-- The field line `X(t) = (R cos φ, R sin φ, z)`. -/
@[expose] def lineS (A L F s t : ℝ) : Space :=
  toLp 2 ![RS L s t * Real.cos (phiS A L F s t), RS L s t * Real.sin (phiS A L F s t), zS L s t]

/-- Reparametrization factor `λ(t) = -L²/(√2 A R(t))`. -/
@[expose] def lamS (A L s t : ℝ) : ℝ := -(L ^ 2 / (Real.sqrt 2 * A * RS L s t))

/-- The safety factor of the surface `ψ̃ = s²`:
`q = (F L²/(√2 A)) (1/2π) ∫_{-π}^{π} R(t)⁻³ dt`. -/
@[expose] def qS (A L F s : ℝ) : ℝ := rateS A L F * (∫ τ in (-π)..π, (RS L s τ ^ 3)⁻¹) / (2 * π)

section
variable {A L F s : ℝ}

/-- `u(t) > 0` when `2s < L²`. -/
theorem uS_pos (hs : 0 ≤ s) (h : 2 * s < L ^ 2) (t : ℝ) : 0 < uS L s t := by
  unfold uS
  nlinarith [Real.neg_one_le_sin t]

/-- `R(t) > 0`. -/
theorem RS_pos (hs : 0 ≤ s) (h : 2 * s < L ^ 2) (t : ℝ) : 0 < RS L s t :=
  Real.sqrt_pos.mpr (uS_pos hs h t)

/-- `R(t)² = u(t)`. -/
theorem RS_sq (hs : 0 ≤ s) (h : 2 * s < L ^ 2) (t : ℝ) : RS L s t ^ 2 = uS L s t :=
  Real.sq_sqrt (uS_pos hs h t).le

/-- `R` is continuous. -/
theorem continuous_RS : Continuous (RS L s) := by
  unfold RS uS; fun_prop

/-- `t ↦ R(t)⁻³` is continuous. -/
theorem continuous_invCube (hs : 0 ≤ s) (h : 2 * s < L ^ 2) :
    Continuous (fun τ => (RS L s τ ^ 3)⁻¹) :=
  ((continuous_RS).pow 3).inv₀ fun τ => (pow_pos (RS_pos hs h τ) 3).ne'

/-- `R(t)` and `z(t)` are `2π`-periodic: the poloidal position returns after one circuit. -/
theorem RS_periodic (t : ℝ) : RS L s (t + 2 * π) = RS L s t := by
  simp [RS, uS, Real.sin_add_two_pi]

/-- Periodicity of `z(t)`. -/
theorem zS_periodic (t : ℝ) : zS L s (t + 2 * π) = zS L s t := by
  simp [zS, RS_periodic, Real.cos_add_two_pi]

/-- The line lies on the flux surface `ψ̃ = s²`. -/
theorem lineS_on_surface (hs : 0 ≤ s) (h : 2 * s < L ^ 2) (t : ℝ) :
    psiT L (lineS A L F s t) = s ^ 2 := by
  have hR := RS_pos hs h t
  have hR2 := RS_sq hs h t
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hc := Real.sin_sq_add_cos_sq (phiS A L F s t)
  have hct := Real.sin_sq_add_cos_sq t
  have hR2' : R2 (lineS A L F s t) = uS L s t := by
    simp only [R2, lineS, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hR2]; linear_combination RS L s t ^ 2 * hc
  unfold psiT
  rw [hR2']
  simp only [lineS, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead,
    Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero, zS]
  rw [← hR2]
  field_simp
  rw [hR2]
  unfold uS
  linear_combination (4 * s ^ 2 * Real.cos t ^ 2) * h2 + 8 * s ^ 2 * hct

/-- **Exact field line.** `X'(t) = λ(t) B(X(t))` for the actual Solov'ev field, with
`λ = -L²/(√2 A R) ≠ 0`. -/
theorem lineS_fieldLine (hA : A ≠ 0) (hL : L ≠ 0) (hs : 0 ≤ s) (h : 2 * s < L ^ 2) (t : ℝ) :
    HasDerivAt (lineS A L F s) (lamS A L s t • field A L F (lineS A L F s t)) t := by
  have hR := RS_pos hs h t
  have hRne := hR.ne'
  have hR2 := RS_sq hs h t
  have h2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  -- derivatives of the pieces
  have hu : HasDerivAt (uS L s) (2 * s * Real.cos t) t := by
    have := ((Real.hasDerivAt_sin t).const_mul (2 * s)).const_add (L ^ 2)
    convert this using 1
    funext y; rfl
  have hRd : HasDerivAt (RS L s) (2 * s * Real.cos t / (2 * RS L s t)) t :=
    hu.sqrt (uS_pos hs h t).ne'
  have hzd : HasDerivAt (zS L s)
      ((Real.sqrt 2 * s * -Real.sin t * RS L s t -
        Real.sqrt 2 * s * Real.cos t * (2 * s * Real.cos t / (2 * RS L s t))) /
          RS L s t ^ 2) t := by
    have := ((Real.hasDerivAt_cos t).const_mul (Real.sqrt 2 * s)).div hRd hRne
    convert this using 1
    funext y; rfl
  have hphi : HasDerivAt (phiS A L F s) (-(rateS A L F * (RS L s t ^ 3)⁻¹)) t := by
    have := (((continuous_invCube hs h).integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul
      (rateS A L F)).neg
    exact this
  have hx := hRd.mul (hphi.cos)
  have hy := hRd.mul (hphi.sin)
  have hc : HasDerivAt (fun τ => ![RS L s τ * Real.cos (phiS A L F s τ),
      RS L s τ * Real.sin (phiS A L F s τ), zS L s τ])
      ![2 * s * Real.cos t / (2 * RS L s t) * Real.cos (phiS A L F s t) +
          RS L s t * (-Real.sin (phiS A L F s t) * -(rateS A L F * (RS L s t ^ 3)⁻¹)),
        2 * s * Real.cos t / (2 * RS L s t) * Real.sin (phiS A L F s t) +
          RS L s t * (Real.cos (phiS A L F s t) * -(rateS A L F * (RS L s t ^ 3)⁻¹)),
        (Real.sqrt 2 * s * -Real.sin t * RS L s t -
          Real.sqrt 2 * s * Real.cos t * (2 * s * Real.cos t / (2 * RS L s t))) /
            RS L s t ^ 2] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    exacts [hx, hy, hzd]
  have hfin := PlasmaLean.Kinetic.hasDerivAt_toLp hc
  change HasDerivAt (fun τ => (toLp 2 ![RS L s τ * Real.cos (phiS A L F s τ),
      RS L s τ * Real.sin (phiS A L F s τ), zS L s τ] : Space)) _ t
  convert hfin using 1
  have hR2' : R2 (lineS A L F s t) = RS L s t ^ 2 := by
    simp only [R2, lineS, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination RS L s t ^ 2 * Real.sin_sq_add_cos_sq (phiS A L F s t)
  apply PlasmaLean.Fields.space_ext
  · simp only [field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, lamS]
    rw [hR2']
    simp only [PiLp.toLp_apply, lineS, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, zS, rateS]
    field_simp
    ring
  · simp only [field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, lamS]
    rw [hR2']
    simp only [PiLp.toLp_apply, lineS, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, zS, rateS]
    field_simp
    ring
  · simp only [field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, lamS]
    rw [hR2']
    simp only [PiLp.toLp_apply, lineS, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, zS, rateS]
    field_simp
    have hR4 : RS L s t ^ 4 = (L ^ 2 + 2 * s * Real.sin t) ^ 2 := by
      rw [show RS L s t ^ 4 = (RS L s t ^ 2) ^ 2 by ring, hR2]; rfl
    rw [hR4, h2]
    try rw [hR2]
    unfold uS
    ring

/-- **Winding number.** After one poloidal circuit the toroidal angle has changed by exactly
`-2π q(s)`: `qS` is the field-line safety factor of the surface `ψ̃ = s²`. -/
theorem phiS_winding (hs : 0 ≤ s) (h : 2 * s < L ^ 2) (t : ℝ) :
    phiS A L F s (t + 2 * π) = phiS A L F s t - 2 * π * qS A L F s := by
  have hc := continuous_invCube hs h
  have hper : Function.Periodic (fun τ => (RS L s τ ^ 3)⁻¹) (2 * π) := fun τ => by
    simp only [RS_periodic]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) t (t + 2 * π))
  have hshift := hper.intervalIntegral_add_eq t (-π)
  rw [show -π + 2 * π = π by ring] at hshift
  unfold phiS qS
  rw [← hsplit, hshift]
  field_simp
  ring

/-- On the axis limit `s = 0` the safety factor is `q₀ = F/(√2 A L)`. -/
theorem qS_zero (hA : A ≠ 0) (hL : 0 < L) : qS A L F 0 = F / (Real.sqrt 2 * A * L) := by
  have hR : ∀ τ, RS L 0 τ = L := fun τ => by
    simp [RS, uS, Real.sqrt_sq hL.le]
  simp only [qS, hR, intervalIntegral.integral_const, smul_eq_mul, rateS]
  have := pi_pos
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Tangent-line bound for `u^{-3/2}` at `u = L²`: `R⁻³ ≥ L⁻³ - 3 s sin t / L⁵`. -/
theorem invCube_ge (hL : 0 < L) (hs : 0 ≤ s) (h : 2 * s < L ^ 2) (t : ℝ) :
    1 / L ^ 3 - 3 * s * Real.sin t / L ^ 5 ≤ (RS L s t ^ 3)⁻¹ := by
  set a := RS L s t with ha
  have hapos : 0 < a := RS_pos hs h t
  have ha2 : a ^ 2 = L ^ 2 + 2 * s * Real.sin t := RS_sq hs h t
  have hlhs : 1 / L ^ 3 - 3 * s * Real.sin t / L ^ 5 = (5 * L ^ 2 - 3 * a ^ 2) / (2 * L ^ 5) := by
    rw [ha2]; field_simp; ring
  rw [hlhs, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hfac : 0 ≤ (a - L) ^ 2 * (3 * a ^ 3 + 6 * a ^ 2 * L + 4 * a * L ^ 2 + 2 * L ^ 3) := by
    positivity
  nlinarith [hfac]

/-- **`q ≥ q₀` on every surface** (`F/A > 0`). -/
theorem qS_ge_axis (hA : 0 < A) (hF : 0 < F) (hL : 0 < L) (hs : 0 ≤ s) (h : 2 * s < L ^ 2) :
    F / (Real.sqrt 2 * A * L) ≤ qS A L F s := by
  have hpi := pi_pos
  have hc := continuous_invCube hs h
  have hlow : ∫ τ in (-π)..π, (1 / L ^ 3 - 3 * s * Real.sin τ / L ^ 5) = 2 * π / L ^ 3 := by
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_sin]
    simp only [Real.cos_neg, sub_self, mul_zero, zero_div, sub_zero]
    ring
  have hmono : 2 * π / L ^ 3 ≤ ∫ τ in (-π)..π, (RS L s τ ^ 3)⁻¹ := by
    rw [← hlow]
    exact intervalIntegral.integral_mono_on (by linarith)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hc.intervalIntegrable _ _) fun τ _ => invCube_ge hL hs h τ
  have hrate : 0 < rateS A L F := by unfold rateS; positivity
  have h2 : 0 < Real.sqrt 2 := by positivity
  calc F / (Real.sqrt 2 * A * L) = rateS A L F * (2 * π / L ^ 3) / (2 * π) := by
        unfold rateS; field_simp
    _ ≤ qS A L F s := by
        unfold qS
        gcongr

end

/-! ## Reactor instance: `A = 7/4 T`, `L = 10 m`, `F = 50 T m` -/

/-- Reactor on-axis safety factor `q₀ ∈ [2.02, 2.021]`, now as the limit `s = 0` of the true
field-line safety factor. -/
theorem reactor_q_axis :
    2.02 ≤ qS (7 / 4) 10 50 0 ∧ qS (7 / 4) 10 50 0 ≤ 2.021 := by
  rw [qS_zero (by norm_num) (by norm_num)]
  have h := SolovevAlpha.reactor_q0_formula_bounds
  have e : (50 : ℝ) / (Real.sqrt 2 * (7 / 4) * 10) = 50 / 10 / (Real.sqrt 2 * (7 / 4)) := by
    field_simp
  rw [e]
  exact h

/-- **`q ≥ 2.02 > 1` on every flux surface of the reactor plasma** `ψ̃ = s² ≤ L⁴/16`
(`0 ≤ s ≤ 25`). -/
theorem reactor_q_ge {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 25) : 2.02 ≤ qS (7 / 4) 10 50 s := by
  have h1 := qS_ge_axis (A := 7 / 4) (F := 50) (L := 10) (by norm_num) (by norm_num)
    (by norm_num) hs (by nlinarith)
  have h2 := reactor_q_axis.1
  rw [qS_zero (by norm_num) (by norm_num)] at h2
  linarith

/-- The reactor flux surface `ψ̃ = s²` (`0 ≤ s ≤ 25`) is in the plasma region `ψ̃ ≤ L⁴/16`, and
the explicit field line on it stays there for all `t`. -/
theorem reactor_line_in_plasma {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 25) (t : ℝ) :
    psiT 10 (lineS (7 / 4) 10 50 s t) ≤ 10 ^ 4 / 16 := by
  rw [lineS_on_surface hs (by nlinarith)]
  nlinarith

/-- The reactor field lines are genuine (reparametrized) field lines of
`SolovevAlpha.reactorField`. -/
theorem reactor_lineS_fieldLine {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 25) (t : ℝ) :
    HasDerivAt (lineS (7 / 4) 10 50 s)
      (lamS (7 / 4) 10 s t • SolovevAlpha.reactorField (lineS (7 / 4) 10 50 s t)) t :=
  lineS_fieldLine (by norm_num) (by norm_num) hs (by nlinarith) t

/-! ## Mercier criteria -/

/-- Sign of the large-aspect-ratio (Shafranov–Yurchenko) Mercier expression with the true
safety factor inserted: for any labelling `c : ℝ → ℝ` (`ψ̃ = c(ρ)²`, `0 ≤ c ≤ 25`) and any
effective cylindrical data `Bθ, S, p'` with `S ≥ 0`, `p' ≤ 0`, `mercierTokamakQ ≥ 0`, because
`q ≥ 2.02 ≥ 1` (proved for the field). The data `Bθ, S, p', c` are arbitrary inputs and are
NOT tied to the Solov'ev field, so this is not a Mercier certificate for the equilibrium.
(Supplied asymptotic formula; indicative only at aspect
ratio ≈ 3.9 and elongation `√2`.) -/
theorem reactor_mercierTokamak {μ₀ : ℝ} {c p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hc0 : 0 ≤ c ρ) (hc1 : c ρ ≤ 25) (hS : 0 ≤ S ρ) (hp : p' ρ ≤ 0) :
    0 ≤ PlasmaLean.Stability.Mercier.mercierTokamakQ μ₀ (fun r => qS (7 / 4) 10 50 (c r))
      p' Bθ S Bθ' S' ρ := by
  apply PlasmaLean.Stability.Mercier.mercierTokamakQ_of_q_ge_one hμ hρ hS _ hp
  have := reactor_q_ge hc0 hc1
  nlinarith

/-- The reactor pressure decreases outward in the flux label: `dp/dψ̃ = -3 (A/L²)²/μ₀ < 0`. -/
theorem reactor_pressure_decreasing {μ₀ : ℝ} (hμ : 0 < μ₀) :
    -(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2 / μ₀) < 0 := by
  have : 0 < 3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2 / μ₀ := by positivity
  linarith

/-- Rounded oracle data for the general Mercier index on the reactor edge surface
`ψ̃ = 625` (NUMERICAL, `scripts/solovev_mercier_oracle.py`): `μ₀p'V'' ≈ 0.01105 > 0`
(well with outward-decreasing pressure), `∫|Ξ|²/|∇ψ|³ ≈ 0.00636`. `ι'` and the remaining
integrals are irrelevant for `mercierIndex_pos_of_well`. -/
@[expose] def oracleEdge : MercierSurfaceData where
  sG := 1
  sψ := 1
  iotaPrime := 0
  muPprime := -1
  Vpp := -1105 / 100000
  intBXi := 0
  intXi2 := 636 / 100000
  intB2 := 1

/-- Fixture: the rounded oracle edge data satisfy the dominant-well hypothesis, hence
`D_Merc > 0` for them. Certifies the reasoning step only, not the equilibrium. -/
theorem oracle_edge_stable : MercierStable oracleEdge := by
  apply mercierIndex_pos_of_well <;> norm_num [oracleEdge]

end PlasmaLean.Design.SolovevMercier
