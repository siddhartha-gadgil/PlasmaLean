/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.ValidatedQuadrature
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Validated quadrature for periodic integrands with a sharp peak

Generic real-analysis lemmas that reduce an integral over a period of a `2π`-periodic,
possibly sharply peaked (Lorentzian) integrand to integrals over `[-1, 1]` of algebraic
functions, which can then be enclosed with the cell sums of `ValidatedQuadrature`.

* **Periodicity.** `integral_period_eq` (any window of length `2π`),
  `integral_periodic_shift` (`∫_{-π}^{π} f(x + φ) = ∫_{-π}^{π} f`) and
  `integral_comp_two_mul_periodic` (`∫_{-π}^{π} g(2ζ) = ∫_{-π}^{π} g`).
* **Quarter arcs.** `integral_eq_quarter_arcs` splits the circle into the four arcs of
  length `π/2` centred at `0, π, π/2, -π/2`, each parametrised by `arctan` over `[-1, 1]`
  with weight `1/(1+t²)`. The closed forms of `sin`, `cos` on these arcs are
  `sin_arctan_add_pi`, `cos_arctan_add_pi`, `sin_pi_div_two_sub_arctan`, ... .
* **Half-circle rational parametrisation.** `integral_sin_cos_eq_rational`: for `f`
  continuous on the unit circle,
  `∫_{-π}^{π} f(sin t, cos t) dt = ∫_{-1}^{1} (f(y, x) + f(-y, -x)) · 2/(1+τ²) dτ`,
  `y = wy τ = 2τ/(1+τ²)`, `x = wx τ = (1-τ²)/(1+τ²)`.
* **Lorentzian kernel.** `integral_lorentzian`:
  `∫_a^b 1/(α + γ t²) = (arctan(b√(γ/α)) - arctan(a√(γ/α))) / √(αγ)`, and the
  product-integration bounds `integral_div_le_lorentz` / `lorentz_le_integral_div` for
  `∫ H/D` when `D` is squeezed between two Lorentzian denominators and `H` is bounded.
* **Cell sums with real bounds.** `sum_le_integral_le_sum_of_cell_integrals` and
  `cell_integral_bounds`.
* **Parametric integrals.** `continuous_parametric_integral`.

Sanity fixtures: `fixture_quarter_arcs_one`, `fixture_half_circle_one`,
`fixture_lorentzian_quarter`, `lorentzK_self` (degenerate interval) and `fixture_wx_values`.
-/

public section

namespace LeanTheory.Certificates.ValidatedQuadrature

open Real Set MeasureTheory intervalIntegral

/-! ## Periodicity -/

/-- The integral of a `2π`-periodic function over any window `[t, t + 2π]` equals its
integral over `[-π, π]`. -/
theorem integral_period_eq {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π)) (t : ℝ) :
    ∫ x in t..t + 2 * π, f x = ∫ x in (-π)..π, f x := by
  have h := hf.intervalIntegral_add_eq t (-π)
  rw [show -π + 2 * π = π by ring] at h
  exact h

/-- **Periodic shift.** For a `2π`-periodic `f` (no continuity needed),
`∫_{-π}^{π} f(x + φ) dx = ∫_{-π}^{π} f`. -/
theorem integral_periodic_shift {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π)) (φ : ℝ) :
    ∫ x in (-π)..π, f (x + φ) = ∫ x in (-π)..π, f x := by
  rw [intervalIntegral.integral_comp_add_right f φ, ← integral_period_eq hf (-π + φ)]
  rw [show -π + φ + 2 * π = π + φ by ring]

/-- **Double angle.** For a continuous `2π`-periodic `g`,
`∫_{-π}^{π} g(2ζ) dζ = ∫_{-π}^{π} g`. -/
theorem integral_comp_two_mul_periodic {g : ℝ → ℝ} (hg : Continuous g)
    (hp : Function.Periodic g (2 * π)) :
    ∫ ζ in (-π)..π, g (2 * ζ) = ∫ t in (-π)..π, g t := by
  rw [intervalIntegral.integral_comp_mul_left g two_ne_zero]
  rw [← integral_add_adjacent_intervals (hg.intervalIntegrable (2 * -π) 0)
    (hg.intervalIntegrable 0 (2 * π))]
  have h1 := integral_period_eq hp (2 * -π)
  have h2 := integral_period_eq hp 0
  rw [show 2 * -π + 2 * π = 0 by ring] at h1
  rw [zero_add] at h2
  rw [h1, h2, smul_eq_mul]
  ring

/-! ## Quarter arcs -/

/-- Substitution `x = arctan t`: `∫_{-1}^{1} G(arctan t)/(1+t²) = ∫_{-π/4}^{π/4} G`. -/
theorem integral_arctan_subst {G : ℝ → ℝ} (hG : Continuous G) :
    ∫ t in (-1 : ℝ)..1, G (arctan t) / (1 + t ^ 2) = ∫ x in (-(π / 4))..(π / 4), G x := by
  have hd : ∀ x ∈ uIcc (-1 : ℝ) 1, HasDerivAt arctan (1 / (1 + x ^ 2)) x :=
    fun x _ => hasDerivAt_arctan x
  have hc : ContinuousOn (fun x : ℝ => 1 / (1 + x ^ 2)) (uIcc (-1 : ℝ) 1) :=
    (Continuous.div continuous_const (by fun_prop) (fun x => by positivity)).continuousOn
  have h := intervalIntegral.integral_comp_mul_deriv hd hc hG
  rw [arctan_neg, arctan_one] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Function.comp]
  ring

/-- A continuous function divided by `1 + t²` is interval integrable. -/
theorem intervalIntegrable_div_one_add_sq {K : ℝ → ℝ} (hK : Continuous K) (a b : ℝ) :
    IntervalIntegrable (fun t => K t / (1 + t ^ 2)) volume a b :=
  (hK.div (by fun_prop) (fun x => by positivity)).intervalIntegrable a b

/-- **Quarter-arc decomposition.** For a continuous `2π`-periodic `G`, the integral over a
period is the sum of four arc integrals: `|x| ≤ π/4` (`x = arctan t`), `|x - π| ≤ π/4`
(`x = arctan t + π`), `|x ∓ π/2| ≤ π/4` (`x = ±π/2 - arctan u`). -/
theorem integral_eq_quarter_arcs {G : ℝ → ℝ} (hG : Continuous G)
    (hp : Function.Periodic G (2 * π)) :
    ∫ x in (-π)..π, G x =
      (∫ t in (-1 : ℝ)..1, (G (arctan t) + G (arctan t + π)) / (1 + t ^ 2)) +
      ∫ u in (-1 : ℝ)..1, (G (π / 2 - arctan u) + G (-(π / 2) - arctan u)) / (1 + u ^ 2) := by
  have hgi : ∀ a b : ℝ, IntervalIntegrable G volume a b := fun a b => hG.intervalIntegrable a b
  have i1 : IntervalIntegrable (fun t => G (arctan t) / (1 + t ^ 2)) volume (-1) 1 :=
    intervalIntegrable_div_one_add_sq (K := fun t => G (arctan t)) (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun t => G (arctan t + π) / (1 + t ^ 2)) volume (-1) 1 :=
    intervalIntegrable_div_one_add_sq (K := fun t => G (arctan t + π)) (by fun_prop) _ _
  have i3 : IntervalIntegrable (fun t => G (π / 2 - arctan t) / (1 + t ^ 2)) volume (-1) 1 :=
    intervalIntegrable_div_one_add_sq (K := fun t => G (π / 2 - arctan t)) (by fun_prop) _ _
  have i4 : IntervalIntegrable (fun t => G (-(π / 2) - arctan t) / (1 + t ^ 2)) volume
      (-1) 1 :=
    intervalIntegrable_div_one_add_sq (K := fun t => G (-(π / 2) - arctan t)) (by fun_prop) _ _
  have hs1 : ∫ t in (-1 : ℝ)..1, (G (arctan t) + G (arctan t + π)) / (1 + t ^ 2) =
      (∫ t in (-1 : ℝ)..1, G (arctan t) / (1 + t ^ 2)) +
        ∫ t in (-1 : ℝ)..1, G (arctan t + π) / (1 + t ^ 2) := by
    rw [← intervalIntegral.integral_add i1 i2]
    congr 1; funext t; ring
  have hs2 : ∫ u in (-1 : ℝ)..1, (G (π / 2 - arctan u) + G (-(π / 2) - arctan u)) /
      (1 + u ^ 2) =
      (∫ t in (-1 : ℝ)..1, G (π / 2 - arctan t) / (1 + t ^ 2)) +
        ∫ t in (-1 : ℝ)..1, G (-(π / 2) - arctan t) / (1 + t ^ 2) := by
    rw [← intervalIntegral.integral_add i3 i4]
    congr 1; funext t; ring
  have hA := integral_arctan_subst hG
  have hC : ∫ t in (-1 : ℝ)..1, G (arctan t + π) / (1 + t ^ 2) =
      ∫ x in (3 * π / 4)..(5 * π / 4), G x := by
    have h : ∫ t in (-1 : ℝ)..1, G (arctan t + π) / (1 + t ^ 2) =
        ∫ x in (-(π / 4))..(π / 4), G (x + π) :=
      integral_arctan_subst (G := fun x => G (x + π)) (by fun_prop)
    rw [h, intervalIntegral.integral_comp_add_right G π,
      show -(π / 4) + π = 3 * π / 4 by ring, show π / 4 + π = 5 * π / 4 by ring]
  have hB : ∫ t in (-1 : ℝ)..1, G (π / 2 - arctan t) / (1 + t ^ 2) =
      ∫ x in (π / 4)..(3 * π / 4), G x := by
    have h : ∫ t in (-1 : ℝ)..1, G (π / 2 - arctan t) / (1 + t ^ 2) =
        ∫ x in (-(π / 4))..(π / 4), G (π / 2 - x) :=
      integral_arctan_subst (G := fun x => G (π / 2 - x)) (by fun_prop)
    rw [h, intervalIntegral.integral_comp_sub_left G (π / 2),
      show π / 2 - π / 4 = π / 4 by ring, show π / 2 - -(π / 4) = 3 * π / 4 by ring]
  have hD : ∫ t in (-1 : ℝ)..1, G (-(π / 2) - arctan t) / (1 + t ^ 2) =
      ∫ x in (5 * π / 4)..(7 * π / 4), G x := by
    have h : ∫ t in (-1 : ℝ)..1, G (-(π / 2) - arctan t) / (1 + t ^ 2) =
        ∫ x in (-(π / 4))..(π / 4), G (-(π / 2) - x) :=
      integral_arctan_subst (G := fun x => G (-(π / 2) - x)) (by fun_prop)
    have hp' : ∀ x, G (x + 2 * π) = G x := hp
    have h2 := intervalIntegral.integral_comp_add_right G (2 * π) (a := -(3 * π / 4))
      (b := -(π / 4))
    simp only [hp'] at h2
    rw [h, intervalIntegral.integral_comp_sub_left G (-(π / 2)),
      show -(π / 2) - π / 4 = -(3 * π / 4) by ring,
      show -(π / 2) - -(π / 4) = -(π / 4) by ring, h2,
      show -(3 * π / 4) + 2 * π = 5 * π / 4 by ring,
      show -(π / 4) + 2 * π = 7 * π / 4 by ring]
  have htot : ∫ x in (-π)..π, G x = (∫ x in (-(π / 4))..(π / 4), G x) +
      (∫ x in (π / 4)..(3 * π / 4), G x) + (∫ x in (3 * π / 4)..(5 * π / 4), G x) +
      ∫ x in (5 * π / 4)..(7 * π / 4), G x := by
    rw [← integral_period_eq hp (-(π / 4)), show -(π / 4) + 2 * π = 7 * π / 4 by ring,
      integral_add_adjacent_intervals (hgi _ _) (hgi _ _),
      integral_add_adjacent_intervals (hgi _ _) (hgi _ _),
      integral_add_adjacent_intervals (hgi _ _) (hgi _ _)]
  rw [htot, hs1, hs2, hA, hB, hC, hD]
  ring

/-- `sin (arctan t + π) = -t/√(1+t²)`. -/
theorem sin_arctan_add_pi (t : ℝ) : Real.sin (arctan t + π) = -(t / √(1 + t ^ 2)) := by
  rw [sin_add_pi, sin_arctan]

/-- `cos (arctan t + π) = -1/√(1+t²)`. -/
theorem cos_arctan_add_pi (t : ℝ) : Real.cos (arctan t + π) = -(1 / √(1 + t ^ 2)) := by
  rw [cos_add_pi, cos_arctan]

/-- `sin (π/2 - arctan u) = 1/√(1+u²)`. -/
theorem sin_pi_div_two_sub_arctan (u : ℝ) : Real.sin (π / 2 - arctan u) = 1 / √(1 + u ^ 2) := by
  rw [sin_pi_div_two_sub, cos_arctan]

/-- `cos (π/2 - arctan u) = u/√(1+u²)`. -/
theorem cos_pi_div_two_sub_arctan (u : ℝ) : Real.cos (π / 2 - arctan u) = u / √(1 + u ^ 2) := by
  rw [cos_pi_div_two_sub, sin_arctan]

/-- `sin (-(π/2) - arctan u) = -1/√(1+u²)`. -/
theorem sin_neg_pi_div_two_sub_arctan (u : ℝ) :
    Real.sin (-(π / 2) - arctan u) = -(1 / √(1 + u ^ 2)) := by
  rw [sin_sub, sin_neg, cos_neg, sin_pi_div_two, cos_pi_div_two, cos_arctan]
  ring

/-- `cos (-(π/2) - arctan u) = -u/√(1+u²)`. -/
theorem cos_neg_pi_div_two_sub_arctan (u : ℝ) :
    Real.cos (-(π / 2) - arctan u) = -(u / √(1 + u ^ 2)) := by
  rw [cos_sub, cos_neg, sin_neg, cos_pi_div_two, sin_pi_div_two, sin_arctan]
  ring

/-! ## Half-circle rational parametrisation of `∫ f(sin t, cos t) dt` -/

/-- The rational parametrisation `x(τ) = (1-τ²)/(1+τ²) = cos(2 arctan τ)`. -/
@[expose] noncomputable def wx (τ : ℝ) : ℝ := (1 - τ ^ 2) / (1 + τ ^ 2)

/-- `cos (2 arctan τ) = (1-τ²)/(1+τ²)`. -/
theorem cos_two_arctan (τ : ℝ) : Real.cos (2 * arctan τ) = wx τ := by
  rw [cos_two_mul, cos_arctan, wx, div_pow, Real.sq_sqrt (by positivity)]
  have h : 0 < 1 + τ ^ 2 := by positivity
  field_simp
  ring

/-- `x` is even. -/
theorem wx_neg (τ : ℝ) : wx (-τ) = wx τ := by unfold wx; ring

/-- `x` is continuous. -/
theorem continuous_wx : Continuous wx := by
  unfold wx
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)

/-- `(y, x)` lies on the unit circle. -/
theorem wy_sq_add_wx_sq (τ : ℝ) : wy τ ^ 2 + wx τ ^ 2 = 1 := by
  unfold wy wx
  have h : 0 < 1 + τ ^ 2 := by positivity
  field_simp
  ring

/-- `x` is nonnegative on `[-1, 1]` and at most `1` everywhere. -/
theorem wx_mem {τ : ℝ} (h1 : -1 ≤ τ) (h2 : τ ≤ 1) : wx τ ∈ Icc (0 : ℝ) 1 := by
  unfold wx
  have h : 0 < 1 + τ ^ 2 := by positivity
  constructor
  · apply div_nonneg _ h.le
    nlinarith
  · rw [div_le_iff₀ h]; nlinarith [sq_nonneg τ]

/-- `x` is decreasing on `[0, ∞)`. -/
theorem wx_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : wx b ≤ wx a := by
  unfold wx
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hab hab ha (ha.trans hab)]

/-- `x` is increasing on `(-∞, 0]`. -/
theorem wx_mono_neg {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) : wx a ≤ wx b := by
  rw [← wx_neg a, ← wx_neg b]
  exact wx_anti (by linarith) (by linarith)

/-- `y` is increasing on `[-1, 1]`. -/
theorem wy_mono' {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : wy a ≤ wy b := by
  unfold wy
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ (b - a) * (1 - a * b) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith

/-- Substitution `x = 2 arctan τ`:
`∫_{-π/2}^{π/2} k = ∫_{-1}^{1} k(2 arctan τ) · 2/(1+τ²) dτ`. -/
theorem integral_two_arctan_subst {k : ℝ → ℝ} (hk : Continuous k) :
    ∫ x in (-(π / 2))..(π / 2), k x =
      ∫ τ in (-1 : ℝ)..1, k (2 * arctan τ) * (2 / (1 + τ ^ 2)) := by
  have hd : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun τ => 2 * arctan τ) (2 * (1 / (1 + x ^ 2))) x :=
    fun x _ => (hasDerivAt_arctan x).const_mul 2
  have hc : ContinuousOn (fun x : ℝ => 2 * (1 / (1 + x ^ 2))) (uIcc (-1 : ℝ) 1) :=
    (Continuous.mul continuous_const
      (Continuous.div continuous_const (by fun_prop) (fun x => by positivity))).continuousOn
  have h := intervalIntegral.integral_comp_mul_deriv hd hc hk
  have e1 : 2 * arctan (-1) = -(π / 2) := by rw [arctan_neg, arctan_one]; ring
  have e2 : 2 * arctan 1 = π / 2 := by rw [arctan_one]; ring
  rw [e1, e2] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Function.comp]
  ring

/-- **Half-circle rational parametrisation.** For `f` with `uncurry f` continuous on the unit
circle, `∫_{-π}^{π} f(sin t, cos t) dt = ∫_{-1}^{1} (f(y, x) + f(-y, -x)) · 2/(1+τ²) dτ`
with `y = wy τ`, `x = wx τ`. -/
theorem integral_sin_cos_eq_rational {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1}) :
    ∫ t in (-π)..π, f (Real.sin t) (Real.cos t) =
      ∫ τ in (-1 : ℝ)..1, (f (wy τ) (wx τ) + f (-wy τ) (-wx τ)) * (2 / (1 + τ ^ 2)) := by
  set g : ℝ → ℝ := fun t => f (Real.sin t) (Real.cos t) with hgdef
  have hg : Continuous g :=
    hf.comp_continuous (Real.continuous_sin.prodMk Real.continuous_cos)
      (fun t => by change Real.sin t ^ 2 + Real.cos t ^ 2 = 1; exact sin_sq_add_cos_sq t)
  have hp : Function.Periodic g (2 * π) := fun t => by
    simp only [hgdef, sin_add_two_pi, cos_add_two_pi]
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  have hgπ : Continuous (fun x => g (x + π)) := by fun_prop
  have htot : ∫ t in (-π)..π, g t =
      (∫ x in (-(π / 2))..(π / 2), g x) + ∫ x in (-(π / 2))..(π / 2), g (x + π) := by
    rw [← integral_period_eq hp (-(π / 2)), intervalIntegral.integral_comp_add_right g π,
      show -(π / 2) + π = π / 2 by ring,
      integral_add_adjacent_intervals (hgi _ _) (hgi _ _)]
    congr 1
    ring
  have i1 : IntervalIntegrable (fun τ => g (2 * arctan τ) * (2 / (1 + τ ^ 2))) volume
      (-1) 1 :=
    ((hg.comp (by fun_prop)).mul
      (continuous_const.div (by fun_prop) (fun x => by positivity))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun τ => g (2 * arctan τ + π) * (2 / (1 + τ ^ 2))) volume
      (-1) 1 :=
    ((hgπ.comp (by fun_prop)).mul
      (continuous_const.div (by fun_prop) (fun x => by positivity))).intervalIntegrable _ _
  have h2 : ∫ x in (-(π / 2))..(π / 2), g (x + π) =
      ∫ τ in (-1 : ℝ)..1, g (2 * arctan τ + π) * (2 / (1 + τ ^ 2)) :=
    integral_two_arctan_subst (k := fun x => g (x + π)) hgπ
  rw [htot, integral_two_arctan_subst hg, h2, ← intervalIntegral.integral_add i1 i2]
  congr 1
  funext τ
  simp only [hgdef, sin_add_pi, cos_add_pi, sin_two_arctan, cos_two_arctan]
  ring

/-! ## Lorentzian kernel -/

/-- `α + γ t² > 0` for `α > 0`, `γ ≥ 0`. -/
theorem lorentz_den_pos {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) (t : ℝ) : 0 < α + γ * t ^ 2 := by
  have := mul_nonneg hγ (sq_nonneg t)
  linarith

/-- **Lorentzian integral.** For `α, γ > 0`,
`∫_a^b 1/(α + γ t²) = (arctan(b√(γ/α)) - arctan(a√(γ/α))) / √(αγ)`. -/
theorem integral_lorentzian {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (a b : ℝ) :
    ∫ t in a..b, 1 / (α + γ * t ^ 2) =
      (arctan (b * √(γ / α)) - arctan (a * √(γ / α))) / √(α * γ) := by
  set s := √(γ / α) with hs
  have hs2 : s ^ 2 = γ / α := Real.sq_sqrt (div_pos hγ hα).le
  have hr0 : 0 < √(α * γ) := Real.sqrt_pos.2 (mul_pos hα hγ)
  have hr2 : √(α * γ) ^ 2 = α * γ := Real.sq_sqrt (mul_pos hα hγ).le
  have hsr : s * √(α * γ) = γ := by
    rw [hs, ← Real.sqrt_mul (div_pos hγ hα).le,
      show γ / α * (α * γ) = γ ^ 2 by field_simp, Real.sqrt_sq hγ.le]
  have hs' : s = γ / √(α * γ) := (eq_div_iff hr0.ne').2 hsr
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun t => arctan (t * s) / √(α * γ))
      (1 / (α + γ * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => t * s) s x := by simpa using (hasDerivAt_id x).mul_const s
    have h2 := (h1.arctan).div_const (√(α * γ))
    convert h2 using 1
    rw [mul_pow, hs2, hs']
    have hd := lorentz_den_pos hα hγ.le x
    field_simp
    rw [hr2]
  have hint : IntervalIntegrable (fun t => 1 / (α + γ * t ^ 2)) volume a b :=
    (continuous_const.div (by fun_prop)
      (fun t => (lorentz_den_pos hα hγ.le t).ne')).intervalIntegrable a b
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The Lorentzian kernel integral `K(α, γ) = ∫_a^b 1/(α + γ t²)`. -/
@[expose] noncomputable def lorentzK (a b α γ : ℝ) : ℝ := ∫ t in a..b, 1 / (α + γ * t ^ 2)

/-- Degenerate case: the kernel over an empty interval vanishes. -/
theorem lorentzK_self (a α γ : ℝ) : lorentzK a a α γ = 0 := by
  simp [lorentzK]

/-- Generic upper product-integration step: a pointwise bound
`H/D ≤ c / (α + γ t²)` on `[a, b]` integrates to `∫ H/D ≤ c K(α, γ)`. -/
theorem integral_div_le_const_mul_lorentzK {H D : ℝ → ℝ} {a b α γ c : ℝ} (hab : a ≤ b)
    (hH : ContinuousOn H (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hDpos : ∀ t ∈ Icc a b, 0 < D t) (hpos : ∀ t ∈ Icc a b, 0 < α + γ * t ^ 2)
    (hpt : ∀ t ∈ Icc a b, H t / D t ≤ c * (1 / (α + γ * t ^ 2))) :
    ∫ t in a..b, H t / D t ≤ c * lorentzK a b α γ := by
  have hi1 : IntervalIntegrable (fun t => H t / D t) volume a b :=
    (hH.div hD (fun t ht => (hDpos t ht).ne')).intervalIntegrable_of_Icc hab
  have hK : ContinuousOn (fun t => 1 / (α + γ * t ^ 2)) (Icc a b) :=
    continuousOn_const.div (Continuous.continuousOn (by fun_prop))
      (fun t ht => (hpos t ht).ne')
  have hi2 : IntervalIntegrable (fun t => c * (1 / (α + γ * t ^ 2))) volume a b :=
    (continuousOn_const.mul hK).intervalIntegrable_of_Icc hab
  unfold lorentzK
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hab hi1 hi2 hpt

/-- Generic lower product-integration step: a pointwise bound
`c / (α + γ t²) ≤ H/D` on `[a, b]` integrates to `c K(α, γ) ≤ ∫ H/D`. -/
theorem const_mul_lorentzK_le_integral_div {H D : ℝ → ℝ} {a b α γ c : ℝ} (hab : a ≤ b)
    (hH : ContinuousOn H (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hDpos : ∀ t ∈ Icc a b, 0 < D t) (hpos : ∀ t ∈ Icc a b, 0 < α + γ * t ^ 2)
    (hpt : ∀ t ∈ Icc a b, c * (1 / (α + γ * t ^ 2)) ≤ H t / D t) :
    c * lorentzK a b α γ ≤ ∫ t in a..b, H t / D t := by
  have hi1 : IntervalIntegrable (fun t => H t / D t) volume a b :=
    (hH.div hD (fun t ht => (hDpos t ht).ne')).intervalIntegrable_of_Icc hab
  have hK : ContinuousOn (fun t => 1 / (α + γ * t ^ 2)) (Icc a b) :=
    continuousOn_const.div (Continuous.continuousOn (by fun_prop))
      (fun t ht => (hpos t ht).ne')
  have hi2 : IntervalIntegrable (fun t => c * (1 / (α + γ * t ^ 2))) volume a b :=
    (continuousOn_const.mul hK).intervalIntegrable_of_Icc hab
  unfold lorentzK
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hab hi2 hi1 hpt

/-- **Product-integration upper bound.** If `αl + γl t² ≤ D t ≤ αh + γh t²` and
`H t ≤ Hh` on `[a, b]` (with `αl, γl > 0`), then
`∫_a^b H/D ≤ Hh K(αl, γl)` if `Hh ≥ 0`, and `≤ Hh K(αh, γh)` otherwise. -/
theorem integral_div_le_lorentz {H D : ℝ → ℝ} {a b αl γl αh γh Hh : ℝ} (hab : a ≤ b)
    (hH : ContinuousOn H (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hαl : 0 < αl) (hγl : 0 < γl)
    (hDl : ∀ t ∈ Icc a b, αl + γl * t ^ 2 ≤ D t) (hDh : ∀ t ∈ Icc a b, D t ≤ αh + γh * t ^ 2)
    (hHh : ∀ t ∈ Icc a b, H t ≤ Hh) :
    ∫ t in a..b, H t / D t ≤
      (if 0 ≤ Hh then Hh * lorentzK a b αl γl else Hh * lorentzK a b αh γh) := by
  have hPl : ∀ t ∈ Icc a b, 0 < αl + γl * t ^ 2 := fun t _ => lorentz_den_pos hαl hγl.le t
  have hDpos : ∀ t ∈ Icc a b, 0 < D t := fun t ht => (hPl t ht).trans_le (hDl t ht)
  have hPh : ∀ t ∈ Icc a b, 0 < αh + γh * t ^ 2 := fun t ht =>
    (hDpos t ht).trans_le (hDh t ht)
  split_ifs with h0
  · refine integral_div_le_const_mul_lorentzK hab hH hD hDpos hPl (fun t ht => ?_)
    have hP := hPl t ht
    have hDp := hDpos t ht
    rw [mul_one_div, div_le_div_iff₀ hDp hP]
    have e1 := mul_le_mul_of_nonneg_right (hHh t ht) hP.le
    have e2 := mul_le_mul_of_nonneg_left (hDl t ht) h0
    linarith
  · refine integral_div_le_const_mul_lorentzK hab hH hD hDpos hPh (fun t ht => ?_)
    have hP := hPh t ht
    have hDp := hDpos t ht
    rw [mul_one_div, div_le_div_iff₀ hDp hP]
    have e1 := mul_le_mul_of_nonneg_right (hHh t ht) hP.le
    have e2 := mul_le_mul_of_nonpos_left (hDh t ht) (le_of_lt (not_le.mp h0))
    linarith

/-- **Product-integration lower bound.** If `αl + γl t² ≤ D t ≤ αh + γh t²` and
`Hl ≤ H t` on `[a, b]` (with `αl, γl > 0`), then `Hl K(αh, γh) ≤ ∫_a^b H/D` if `Hl ≥ 0`,
and `Hl K(αl, γl) ≤ ∫_a^b H/D` otherwise. -/
theorem lorentz_le_integral_div {H D : ℝ → ℝ} {a b αl γl αh γh Hl : ℝ} (hab : a ≤ b)
    (hH : ContinuousOn H (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hαl : 0 < αl) (hγl : 0 < γl)
    (hDl : ∀ t ∈ Icc a b, αl + γl * t ^ 2 ≤ D t) (hDh : ∀ t ∈ Icc a b, D t ≤ αh + γh * t ^ 2)
    (hHl : ∀ t ∈ Icc a b, Hl ≤ H t) :
    (if 0 ≤ Hl then Hl * lorentzK a b αh γh else Hl * lorentzK a b αl γl) ≤
      ∫ t in a..b, H t / D t := by
  have hPl : ∀ t ∈ Icc a b, 0 < αl + γl * t ^ 2 := fun t _ => lorentz_den_pos hαl hγl.le t
  have hDpos : ∀ t ∈ Icc a b, 0 < D t := fun t ht => (hPl t ht).trans_le (hDl t ht)
  have hPh : ∀ t ∈ Icc a b, 0 < αh + γh * t ^ 2 := fun t ht =>
    (hDpos t ht).trans_le (hDh t ht)
  split_ifs with h0
  · refine const_mul_lorentzK_le_integral_div hab hH hD hDpos hPh (fun t ht => ?_)
    have hP := hPh t ht
    have hDp := hDpos t ht
    rw [mul_one_div, div_le_div_iff₀ hP hDp]
    have e1 := mul_le_mul_of_nonneg_right (hHl t ht) hP.le
    have e2 := mul_le_mul_of_nonneg_left (hDh t ht) h0
    linarith
  · refine const_mul_lorentzK_le_integral_div hab hH hD hDpos hPl (fun t ht => ?_)
    have hP := hPl t ht
    have hDp := hDpos t ht
    rw [mul_one_div, div_le_div_iff₀ hP hDp]
    have e1 := mul_le_mul_of_nonneg_right (hHl t ht) hP.le
    have e2 := mul_le_mul_of_nonpos_left (hDl t ht) (le_of_lt (not_le.mp h0))
    linarith

/-- **Pointwise kernel bounds.** If `αl + γl t² ≤ D t ≤ αh + γh t²` on `[a, b]` with
`αl, γl > 0`, then `K(αh, γh) ≤ ∫_a^b 1/D ≤ K(αl, γl)`. -/
theorem lorentzK_le_integral_inv_le {D : ℝ → ℝ} {a b αl γl αh γh : ℝ} (hab : a ≤ b)
    (hD : ContinuousOn D (Icc a b)) (hαl : 0 < αl) (hγl : 0 < γl)
    (hDl : ∀ t ∈ Icc a b, αl + γl * t ^ 2 ≤ D t) (hDh : ∀ t ∈ Icc a b, D t ≤ αh + γh * t ^ 2) :
    lorentzK a b αh γh ≤ ∫ t in a..b, 1 / D t ∧ ∫ t in a..b, 1 / D t ≤ lorentzK a b αl γl := by
  have hu := integral_div_le_lorentz (H := fun _ => 1) (Hh := 1) hab
    continuousOn_const hD hαl hγl hDl hDh (fun _ _ => le_rfl)
  have hl := lorentz_le_integral_div (H := fun _ => 1) (Hl := 1) hab
    continuousOn_const hD hαl hγl hDl hDh (fun _ _ => le_rfl)
  simp only [zero_le_one, ite_true, one_mul] at hu hl
  exact ⟨hl, hu⟩

/-! ## Cell sums with real bounds -/

/-- **Cell sums with real cell bounds.** If each cell integral over
`[a + i h, a + (i+1) h]` (`i < N`) lies in `[L i, U i]`, then
`Σ L i ≤ ∫_a^{a+Nh} g ≤ Σ U i`. -/
theorem sum_le_integral_le_sum_of_cell_integrals {g : ℝ → ℝ} {a h : ℝ} (hh : 0 ≤ h)
    (L U : ℕ → ℝ) : ∀ N : ℕ, IntervalIntegrable g volume a (a + N * h) →
      (∀ i < N, L i ≤ ∫ x in (a + i * h)..(a + (i + 1) * h), g x ∧
        ∫ x in (a + i * h)..(a + (i + 1) * h), g x ≤ U i) →
      ∑ i ∈ Finset.range N, L i ≤ ∫ x in a..(a + N * h), g x ∧
        ∫ x in a..(a + N * h), g x ≤ ∑ i ∈ Finset.range N, U i
  | 0, _, _ => by simp
  | N + 1, hint, hc => by
    have hle1 : a ≤ a + N * h := by
      have : (0 : ℝ) ≤ N * h := by positivity
      linarith
    have hle2 : a + N * h ≤ a + ((N + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have hsub1 : IntervalIntegrable g volume a (a + N * h) :=
      hint.mono_set (by
        rw [uIcc_of_le hle1, uIcc_of_le (hle1.trans hle2)]
        exact Icc_subset_Icc le_rfl hle2)
    have hsub2 : IntervalIntegrable g volume (a + N * h) (a + ((N + 1 : ℕ) : ℝ) * h) :=
      hint.mono_set (by
        rw [uIcc_of_le hle2, uIcc_of_le (hle1.trans hle2)]
        exact Icc_subset_Icc hle1 le_rfl)
    have ih := sum_le_integral_le_sum_of_cell_integrals hh L U N hsub1
      (fun i hi => hc i (by omega))
    have hN := hc N (by omega)
    rw [← integral_add_adjacent_intervals hsub1 hsub2, Finset.sum_range_succ,
      Finset.sum_range_succ]
    push_cast
    constructor <;> linarith [ih.1, ih.2, hN.1, hN.2]

/-- **Pointwise cell bounds.** If `lo ≤ g ≤ hi` on the cell `[a + i h, a + (i+1) h]`, the
cell integral lies in `[h lo, h hi]`. -/
theorem cell_integral_bounds {g : ℝ → ℝ} {a h lo hi : ℝ} (hh : 0 ≤ h) (i : ℕ)
    (hg : IntervalIntegrable g volume (a + i * h) (a + (i + 1) * h))
    (hb : ∀ x ∈ Icc (a + i * h) (a + (i + 1) * h), lo ≤ g x ∧ g x ≤ hi) :
    h * lo ≤ ∫ x in (a + i * h)..(a + (i + 1) * h), g x ∧
      ∫ x in (a + i * h)..(a + (i + 1) * h), g x ≤ h * hi := by
  have hle : a + i * h ≤ a + (i + 1) * h := by nlinarith
  have e : a + (i + 1) * h - (a + i * h) = h := by ring
  have h1 := intervalIntegral.integral_mono_on hle intervalIntegrable_const hg
    (fun x hx => (hb x hx).1)
  have h2 := intervalIntegral.integral_mono_on hle hg intervalIntegrable_const
    (fun x hx => (hb x hx).2)
  rw [intervalIntegral.integral_const, smul_eq_mul, e] at h1 h2
  exact ⟨h1, h2⟩

/-! ## Parametric integrals -/

/-- **Continuity of a parametric integral.** If `(χ, ζ) ↦ F χ ζ` is jointly continuous, then
`ζ ↦ ∫_a^b F χ ζ dχ` is continuous. -/
theorem continuous_parametric_integral {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (a b : ℝ) : Continuous (fun ζ => ∫ χ in a..b, F χ ζ) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ζ χ => F χ ζ) (hF.comp continuous_swap) a b

/-- A parametric integral of a jointly continuous function is interval integrable in the
parameter. -/
theorem intervalIntegrable_parametric_integral {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (a b c d : ℝ) :
    IntervalIntegrable (fun ζ => ∫ χ in a..b, F χ ζ) volume c d :=
  (continuous_parametric_integral hF a b).intervalIntegrable c d

/-! ## Sanity fixtures -/

/-- Quarter-arc fixture: with `G = 1`, `integral_eq_quarter_arcs` gives
`∫_{-1}^{1} 1/(1+t²) = π/2`. -/
theorem fixture_quarter_arcs_one : ∫ t in (-1 : ℝ)..1, 1 / (1 + t ^ 2) = π / 2 := by
  have h := integral_eq_quarter_arcs (G := fun _ => (1 : ℝ)) continuous_const (fun _ => rfl)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_neg_eq_add] at h
  have e : ∀ τ : ℝ, (1 + 1) / (1 + τ ^ 2) = 2 * (1 / (1 + τ ^ 2)) := fun τ => by ring
  simp only [e, intervalIntegral.integral_const_mul] at h
  linarith

/-- Half-circle fixture: with `f = 1`, `integral_sin_cos_eq_rational` gives
`∫_{-1}^{1} 1/(1+τ²) = π/2`. -/
theorem fixture_half_circle_one : ∫ τ in (-1 : ℝ)..1, 1 / (1 + τ ^ 2) = π / 2 := by
  have h := integral_sin_cos_eq_rational (f := fun _ _ => (1 : ℝ)) continuousOn_const
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_neg_eq_add] at h
  have e : ∀ τ : ℝ, (1 + 1) * (2 / (1 + τ ^ 2)) = 4 * (1 / (1 + τ ^ 2)) := fun τ => by ring
  simp only [e, intervalIntegral.integral_const_mul] at h
  linarith

/-- Lorentzian fixture: `α = γ = 1`, `[0, 1]` gives `∫₀¹ 1/(1+t²) = π/4`. -/
theorem fixture_lorentzian_quarter : ∫ t in (0 : ℝ)..1, 1 / (1 + 1 * t ^ 2) = π / 4 := by
  rw [integral_lorentzian one_pos one_pos 0 1]
  simp [arctan_one]

/-- Values of the cosine parametrisation: `x(0) = 1`, `x(1) = 0`, `x(-1) = 0`. -/
theorem fixture_wx_values : wx 0 = 1 ∧ wx 1 = 0 ∧ wx (-1) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [wx]

end LeanTheory.Certificates.ValidatedQuadrature
