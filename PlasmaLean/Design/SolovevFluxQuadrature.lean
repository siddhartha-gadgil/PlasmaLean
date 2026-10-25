/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevMercierQuadrature
public import PlasmaLean.Certificates.PolyInterval
public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Certificates.BoolCert

/-!
# Certified enclosures of the Solov'ev flux-surface averages (polynomial quadrature)

For the reactor Solov'ev surfaces (normalized radius `ε = σ/50`, `v = 1 + ε sin t = R²/L²`)
the flux-surface geometry of `PlasmaLean.Design.SolovevFluxGeometry` reduces exactly to the
three one-dimensional integrals

* `Pn ε = ∫_{-π}^{π} v^{-1/2} dt` (`SolovevMercierQuadrature.Pn`),
* `IGn ε = ∫_{-π}^{π} G(ε, sin t) v^{-3/2} dt`, `G = (2y + ε(1+y²))² + 2(1-y²)(1+εy)²`
  (`SolovevMercierQuadrature.Gn`; `|∇ψ̃|² = 10⁴ σ² G/R²`),
* `IHn ε = ∫_{-π}^{π} H(ε, sin t) v^{-3/2} dt`, `H = 3 + 8εy + ε² + 4ε²y²`
  (`Δψ̃ / R = 10 H v^{-3/2}`).

This module proves, for EVERY real `ε ∈ [0, 12/25]` (the transport domain is
`ε ≤ √(11/48) < 0.4788`),

  `flux_ratio_bounds : 539 Pn ≤ 192 IGn ∧ 128 IGn ≤ 385 Pn ∧ 539 Pn ≤ 192 IHn ∧ 128 IHn ≤ 385 Pn`,

i.e. `IGn/Pn, IHn/Pn ∈ [539/192, 385/128]`, which are exactly the enclosures
`0.49 ≤ (48/275)·(·) ≤ 0.525` required by `SolovevBand.IsSolovevGeometry`.

## Method (no interval quadrature cells; everything is exact rational arithmetic)

The required accuracy is about `0.1 %` (the true ratio at the axis is `3`, the bound
`385/128 ≈ 3.0078`). Riemann-type cell enclosures would need thousands of cells, so a
different, fully rigorous route is used:

1. **Pointwise polynomial enclosures** of `v^{-3/2}`: rational polynomials `L₃ ≤ (1+x)^{-3/2}
   ≤ U₃` on `|x| ≤ 12/25` (`fQ_bounds`), where `L₃`, `U₃` are the degree-11 Taylor polynomial
   (shifted by `10⁻⁷`, `U₃` with an extra `x¹²` term). They are certified through the
   polynomial inequalities `U₃ ≥ 0`, `L₃ ≥ 0`, `U₃²(1+x)³ ≥ 1`, `L₃²(1+x)³ ≤ 1`, each checked by
   the exact piecewise Horner checker `QPoly.checkOn` (48 pieces, one `kernel_fact` each).
2. **Bivariate polynomials** `BPoly` (`Σ c ε^a y^b`, exact product `BPoly.mul`): the
   integrands are squeezed between `G · L₃(εy)` and `G · U₃(εy)` (`G, H ≥ 0`; for `Pn` use
   `v^{-1/2} = v · v^{-3/2}`).
3. **Exact integration** (`integral_bpoly`): `∫_{-π}^{π} sin^b t dt = π · wallis b`
   (`integral_sin_pow_wallis`, Mathlib's reduction formula), so the integral of a bivariate
   polynomial is `π` times an explicit univariate polynomial in `ε` (`toEps`).
4. **Final checks**: the four inequalities become polynomial inequalities in `ε` on
   `[0, 12/25]`, checked by `QPoly.checkOn` (4 pieces each).

The data are not tuned numerically beyond a small exact-rational search (outside Lean): the
Taylor coefficients are the binomial coefficients `binom(-3/2, n)`, the shift is `10⁻⁷`, the
extra coefficient is `2 |binom(-3/2, 12)|`, and the pieces are uniform; they only have to pass
the kernel checks.

Sanity: `wallis_two` (`∫ sin² = π`), `gup_tight_rejected` (the checker REJECTS the upper bound
`IGn ≤ 3 Pn` (i.e. `g ≤ (144/275) s`, the axis value), which is false near the axis — the
certificate is not vacuous), `fQ_bounds_zero`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevFluxQuadrature

open PlasmaLean.Certificates.BoolCert

open Real Set MeasureTheory intervalIntegral PlasmaLean.Certificates
open PlasmaLean.Design.SolovevMercierQuadrature (Gn Pn fP fQ Gn_pos)

/-! ## Wallis integrals over a full period -/

/-- `wallis n = (1/π) ∫_{-π}^{π} sin^n t dt`: `2, 0, ((n+1)/(n+2)) wallis n`. -/
@[expose] def wallis : ℕ → ℚ
  | 0 => 2
  | 1 => 0
  | n + 2 => (n + 1) / (n + 2) * wallis n

/-- **Wallis integrals**: `∫_{-π}^{π} sin^n t dt = π · wallis n`. -/
theorem integral_sin_pow_wallis : ∀ n : ℕ, ∫ t in (-π)..π, Real.sin t ^ n = π * wallis n
  | 0 => by simp [wallis]; ring
  | 1 => by simp [wallis]
  | n + 2 => by
    rw [integral_sin_pow, integral_sin_pow_wallis n]
    simp only [Real.sin_neg, Real.sin_pi, neg_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, zero_pow, zero_mul, sub_self, zero_div, zero_add, wallis]
    push_cast
    ring

/-- Sanity: `∫_{-π}^{π} sin² t dt = π`. -/
theorem wallis_two : wallis 2 = 1 := by norm_num [wallis]

/-! ## Bivariate polynomials `Σ c ε^a y^b` -/

/-- A bivariate polynomial as a list of terms `(a, b, c)` meaning `c ε^a y^b`. -/
abbrev BPoly := List (ℕ × ℕ × ℚ)

namespace BPoly

/-- Real evaluation `Σ c ε^a y^b`. -/
@[expose] def eval (p : BPoly) (ε y : ℝ) : ℝ :=
  (p.map fun m => (m.2.2 : ℝ) * ε ^ m.1 * y ^ m.2.1).sum

/-- The empty polynomial evaluates to `0`. -/
@[simp] theorem eval_nil (ε y : ℝ) : eval [] ε y = 0 := rfl

/-- Evaluation of a term followed by a polynomial. -/
@[simp] theorem eval_cons (m : ℕ × ℕ × ℚ) (p : BPoly) (ε y : ℝ) :
    eval (m :: p) ε y = (m.2.2 : ℝ) * ε ^ m.1 * y ^ m.2.1 + eval p ε y := by
  simp [eval]

/-- Evaluation is additive over concatenation. -/
@[simp] theorem eval_append (p q : BPoly) (ε y : ℝ) :
    eval (p ++ q) ε y = eval p ε y + eval q ε y := by
  simp [eval]

/-- Multiplication of one term into a polynomial. -/
@[expose] def mulTerm (m : ℕ × ℕ × ℚ) (q : BPoly) : BPoly :=
  q.map fun n => (m.1 + n.1, m.2.1 + n.2.1, m.2.2 * n.2.2)

/-- Evaluation of a term times a polynomial. -/
theorem eval_mulTerm (m : ℕ × ℕ × ℚ) (q : BPoly) (ε y : ℝ) :
    eval (mulTerm m q) ε y = (m.2.2 : ℝ) * ε ^ m.1 * y ^ m.2.1 * eval q ε y := by
  induction q with
  | nil => simp [mulTerm]
  | cons n q ih =>
    simp only [mulTerm, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- Exact product of bivariate polynomials. -/
@[expose] def mul (p q : BPoly) : BPoly := p.flatMap fun m => mulTerm m q

/-- Evaluation is multiplicative. -/
@[simp] theorem eval_mul (p q : BPoly) (ε y : ℝ) :
    eval (mul p q) ε y = eval p ε y * eval q ε y := by
  induction p with
  | nil => simp [mul]
  | cons m p ih =>
    simp only [mul, List.flatMap_cons, eval_append, eval_cons] at ih ⊢
    rw [ih, eval_mulTerm]; ring

/-- Scaling by a rational. -/
@[expose] def scale (k : ℚ) (p : BPoly) : BPoly := p.map fun m => (m.1, m.2.1, k * m.2.2)

/-- Evaluation commutes with scaling. -/
@[simp] theorem eval_scale (k : ℚ) (p : BPoly) (ε y : ℝ) :
    eval (scale k p) ε y = k * eval p ε y := by
  induction p with
  | nil => simp [scale]
  | cons m p ih =>
    simp only [scale, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- The terms `(k+i, k+i, uᵢ)`: the univariate polynomial `u` at `x = ε y`, times `(εy)^k`. -/
@[expose] def diagAux : ℕ → List ℚ → BPoly
  | _, [] => []
  | k, c :: u => (k, k, c) :: diagAux (k + 1) u

/-- Evaluation of `diagAux k u` is `(εy)^k u(εy)`. -/
theorem eval_diagAux (k : ℕ) (u : List ℚ) (ε y : ℝ) :
    eval (diagAux k u) ε y = (ε * y) ^ k * QPoly.eval u (ε * y) := by
  induction u generalizing k with
  | nil => simp [diagAux]
  | cons c u ih =>
    simp only [diagAux, eval_cons, ih, QPoly.eval_cons]
    rw [mul_pow]; ring

/-- The univariate polynomial `u` evaluated at `x = ε y`. -/
@[expose] def diag (u : List ℚ) : BPoly := diagAux 0 u

/-- Evaluation of `diag u` is `u(εy)`. -/
@[simp] theorem eval_diag (u : List ℚ) (ε y : ℝ) :
    eval (diag u) ε y = QPoly.eval u (ε * y) := by
  simp [diag, eval_diagAux]

/-- The monomial `c x^a` as a coefficient list. -/
@[expose] def mono : ℕ → ℚ → List ℚ
  | 0, c => [c]
  | a + 1, c => 0 :: mono a c

/-- Evaluation of the monomial list. -/
theorem eval_mono (a : ℕ) (c : ℚ) (x : ℝ) : QPoly.eval (mono a c) x = c * x ^ a := by
  induction a with
  | zero => simp [mono]
  | succ a ih => simp [mono, ih]; ring

/-- `(1/π) ∫_{-π}^{π} p(ε, sin t) dt` as a univariate polynomial in `ε`. -/
@[expose] def toEps : BPoly → List ℚ
  | [] => []
  | m :: p => QPoly.add (mono m.1 (m.2.2 * wallis m.2.1)) (toEps p)

/-- Bivariate polynomials are continuous. -/
theorem continuous_eval (p : BPoly) (ε : ℝ) : Continuous fun y => eval p ε y := by
  induction p with
  | nil => simpa using continuous_const
  | cons m p ih => simp only [eval_cons]; fun_prop

/-- **Exact integration**: `∫_{-π}^{π} p(ε, sin t) dt = π · toEps p (ε)`. -/
theorem integral_bpoly (p : BPoly) (ε : ℝ) :
    ∫ t in (-π)..π, eval p ε (Real.sin t) = π * QPoly.eval (toEps p) ε := by
  induction p with
  | nil => simp [toEps]
  | cons m p ih =>
    simp only [eval_cons, toEps, QPoly.eval_add, eval_mono]
    have h1 : IntervalIntegrable (fun t => (m.2.2 : ℝ) * ε ^ m.1 * Real.sin t ^ m.2.1) volume
        (-π) π := Continuous.intervalIntegrable (by fun_prop) _ _
    have h2 : IntervalIntegrable (fun t => eval p ε (Real.sin t)) volume (-π) π :=
      ((continuous_eval p ε).comp Real.continuous_sin).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 h2, ih,
      intervalIntegral.integral_const_mul, integral_sin_pow_wallis]
    push_cast; ring

end BPoly

/-! ## Pointwise polynomial enclosures of `(1+x)^{-3/2}` on `|x| ≤ 12/25` -/

/-- Upper polynomial: Taylor polynomial of `(1+x)^{-3/2}` of degree 11, plus `10⁻⁷`, plus
`2 |binom(-3/2, 12)| x¹²`. -/
@[expose] def U3 : List ℚ :=
  [1 + 1 / 10 ^ 7, -3 / 2, 15 / 8, -35 / 16, 315 / 128, -693 / 256, 3003 / 1024, -6435 / 2048,
    109395 / 32768, -230945 / 65536, 969969 / 262144, -2028117 / 524288, 16900975 / 2097152]

/-- Lower polynomial: Taylor polynomial of `(1+x)^{-3/2}` of degree 11, minus `10⁻⁷`. -/
@[expose] def L3 : List ℚ :=
  [1 - 1 / 10 ^ 7, -3 / 2, 15 / 8, -35 / 16, 315 / 128, -693 / 256, 3003 / 1024, -6435 / 2048,
    109395 / 32768, -230945 / 65536, 969969 / 262144, -2028117 / 524288]

/-- `(1+x)³`. -/
@[expose] def cube1 : List ℚ := [1, 3, 3, 1]

/-- 48 equal pieces of `[-12/25, 12/25]` (points after the left endpoint). -/
@[expose] def xPts : List ℚ := (List.range 48).map fun k => -12 / 25 + ((k : ℚ) + 1) / 50

/-- `U₃ ≥ 0` on `[-12/25, 12/25]`. -/
theorem U3_nonneg_check : QPoly.checkOn U3 0 (-12 / 25) (12 / 25) xPts = true := by
  bool_cert

/-- `L₃ ≥ 0` on `[-12/25, 12/25]`. -/
theorem L3_nonneg_check : QPoly.checkOn L3 0 (-12 / 25) (12 / 25) xPts = true := by
  bool_cert

/-- `U₃²(1+x)³ - 1 ≥ 5·10⁻⁸` on `[-12/25, 12/25]`. -/
theorem U3_sq_check : QPoly.checkOn (QPoly.add (QPoly.mul (QPoly.mul U3 U3) cube1) [-1])
    (1 / (2 * 10 ^ 7)) (-12 / 25) (12 / 25) xPts = true := by
  bool_cert

/-- `1 - L₃²(1+x)³ ≥ 5·10⁻⁸` on `[-12/25, 12/25]`. -/
theorem L3_sq_check : QPoly.checkOn (QPoly.add [1] (QPoly.scale (-1) (QPoly.mul (QPoly.mul L3 L3)
    cube1))) (1 / (2 * 10 ^ 7)) (-12 / 25) (12 / 25) xPts = true := by
  bool_cert

/-- `(1+x)³` evaluates to `(1+x)³`. -/
theorem cube1_eval (x : ℝ) : QPoly.eval cube1 x = (1 + x) ^ 3 := by
  simp [cube1]; ring

/-- **Pointwise enclosure** `L₃(x) ≤ (1+x)^{-3/2} ≤ U₃(x)` for `|x| ≤ 12/25`. -/
theorem fQ_bounds {x : ℝ} (hx : x ∈ Icc (-12 / 25 : ℝ) (12 / 25)) :
    QPoly.eval L3 x ≤ (√(1 + x) ^ 3)⁻¹ ∧ (√(1 + x) ^ 3)⁻¹ ≤ QPoly.eval U3 x := by
  have hx' : x ∈ Icc (((-12 / 25 : ℚ)) : ℝ) ((12 / 25 : ℚ) : ℝ) := by
    constructor <;> push_cast <;> linarith [hx.1, hx.2]
  have hU0 := QPoly.checkOn_sound U3_nonneg_check x hx'
  have hL0 := QPoly.checkOn_sound L3_nonneg_check x hx'
  have hU := QPoly.checkOn_sound U3_sq_check x hx'
  have hL := QPoly.checkOn_sound L3_sq_check x hx'
  simp only [QPoly.eval_add, QPoly.eval_mul, QPoly.eval_scale, cube1_eval] at hU hL
  push_cast at hU0 hL0 hU hL
  have hv : 0 < 1 + x := by linarith [hx.1]
  set a := √(1 + x) ^ 3 with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a ^ 2 = (1 + x) ^ 3 := by
    rw [ha, ← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, Real.sq_sqrt hv.le]
  simp only [QPoly.eval_cons, QPoly.eval_nil] at hU hL
  push_cast at hU hL
  rw [← ha2] at hU hL
  constructor
  · rw [← one_div, le_div_iff₀ ha0]
    have h0 : 0 ≤ QPoly.eval L3 x * a := mul_nonneg hL0 ha0.le
    nlinarith
  · rw [← one_div, div_le_iff₀ ha0]
    have h0 : 0 ≤ QPoly.eval U3 x * a := mul_nonneg hU0 ha0.le
    nlinarith

/-- Sanity: at `x = 0` the enclosure is `[1 - 10⁻⁷, 1 + 10⁻⁷]` around `1`. -/
theorem fQ_bounds_zero : QPoly.eval L3 0 = 1 - 1 / 10 ^ 7 ∧ QPoly.eval U3 0 = 1 + 1 / 10 ^ 7 := by
  simp [L3, U3]

/-! ## The three surface integrals and their polynomial squeezes -/

/-- `H(ε, y) = 3 + 8εy + ε² + 4ε²y²` (`Δψ̃/R = 10 H v^{-3/2}` on the surface). -/
@[expose] def Hn (ε y : ℝ) : ℝ := 3 + 8 * ε * y + ε ^ 2 + 4 * ε ^ 2 * y ^ 2

/-- `IGn ε = ∫_{-π}^{π} G(ε, sin t) v^{-3/2} dt`. -/
@[expose] def IGn (ε : ℝ) : ℝ := ∫ t in (-π)..π, Gn ε (Real.sin t) * fQ ε (Real.sin t)

/-- `IHn ε = ∫_{-π}^{π} H(ε, sin t) v^{-3/2} dt`. -/
@[expose] def IHn (ε : ℝ) : ℝ := ∫ t in (-π)..π, Hn ε (Real.sin t) * fQ ε (Real.sin t)

/-- `H = (2εy + 1)(2εy + 3) + ε² ≥ 0` for `|εy| ≤ 1/2`. -/
theorem Hn_nonneg {ε y : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (hy : y ∈ Icc (-1 : ℝ) 1) :
    0 ≤ Hn ε y := by
  have h1 : -(1 / 2) ≤ ε * y := by nlinarith [hy.1, hy.2]
  have : Hn ε y = (2 * (ε * y) + 1) * (2 * (ε * y) + 3) + ε ^ 2 := by unfold Hn; ring
  rw [this]
  have := sq_nonneg ε
  nlinarith

/-- `2y + ε + εy²`. -/
@[expose] def AB : BPoly := [(0, 1, 2), (1, 0, 1), (1, 2, 1)]
/-- `1 + εy`. -/
@[expose] def VB : BPoly := [(0, 0, 1), (1, 1, 1)]
/-- `1 - y²`. -/
@[expose] def OmB : BPoly := [(0, 0, 1), (0, 2, -1)]
/-- `G = (2y + ε(1+y²))² + 2(1-y²)(1+εy)²` as a bivariate polynomial. -/
@[expose] def GnB : BPoly := BPoly.mul AB AB ++ BPoly.scale 2 (BPoly.mul OmB (BPoly.mul VB VB))
/-- `H` as a bivariate polynomial. -/
@[expose] def HnB : BPoly := [(0, 0, 3), (1, 1, 8), (2, 0, 1), (2, 2, 4)]

/-- `VB` evaluates to `1 + εy`. -/
theorem VB_eval (ε y : ℝ) : BPoly.eval VB ε y = 1 + ε * y := by simp [VB]
/-- `GnB` evaluates to `G`. -/
theorem GnB_eval (ε y : ℝ) : BPoly.eval GnB ε y = Gn ε y := by
  simp [GnB, AB, VB, OmB, Gn]; ring
/-- `HnB` evaluates to `H`. -/
theorem HnB_eval (ε y : ℝ) : BPoly.eval HnB ε y = Hn ε y := by simp [HnB, Hn]; ring

/-- `π ·` upper polynomial of `IGn`. -/
@[expose] def UG : List ℚ := BPoly.toEps (BPoly.mul GnB (BPoly.diag U3))
/-- `π ·` lower polynomial of `IGn`. -/
@[expose] def LG : List ℚ := BPoly.toEps (BPoly.mul GnB (BPoly.diag L3))
/-- `π ·` upper polynomial of `IHn`. -/
@[expose] def UH : List ℚ := BPoly.toEps (BPoly.mul HnB (BPoly.diag U3))
/-- `π ·` lower polynomial of `IHn`. -/
@[expose] def LH : List ℚ := BPoly.toEps (BPoly.mul HnB (BPoly.diag L3))
/-- `π ·` upper polynomial of `Pn`. -/
@[expose] def UP : List ℚ := BPoly.toEps (BPoly.mul VB (BPoly.diag U3))
/-- `π ·` lower polynomial of `Pn`. -/
@[expose] def LP : List ℚ := BPoly.toEps (BPoly.mul VB (BPoly.diag L3))

/-- `x = εy` stays in `[-12/25, 12/25]`. -/
theorem mul_mem {ε y : ℝ} (hε : ε ∈ Icc (0 : ℝ) (12 / 25)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    ε * y ∈ Icc (-12 / 25 : ℝ) (12 / 25) := by
  obtain ⟨h0, h1⟩ := hε
  constructor <;> nlinarith [hy.1, hy.2]

/-- `v^{-1/2} = v · v^{-3/2}`. -/
theorem fP_eq_mul {ε y : ℝ} (hv : 0 < 1 + ε * y) : fP ε y = (1 + ε * y) * fQ ε y := by
  unfold fP fQ
  have ha := Real.sqrt_pos.2 hv
  have ha2 := Real.sq_sqrt hv.le
  rw [show √(1 + ε * y) ^ 3 = (1 + ε * y) * √(1 + ε * y) by rw [pow_succ, ha2]]
  field_simp

/-- Continuity of `t ↦ f(ε, sin t)` for a continuous-on-`[-1,1]` integrand. -/
theorem cont_sin {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    Continuous fun t => f (Real.sin t) :=
  hf.comp_continuous Real.continuous_sin fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩

/-- Squeeze of an integral by two bivariate polynomials. -/
theorem squeeze {f : ℝ → ℝ} {lo hi : BPoly} {ε : ℝ} (hf : Continuous f)
    (h : ∀ t, BPoly.eval lo ε (Real.sin t) ≤ f t ∧ f t ≤ BPoly.eval hi ε (Real.sin t)) :
    π * QPoly.eval (BPoly.toEps lo) ε ≤ ∫ t in (-π)..π, f t ∧
      ∫ t in (-π)..π, f t ≤ π * QPoly.eval (BPoly.toEps hi) ε := by
  have hle : -π ≤ π := by linarith [Real.pi_pos]
  have ilo := ((BPoly.continuous_eval lo ε).comp Real.continuous_sin).intervalIntegrable
    (μ := volume) (-π) π
  have ihi := ((BPoly.continuous_eval hi ε).comp Real.continuous_sin).intervalIntegrable
    (μ := volume) (-π) π
  have ifn := hf.intervalIntegrable (μ := volume) (-π) π
  rw [← BPoly.integral_bpoly, ← BPoly.integral_bpoly]
  exact ⟨intervalIntegral.integral_mono_on hle ilo ifn fun t _ => (h t).1,
    intervalIntegral.integral_mono_on hle ifn ihi fun t _ => (h t).2⟩

section squeezes

variable {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (12 / 25))
include hε

/-- `ε ≤ 1/2` on the domain. -/
theorem hε_half : ε ≤ 1 / 2 := by linarith [hε.2]

/-- `π LG(ε) ≤ IGn ε ≤ π UG(ε)`. -/
theorem IGn_squeeze : π * QPoly.eval LG ε ≤ IGn ε ∧ IGn ε ≤ π * QPoly.eval UG ε := by
  have h' := hε_half hε
  refine squeeze ((cont_sin (by unfold Gn; fun_prop)).mul
    (cont_sin (SolovevMercierQuadrature.continuousOn_fQ hε.1 h'))) fun t => ?_
  have hy : Real.sin t ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have hb := fQ_bounds (mul_mem hε hy)
  have hG := (Gn_pos hε.1 h' hy).le
  simp only [BPoly.eval_mul, GnB_eval, BPoly.eval_diag]
  unfold fQ
  exact ⟨mul_le_mul_of_nonneg_left hb.1 hG, mul_le_mul_of_nonneg_left hb.2 hG⟩

/-- `π LH(ε) ≤ IHn ε ≤ π UH(ε)`. -/
theorem IHn_squeeze : π * QPoly.eval LH ε ≤ IHn ε ∧ IHn ε ≤ π * QPoly.eval UH ε := by
  have h' := hε_half hε
  refine squeeze ((cont_sin (by unfold Hn; fun_prop)).mul
    (cont_sin (SolovevMercierQuadrature.continuousOn_fQ hε.1 h'))) fun t => ?_
  have hy : Real.sin t ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have hb := fQ_bounds (mul_mem hε hy)
  have hH := Hn_nonneg hε.1 h' hy
  simp only [BPoly.eval_mul, HnB_eval, BPoly.eval_diag]
  unfold fQ
  exact ⟨mul_le_mul_of_nonneg_left hb.1 hH, mul_le_mul_of_nonneg_left hb.2 hH⟩

/-- `π LP(ε) ≤ Pn ε ≤ π UP(ε)`. -/
theorem Pn_squeeze : π * QPoly.eval LP ε ≤ Pn ε ∧ Pn ε ≤ π * QPoly.eval UP ε := by
  have h' := hε_half hε
  refine squeeze (cont_sin (SolovevMercierQuadrature.continuousOn_fP hε.1 h')) fun t => ?_
  have hy : Real.sin t ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have hb := fQ_bounds (mul_mem hε hy)
  have hv : 0 < 1 + ε * Real.sin t := by nlinarith [hy.1, hy.2, hε.1]
  simp only [BPoly.eval_mul, VB_eval, BPoly.eval_diag]
  rw [fP_eq_mul hv]
  unfold fQ
  exact ⟨mul_le_mul_of_nonneg_left hb.1 hv.le, mul_le_mul_of_nonneg_left hb.2 hv.le⟩

end squeezes

/-! ## The four final polynomial checks in `ε ∈ [0, 12/25]` -/

/-- Pieces of `[0, 12/25]`. -/
@[expose] def epsPts : List ℚ := [3 / 25, 6 / 25, 9 / 25, 12 / 25]

/-- `192 LG - 539 UP ≥ 0` (lower bound of `g/s`). -/
theorem glo_check :
    QPoly.checkOn (QPoly.add (QPoly.scale 192 LG) (QPoly.scale (-539) UP)) 0 0 (12 / 25) epsPts
      = true := by bool_cert

/-- `385 LP - 128 UG ≥ 0` (upper bound of `g/s`). -/
theorem gup_check :
    QPoly.checkOn (QPoly.add (QPoly.scale 385 LP) (QPoly.scale (-128) UG)) 0 0 (12 / 25) epsPts
      = true := by bool_cert

/-- `192 LH - 539 UP ≥ 0` (lower bound of `h`). -/
theorem hlo_check :
    QPoly.checkOn (QPoly.add (QPoly.scale 192 LH) (QPoly.scale (-539) UP)) 0 0 (12 / 25) epsPts
      = true := by bool_cert

/-- `385 LP - 128 UH ≥ 0` (upper bound of `h`). -/
theorem hup_check :
    QPoly.checkOn (QPoly.add (QPoly.scale 385 LP) (QPoly.scale (-128) UH)) 0 0 (12 / 25) epsPts
      = true := by bool_cert

/-- Rejected fixture: the checker does NOT certify `IGn ≤ 3 Pn` (`g ≤ (144/275) s`, the axis
value, which fails just off the axis to within the enclosure width): the certificate's
margin is genuine, not vacuous. -/
theorem gup_tight_rejected :
    QPoly.checkOn (QPoly.add (QPoly.scale 3 LP) (QPoly.scale (-1) UG)) 0 0 (12 / 25) epsPts
      = false := by bool_cert

/-- From a polynomial check to a real inequality on `[0, 12/25]`. -/
theorem check_apply {p q : List ℚ} {a b : ℚ}
    (h : QPoly.checkOn (QPoly.add (QPoly.scale a p) (QPoly.scale (-b) q)) 0 0 (12 / 25) epsPts
      = true) {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (12 / 25)) :
    (b : ℝ) * QPoly.eval q ε ≤ a * QPoly.eval p ε := by
  have := QPoly.checkOn_sound h ε (by constructor <;> push_cast <;> linarith [hε.1, hε.2])
  simp only [QPoly.eval_add, QPoly.eval_scale] at this
  push_cast at this
  linarith

/-- **Certified enclosures of the flux-surface ratios** for every `ε ∈ [0, 12/25]`:
`539/192 ≤ IGn/Pn, IHn/Pn ≤ 385/128`. -/
theorem flux_ratio_bounds {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) (12 / 25)) :
    539 * Pn ε ≤ 192 * IGn ε ∧ 128 * IGn ε ≤ 385 * Pn ε ∧
      539 * Pn ε ≤ 192 * IHn ε ∧ 128 * IHn ε ≤ 385 * Pn ε := by
  have hP := Pn_squeeze hε
  have hG := IGn_squeeze hε
  have hH := IHn_squeeze hε
  have c1 := check_apply glo_check hε
  have c2 := check_apply gup_check hε
  have c3 := check_apply hlo_check hε
  have c4 := check_apply hup_check hε
  push_cast at c1 c2 c3 c4
  have hπ := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_left c1 hπ.le,
    mul_le_mul_of_nonneg_left c2 hπ.le, mul_le_mul_of_nonneg_left c3 hπ.le,
    mul_le_mul_of_nonneg_left c4 hπ.le]

end PlasmaLean.Design.SolovevFluxQuadrature
