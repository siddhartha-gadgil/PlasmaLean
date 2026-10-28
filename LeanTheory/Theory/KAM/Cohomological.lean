/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.Diophantine
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The cohomological equation on the 2-torus in weighted `ℓ¹` norms

This is the linear small-divisor
problem that every Newton step of the a posteriori KAM theorem solves (twice): given a zero-mean
`f` on `𝕋² = (ℝ/2πℤ)²`, find `u` with

  `∂_ψ u + ω ∂_θ u = f`.

**Fourier model and norm.** A function is represented by its Fourier coefficients
`f : ℤ × ℤ → ℂ`, the pair `(k, m)` indexing the mode `e^{i(kθ + mψ)}` (`fourierMode`). The norm is
the weighted `ℓ¹` norm

  `‖f‖_r = ∑_{k,m} |f_{k,m}| e^{r(|k| + |m|)}`   (`wnorm`, finiteness `InWeighted`),

with `r = 2πρ` when the strip half-width `ρ` is measured in turns. It dominates the sup norm of
the Fourier series on the complex strip `|Im θ|, |Im ψ| ≤ r`. Every estimate below is a
coefficientwise bound followed by `tsum_le_tsum`; no Banach-space structure is needed.

**Solution.** The symbol of `L_ω = ∂_ψ + ω ∂_θ` on mode `(k, m)` is `i (m + k ω)` (`divisor`).
For zero-mean `f` (`f (0,0) = 0`) and Diophantine `ω` the unique zero-mean solution is
`u_{k,m} = f_{k,m} / (i (m + k ω))` (`cohSol`, `cohSol_spec`, `cohSol_unique`).
For torus A (`ψ = 2φ − π/2`): `∂_φ + ι ∂_θ = 2 L_{ι/2}`, so one uses
`ω = ι/2` with `torusA_period_diophantine` (`γ = 0.0687`) and divides the solution by `2`.

**Estimates (main results).**
* `pow_mul_exp_neg_le`: `x^τ e^{−δx} ≤ (τ/(eδ))^τ` for `x ≥ 0`, `δ > 0`.
* `cohSol_estimate` (Rüssmann-type, crude sup version): for `(γ, τ)`-Diophantine `ω`,
  `‖u‖_{r−δ} ≤ C_R(γ, δ, τ) ‖f‖_r` with `C_R = max 1 ((τ/(eδ))^τ / γ)` (`russmannConst`); the `1`
  covers the `k = 0` modes, where the divisor is the integer `m`. For `τ = 1`, `γ ≤ 1/2` and
  `δ ≤ 2/e` the maximum is `1/(eγδ)` (`russmannConst_one_of_le`).
* `dθ_estimate`, `dψ_estimate` (Cauchy): `‖∂_θ u‖_{r−δ} ≤ (eδ)⁻¹ ‖u‖_r`, same for `∂_ψ`.
* `hasDerivAt_fourierSum_cohSol`: the coefficient solution is a genuine classical solution:
  for `r > 0` the Fourier series `U` of `u` is differentiable in `θ` and in `ψ` and
  `∂_ψ U + ω ∂_θ U = F` pointwise, `F` the Fourier series of `f`.

**Sanity.** `cohSol_zero` (zero data), `cohSol_const` (a constant has no zero-mean
obstruction: the constant mode is discarded), `cohSol_single` (one mode), and two
counterexamples without the Diophantine hypothesis: `no_solution_of_rat` (rational `ω`: a
zero-mean trigonometric monomial has **no** solution) and `divisor_lower_of_estimate` (any
estimate `‖v‖_{r−δ} ≤ C ‖f‖_r` for solutions forces `|m + kω| ≥ e^{−δ(|k|+|m|)}/C` on every
mode, so it fails for rational `ω`: `not_estimate_of_rat`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

open Complex

/-! ## Weighted `ℓ¹` norms on `ℤ²` -/

/-- The size `|k| + |m|` of the Fourier mode `(k, m)`. -/
def modeSize (km : ℤ × ℤ) : ℝ := |(km.1 : ℝ)| + |(km.2 : ℝ)|

/-- The analytic weight `e^{r(|k| + |m|)}` (strip half-width `r`, in radians). -/
def weight (r : ℝ) (km : ℤ × ℤ) : ℝ := Real.exp (r * modeSize km)

/-- `f` has finite weighted `ℓ¹` norm with weight `e^{r(|k|+|m|)}`. -/
def InWeighted (r : ℝ) (f : ℤ × ℤ → ℂ) : Prop := Summable fun km => ‖f km‖ * weight r km

/-- The weighted `ℓ¹` norm `‖f‖_r = ∑ |f_{k,m}| e^{r(|k|+|m|)}`. -/
def wnorm (r : ℝ) (f : ℤ × ℤ → ℂ) : ℝ := ∑' km, ‖f km‖ * weight r km

/-- Mode sizes are nonnegative. -/
theorem modeSize_nonneg (km : ℤ × ℤ) : 0 ≤ modeSize km := by unfold modeSize; positivity

/-- Weights are positive. -/
theorem weight_pos (r : ℝ) (km : ℤ × ℤ) : 0 < weight r km := Real.exp_pos _

/-- `e^{(r−δ)s} = e^{rs} e^{−δs}`. -/
theorem weight_sub (r δ : ℝ) (km : ℤ × ℤ) :
    weight (r - δ) km = weight r km * Real.exp (-δ * modeSize km) := by
  unfold weight; rw [← Real.exp_add]; ring_nf

/-- Weights increase with `r`. -/
theorem weight_mono {r r' : ℝ} (h : r' ≤ r) (km : ℤ × ℤ) : weight r' km ≤ weight r km := by
  unfold weight
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (modeSize_nonneg km))

/-- For `r ≥ 0` the weight is at least `1`. -/
theorem one_le_weight {r : ℝ} (hr : 0 ≤ r) (km : ℤ × ℤ) : 1 ≤ weight r km :=
  Real.one_le_exp (mul_nonneg hr (modeSize_nonneg km))

/-- The weighted norm is nonnegative. -/
theorem wnorm_nonneg (r : ℝ) (f : ℤ × ℤ → ℂ) : 0 ≤ wnorm r f :=
  tsum_nonneg fun km => mul_nonneg (norm_nonneg _) (weight_pos r km).le

/-- Sanity: the zero function has norm `0`. -/
@[simp] theorem wnorm_zero (r : ℝ) : wnorm r 0 = 0 := by simp [wnorm]

/-- A single coefficient is bounded by the norm. -/
theorem norm_mul_weight_le_wnorm {r : ℝ} {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) (km : ℤ × ℤ) :
    ‖f km‖ * weight r km ≤ wnorm r f :=
  hf.le_tsum km fun j _ => mul_nonneg (norm_nonneg _) (weight_pos r j).le

/-- **Comparison principle.** A coefficientwise bound `‖g‖ w' ≤ C ‖f‖ w` transfers to the
weighted norms (and gives summability). -/
theorem wnorm_le_of_termwise {r r' C : ℝ} {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f)
    (h : ∀ km, ‖g km‖ * weight r' km ≤ C * (‖f km‖ * weight r km)) :
    InWeighted r' g ∧ wnorm r' g ≤ C * wnorm r f := by
  have hs : InWeighted r' g :=
    (hf.mul_left C).of_nonneg_of_le (fun km => mul_nonneg (norm_nonneg _) (weight_pos _ _).le) h
  refine ⟨hs, ?_⟩
  unfold wnorm
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum h (hf.mul_left C)

/-! ## The elementary sup bound -/

/-- **The sup bound** `x^τ e^{−δx} ≤ (τ/(eδ))^τ` for `x ≥ 0`, `δ > 0` (the maximum of
`x ↦ x^τ e^{−δx}` is at `x = τ/δ`). -/
theorem pow_mul_exp_neg_le {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) (τ : ℕ) :
    x ^ τ * Real.exp (-δ * x) ≤ ((τ : ℝ) / (Real.exp 1 * δ)) ^ τ := by
  rcases Nat.eq_zero_or_pos τ with rfl | hτ
  · simp only [pow_zero, one_mul]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  -- the one-factor bound `x e^{−δx/τ} ≤ τ/(eδ)`
  set y := δ * x / τ with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y ≤ Real.exp (y - 1) := by linarith [Real.add_one_le_exp (y - 1)]
  have h2 : y * Real.exp (-y) ≤ Real.exp (-1) := by
    calc y * Real.exp (-y) ≤ Real.exp (y - 1) * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
  have hone : x * Real.exp (-δ * x / τ) ≤ τ / (Real.exp 1 * δ) := by
    have e1 : x * Real.exp (-δ * x / τ) = (τ / δ) * (y * Real.exp (-y)) := by
      rw [hy]; field_simp
    have e2 : (τ : ℝ) / (Real.exp 1 * δ) = (τ / δ) * Real.exp (-1) := by
      rw [Real.exp_neg]; field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsplit : Real.exp (-δ * x) = Real.exp (-δ * x / τ) ^ τ := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [hsplit, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hone τ

/-! ## The cohomological operator and its inverse -/

/-- The (real) small divisor `m + k ω`: `L_ω = ∂_ψ + ω ∂_θ` acts on mode `(k, m)` by
multiplication by `i (m + k ω)`. -/
def divisor (ω : ℝ) (km : ℤ × ℤ) : ℝ := km.2 + km.1 * ω

/-- The `θ`-derivative on Fourier coefficients: `(∂_θ u)_{k,m} = i k u_{k,m}`. -/
def dθ (u : ℤ × ℤ → ℂ) (km : ℤ × ℤ) : ℂ := I * km.1 * u km

/-- The `ψ`-derivative on Fourier coefficients: `(∂_ψ u)_{k,m} = i m u_{k,m}`. -/
def dψ (u : ℤ × ℤ → ℂ) (km : ℤ × ℤ) : ℂ := I * km.2 * u km

/-- The operator `L_ω u = ∂_ψ u + ω ∂_θ u` on Fourier coefficients. -/
def cohOp (ω : ℝ) (u : ℤ × ℤ → ℂ) (km : ℤ × ℤ) : ℂ := dψ u km + (ω : ℂ) * dθ u km

/-- `L_ω` is multiplication by the symbol `i (m + kω)`. -/
theorem cohOp_eq (ω : ℝ) (u : ℤ × ℤ → ℂ) (km : ℤ × ℤ) :
    cohOp ω u km = I * (divisor ω km : ℂ) * u km := by
  simp only [cohOp, dψ, dθ, divisor]; push_cast; ring

/-- The zero-mean solution `u_{k,m} = f_{k,m} / (i (m + kω))` of `L_ω u = f` (for `(k,m) = 0`
the divisor is `0` and Lean's `x / 0 = 0` gives `u_{0,0} = 0`). -/
def cohSol (ω : ℝ) (f : ℤ × ℤ → ℂ) (km : ℤ × ℤ) : ℂ := f km / (I * (divisor ω km : ℂ))

/-- The solution has zero mean. -/
@[simp] theorem cohSol_zero_mode (ω : ℝ) (f : ℤ × ℤ → ℂ) : cohSol ω f (0, 0) = 0 := by
  simp [cohSol, divisor]

/-- Modulus of the solution coefficients: `|u_{k,m}| = |f_{k,m}| / |m + kω|`. -/
theorem norm_cohSol (ω : ℝ) (f : ℤ × ℤ → ℂ) (km : ℤ × ℤ) :
    ‖cohSol ω f km‖ = ‖f km‖ / |divisor ω km| := by
  simp [cohSol, Complex.norm_real]

/-- **The solution solves the cohomological equation** for zero-mean `f` and Diophantine `ω`
with `γ > 0`. -/
theorem cohSol_spec {ω γ : ℝ} {τ : ℕ} (hD : Diophantine ω γ τ) (hγ : 0 < γ)
    {f : ℤ × ℤ → ℂ} (hf0 : f (0, 0) = 0) (km : ℤ × ℤ) : cohOp ω (cohSol ω f) km = f km := by
  rw [cohOp_eq]
  by_cases h : km = (0, 0)
  · subst h; simp [hf0]
  · have hd : (divisor ω km : ℂ) ≠ 0 := by
      have := hD.divisor_ne_zero hγ (k := km.1) (m := km.2) (by simpa using h)
      exact_mod_cast this
    simp only [cohSol]
    field_simp

/-- **Uniqueness.** A zero-mean solution of `L_ω v = f` equals `cohSol ω f`. -/
theorem cohSol_unique {ω γ : ℝ} {τ : ℕ} (hD : Diophantine ω γ τ) (hγ : 0 < γ)
    {f v : ℤ × ℤ → ℂ} (hv0 : v (0, 0) = 0) (hv : ∀ km, cohOp ω v km = f km) :
    v = cohSol ω f := by
  funext km
  by_cases h : km = (0, 0)
  · subst h; simp [hv0]
  · have hd : (divisor ω km : ℂ) ≠ 0 := by
      have := hD.divisor_ne_zero hγ (k := km.1) (m := km.2) (by simpa using h)
      exact_mod_cast this
    rw [cohSol, ← hv km, cohOp_eq]
    field_simp

/-! ## The Rüssmann-type estimate -/

/-- The crude Rüssmann constant `C_R(γ, δ, τ) = max 1 ((τ/(eδ))^τ / γ)`. -/
def russmannConst (γ δ : ℝ) (τ : ℕ) : ℝ := max 1 (((τ : ℝ) / (Real.exp 1 * δ)) ^ τ / γ)

/-- For `τ = 1`, `0 < γ ≤ 1/2` (always true for Diophantine `γ`, `Diophantine.le_half`) and
`0 < δ ≤ 2/e`, the Rüssmann constant is `1/(eγδ)`. -/
theorem russmannConst_one_of_le {γ δ : ℝ} (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hδ : 0 < δ)
    (hδ2 : δ ≤ 2 / Real.exp 1) : russmannConst γ δ 1 = 1 / (Real.exp 1 * γ * δ) := by
  have he := Real.exp_pos 1
  unfold russmannConst
  rw [max_eq_right]
  · push_cast; field_simp
  · push_cast
    rw [pow_one, le_div_iff₀ hγ, one_mul, le_div_iff₀ (by positivity)]
    have : Real.exp 1 * δ ≤ 2 := by
      rw [le_div_iff₀ he] at hδ2; linarith
    nlinarith

/-- **Termwise small-divisor bound.** For `(γ, τ)`-Diophantine `ω` with `γ > 0` and `δ > 0`,
`|u_{k,m}| e^{(r−δ)(|k|+|m|)} ≤ C_R |f_{k,m}| e^{r(|k|+|m|)}` for `u = cohSol ω f`. -/
theorem cohSol_termwise {ω γ δ : ℝ} {τ : ℕ} (hD : Diophantine ω γ τ) (hγ : 0 < γ) (hδ : 0 < δ)
    (r : ℝ) (f : ℤ × ℤ → ℂ) (km : ℤ × ℤ) :
    ‖cohSol ω f km‖ * weight (r - δ) km ≤ russmannConst γ δ τ * (‖f km‖ * weight r km) := by
  obtain ⟨k, m⟩ := km
  rw [norm_cohSol, weight_sub]
  have hw := weight_pos r (k, m)
  have hfn := norm_nonneg (f (k, m))
  have hexp : Real.exp (-δ * modeSize (k, m)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [modeSize_nonneg (k, m)])
  by_cases hk : k = 0
  · subst hk
    by_cases hm : m = 0
    · subst hm
      simp only [divisor, Int.cast_zero, zero_mul, add_zero, abs_zero, div_zero, zero_mul]
      exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (mul_nonneg hfn hw.le)
    · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
        exact_mod_cast this
      simp only [divisor, Int.cast_zero, zero_mul, add_zero]
      have h1 : ‖f (0, m)‖ / |(m : ℝ)| ≤ ‖f (0, m)‖ :=
        div_le_self hfn hm1
      calc ‖f (0, m)‖ / |(m : ℝ)| * (weight r (0, m) * Real.exp (-δ * modeSize (0, m)))
          ≤ ‖f (0, m)‖ * (weight r (0, m) * 1) := by
            apply mul_le_mul h1 (mul_le_mul_of_nonneg_left hexp hw.le) (by positivity) hfn
        _ = 1 * (‖f (0, m)‖ * weight r (0, m)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hfn hw.le)
  · have hK : 0 < |(k : ℝ)| := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    have hdiv := hD.abs_divisor_ge hk m
    have hdpos : 0 < |divisor ω (k, m)| := lt_of_lt_of_le (by positivity) hdiv
    -- `1/|d| ≤ |k|^τ/γ`
    have hinv : 1 / |divisor ω (k, m)| ≤ |(k : ℝ)| ^ τ / γ := by
      rw [div_le_div_iff₀ hdpos hγ, one_mul]
      have := (div_le_iff₀ (by positivity)).1 hdiv
      simpa [divisor, mul_comm] using this
    -- `e^{−δ(|k|+|m|)} ≤ e^{−δ|k|}`
    have hexpk : Real.exp (-δ * modeSize (k, m)) ≤ Real.exp (-δ * |(k : ℝ)|) := by
      apply Real.exp_le_exp.2
      have : |(k : ℝ)| ≤ modeSize (k, m) := by
        simp only [modeSize]; linarith [abs_nonneg (m : ℝ)]
      nlinarith
    have hsup := pow_mul_exp_neg_le (abs_nonneg (k : ℝ)) hδ τ
    have key : 1 / |divisor ω (k, m)| * Real.exp (-δ * modeSize (k, m)) ≤
        russmannConst γ δ τ := by
      calc 1 / |divisor ω (k, m)| * Real.exp (-δ * modeSize (k, m))
          ≤ |(k : ℝ)| ^ τ / γ * Real.exp (-δ * |(k : ℝ)|) :=
            mul_le_mul hinv hexpk (Real.exp_pos _).le (by positivity)
        _ = (|(k : ℝ)| ^ τ * Real.exp (-δ * |(k : ℝ)|)) / γ := by ring
        _ ≤ ((τ : ℝ) / (Real.exp 1 * δ)) ^ τ / γ := by gcongr
        _ ≤ russmannConst γ δ τ := le_max_right _ _
    calc ‖f (k, m)‖ / |divisor ω (k, m)| * (weight r (k, m) * Real.exp (-δ * modeSize (k, m)))
        = (1 / |divisor ω (k, m)| * Real.exp (-δ * modeSize (k, m))) *
            (‖f (k, m)‖ * weight r (k, m)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key (mul_nonneg hfn hw.le)

/-- **Rüssmann-type estimate for the cohomological equation.** If `ω` is `(γ, τ)`-Diophantine
(`γ > 0`), `δ > 0` and `‖f‖_r < ∞`, then `u = cohSol ω f` satisfies `‖u‖_{r−δ} < ∞` and
`‖u‖_{r−δ} ≤ max 1 ((τ/(eδ))^τ/γ) · ‖f‖_r`. -/
theorem cohSol_estimate {ω γ δ r : ℝ} {τ : ℕ} (hD : Diophantine ω γ τ) (hγ : 0 < γ)
    (hδ : 0 < δ) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol ω f) ∧
      wnorm (r - δ) (cohSol ω f) ≤ russmannConst γ δ τ * wnorm r f :=
  wnorm_le_of_termwise hf (cohSol_termwise hD hγ hδ r f)

/-- The `τ = 1` form used by K3: `‖u‖_{r−δ} ≤ ‖f‖_r / (e γ δ)` when `δ ≤ 2/e`. -/
theorem cohSol_estimate_one {ω γ δ r : ℝ} (hD : Diophantine ω γ 1) (hγ : 0 < γ)
    (hδ : 0 < δ) (hδ2 : δ ≤ 2 / Real.exp 1) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol ω f) ∧
      wnorm (r - δ) (cohSol ω f) ≤ wnorm r f / (Real.exp 1 * γ * δ) := by
  obtain ⟨h1, h2⟩ := cohSol_estimate hD hγ hδ hf
  rw [russmannConst_one_of_le hγ hD.le_half hδ hδ2] at h2
  exact ⟨h1, by rw [div_eq_mul_one_div, mul_comm]; exact h2⟩

/-! ## Cauchy estimates -/

/-- **Cauchy estimate for `∂_θ`:** `‖∂_θ u‖_{r−δ} ≤ (eδ)⁻¹ ‖u‖_r`. -/
theorem dθ_estimate {r δ : ℝ} (hδ : 0 < δ) {u : ℤ × ℤ → ℂ} (hu : InWeighted r u) :
    InWeighted (r - δ) (dθ u) ∧ wnorm (r - δ) (dθ u) ≤ (Real.exp 1 * δ)⁻¹ * wnorm r u := by
  refine wnorm_le_of_termwise hu fun km => ?_
  obtain ⟨k, m⟩ := km
  have hsup := pow_mul_exp_neg_le (abs_nonneg (k : ℝ)) hδ 1
  simp only [pow_one, Nat.cast_one] at hsup
  have hexpk : Real.exp (-δ * modeSize (k, m)) ≤ Real.exp (-δ * |(k : ℝ)|) := by
    apply Real.exp_le_exp.2
    have : |(k : ℝ)| ≤ modeSize (k, m) := by
      simp only [modeSize]; linarith [abs_nonneg (m : ℝ)]
    nlinarith
  have hfac : |(k : ℝ)| * Real.exp (-δ * modeSize (k, m)) ≤ (Real.exp 1 * δ)⁻¹ := by
    calc |(k : ℝ)| * Real.exp (-δ * modeSize (k, m)) ≤ |(k : ℝ)| * Real.exp (-δ * |(k : ℝ)|) :=
          mul_le_mul_of_nonneg_left hexpk (abs_nonneg _)
      _ ≤ 1 / (Real.exp 1 * δ) := hsup
      _ = _ := one_div _
  rw [weight_sub]
  have hn : ‖dθ u (k, m)‖ = |(k : ℝ)| * ‖u (k, m)‖ := by
    simp [dθ, Complex.norm_intCast]
  rw [hn]
  calc |(k : ℝ)| * ‖u (k, m)‖ * (weight r (k, m) * Real.exp (-δ * modeSize (k, m)))
      = (|(k : ℝ)| * Real.exp (-δ * modeSize (k, m))) * (‖u (k, m)‖ * weight r (k, m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac
        (mul_nonneg (norm_nonneg _) (weight_pos _ _).le)

/-- **Cauchy estimate for `∂_ψ`:** `‖∂_ψ u‖_{r−δ} ≤ (eδ)⁻¹ ‖u‖_r`. -/
theorem dψ_estimate {r δ : ℝ} (hδ : 0 < δ) {u : ℤ × ℤ → ℂ} (hu : InWeighted r u) :
    InWeighted (r - δ) (dψ u) ∧ wnorm (r - δ) (dψ u) ≤ (Real.exp 1 * δ)⁻¹ * wnorm r u := by
  refine wnorm_le_of_termwise hu fun km => ?_
  obtain ⟨k, m⟩ := km
  have hsup := pow_mul_exp_neg_le (abs_nonneg (m : ℝ)) hδ 1
  simp only [pow_one, Nat.cast_one] at hsup
  have hexpm : Real.exp (-δ * modeSize (k, m)) ≤ Real.exp (-δ * |(m : ℝ)|) := by
    apply Real.exp_le_exp.2
    have : |(m : ℝ)| ≤ modeSize (k, m) := by
      simp only [modeSize]; linarith [abs_nonneg (k : ℝ)]
    nlinarith
  have hfac : |(m : ℝ)| * Real.exp (-δ * modeSize (k, m)) ≤ (Real.exp 1 * δ)⁻¹ := by
    calc |(m : ℝ)| * Real.exp (-δ * modeSize (k, m)) ≤ |(m : ℝ)| * Real.exp (-δ * |(m : ℝ)|) :=
          mul_le_mul_of_nonneg_left hexpm (abs_nonneg _)
      _ ≤ 1 / (Real.exp 1 * δ) := hsup
      _ = _ := one_div _
  rw [weight_sub]
  have hn : ‖dψ u (k, m)‖ = |(m : ℝ)| * ‖u (k, m)‖ := by
    simp [dψ, Complex.norm_intCast]
  rw [hn]
  calc |(m : ℝ)| * ‖u (k, m)‖ * (weight r (k, m) * Real.exp (-δ * modeSize (k, m)))
      = (|(m : ℝ)| * Real.exp (-δ * modeSize (k, m))) * (‖u (k, m)‖ * weight r (k, m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac
        (mul_nonneg (norm_nonneg _) (weight_pos _ _).le)

/-! ## The classical solution -/

/-- The Fourier mode `e^{i(kθ + mψ)}`. -/
def fourierMode (km : ℤ × ℤ) (θ ψ : ℝ) : ℂ :=
  Complex.exp (((km.1 * θ + km.2 * ψ : ℝ) : ℂ) * I)

/-- The Fourier series `∑ u_{k,m} e^{i(kθ + mψ)}`. -/
def fourierSum (u : ℤ × ℤ → ℂ) (θ ψ : ℝ) : ℂ := ∑' km, u km * fourierMode km θ ψ

/-- Fourier modes are unimodular. -/
theorem norm_fourierMode (km : ℤ × ℤ) (θ ψ : ℝ) : ‖fourierMode km θ ψ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- `ψ`-derivative of a mode. -/
theorem hasDerivAt_fourierMode_ψ (km : ℤ × ℤ) (θ ψ : ℝ) :
    HasDerivAt (fun ψ' => fourierMode km θ ψ') (I * km.2 * fourierMode km θ ψ) ψ := by
  have h1 : HasDerivAt (fun ψ' : ℝ => (km.1 : ℝ) * θ + km.2 * ψ') (km.2 : ℝ) ψ := by
    simpa using ((hasDerivAt_id ψ).const_mul (km.2 : ℝ)).const_add ((km.1 : ℝ) * θ)
  have h2 : HasDerivAt (fun ψ' => fourierMode km θ ψ')
      (fourierMode km θ ψ * (((km.2 : ℝ) : ℂ) * I)) ψ := (h1.ofReal_comp.mul_const I).cexp
  convert h2 using 1
  push_cast; ring

/-- `θ`-derivative of a mode. -/
theorem hasDerivAt_fourierMode_θ (km : ℤ × ℤ) (θ ψ : ℝ) :
    HasDerivAt (fun θ' => fourierMode km θ' ψ) (I * km.1 * fourierMode km θ ψ) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => (km.1 : ℝ) * θ' + km.2 * ψ) (km.1 : ℝ) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (km.1 : ℝ)).add_const ((km.2 : ℝ) * ψ)
  have h2 : HasDerivAt (fun θ' => fourierMode km θ' ψ)
      (fourierMode km θ ψ * (((km.1 : ℝ) : ℂ) * I)) θ := (h1.ofReal_comp.mul_const I).cexp
  convert h2 using 1
  push_cast; ring

/-- An element of `ℓ¹_r`, `r ≥ 0`, is absolutely summable. -/
theorem summable_norm_of_inWeighted {r : ℝ} (hr : 0 ≤ r) {u : ℤ × ℤ → ℂ}
    (hu : InWeighted r u) : Summable fun km => ‖u km‖ :=
  hu.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun km => le_mul_of_one_le_right (norm_nonneg _) (one_le_weight hr km))

/-- Termwise differentiation in `ψ`: if `u` and `∂_ψ u` are absolutely summable, the Fourier
series is differentiable in `ψ` with derivative the series of `∂_ψ u`. -/
theorem hasDerivAt_fourierSum_ψ {u : ℤ × ℤ → ℂ} (hu : Summable fun km => ‖u km‖)
    (hdu : Summable fun km => ‖dψ u km‖) (θ ψ : ℝ) :
    HasDerivAt (fun ψ' => fourierSum u θ ψ') (fourierSum (dψ u) θ ψ) ψ := by
  have := hasDerivAt_tsum (𝕜 := ℝ) (F := ℂ) (g := fun km ψ' => u km * fourierMode km θ ψ')
    (g' := fun km ψ' => dψ u km * fourierMode km θ ψ') (y₀ := ψ) hdu
    (fun km y => by
      have := (hasDerivAt_fourierMode_ψ km θ y).const_mul (u km)
      convert this using 1; simp only [dψ]; ring)
    (fun km y => by rw [norm_mul, norm_fourierMode, mul_one])
    (Summable.of_norm (by simpa [norm_mul, norm_fourierMode] using hu)) ψ
  exact this

/-- Termwise differentiation in `θ`. -/
theorem hasDerivAt_fourierSum_θ {u : ℤ × ℤ → ℂ} (hu : Summable fun km => ‖u km‖)
    (hdu : Summable fun km => ‖dθ u km‖) (θ ψ : ℝ) :
    HasDerivAt (fun θ' => fourierSum u θ' ψ) (fourierSum (dθ u) θ ψ) θ := by
  have := hasDerivAt_tsum (𝕜 := ℝ) (F := ℂ) (g := fun km θ' => u km * fourierMode km θ' ψ)
    (g' := fun km θ' => dθ u km * fourierMode km θ' ψ) (y₀ := θ) hdu
    (fun km y => by
      have := (hasDerivAt_fourierMode_θ km y ψ).const_mul (u km)
      convert this using 1; simp only [dθ]; ring)
    (fun km y => by rw [norm_mul, norm_fourierMode, mul_one])
    (Summable.of_norm (by simpa [norm_mul, norm_fourierMode] using hu)) θ
  exact this

/-- **Classical solution of the cohomological equation.** Let `ω` be `(γ, τ)`-Diophantine with
`γ > 0`, `r > 0`, and `f` zero-mean with `‖f‖_r < ∞`. Then the Fourier series `U` of
`u = cohSol ω f` is differentiable in `θ` and in `ψ` at every point, and
`∂_ψ U + ω ∂_θ U = F`, where `F` is the Fourier series of `f`. -/
theorem hasDerivAt_fourierSum_cohSol {ω γ r : ℝ} {τ : ℕ} (hD : Diophantine ω γ τ) (hγ : 0 < γ)
    (hr : 0 < r) {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) (hf0 : f (0, 0) = 0) (θ ψ : ℝ) :
    ∃ Uθ Uψ : ℂ,
      HasDerivAt (fun θ' => fourierSum (cohSol ω f) θ' ψ) Uθ θ ∧
      HasDerivAt (fun ψ' => fourierSum (cohSol ω f) θ ψ') Uψ ψ ∧
      Uψ + (ω : ℂ) * Uθ = fourierSum f θ ψ := by
  set u := cohSol ω f
  have hδ : 0 < r / 2 := by positivity
  obtain ⟨hu, -⟩ := cohSol_estimate hD hγ hδ hf
  have hr2 : r - r / 2 = r / 2 := by ring
  rw [hr2] at hu
  obtain ⟨hθ, -⟩ := dθ_estimate hδ hu
  obtain ⟨hψ, -⟩ := dψ_estimate hδ hu
  rw [sub_self] at hθ hψ
  have hu1 := summable_norm_of_inWeighted hδ.le hu
  have hθ1 := summable_norm_of_inWeighted le_rfl hθ
  have hψ1 := summable_norm_of_inWeighted le_rfl hψ
  refine ⟨_, _, hasDerivAt_fourierSum_θ hu1 hθ1 θ ψ, hasDerivAt_fourierSum_ψ hu1 hψ1 θ ψ, ?_⟩
  have sθ : Summable fun km => dθ u km * fourierMode km θ ψ :=
    Summable.of_norm (by simpa [norm_mul, norm_fourierMode] using hθ1)
  have sψ : Summable fun km => dψ u km * fourierMode km θ ψ :=
    Summable.of_norm (by simpa [norm_mul, norm_fourierMode] using hψ1)
  simp only [fourierSum]
  rw [← tsum_mul_left, ← sψ.tsum_add (sθ.mul_left _)]
  congr 1; funext km
  have := cohSol_spec hD hγ hf0 km
  simp only [cohOp] at this
  rw [← this]; ring

/-! ## Sanity checks -/

/-- Sanity (zero data): the solution of `L_ω u = 0` is `0`. -/
@[simp] theorem cohSol_zero (ω : ℝ) : cohSol ω 0 = 0 := by funext km; simp [cohSol]

/-- Sanity (constant data): a constant (supported on the zero mode) is not in the range of
`L_ω`; `cohSol` discards it and returns `0`. -/
theorem cohSol_const (ω : ℝ) (c : ℂ) :
    cohSol ω (fun km => if km = (0, 0) then c else 0) = 0 := by
  funext km
  by_cases h : km = (0, 0)
  · subst h; simp
  · simp [cohSol, h]

/-- Sanity (one mode): for `f = e^{iψ}` (mode `(0, 1)`), `u = −i e^{iψ}`, i.e. `∂_ψ u = f`. -/
theorem cohSol_single (ω : ℝ) :
    cohSol ω (fun km => if km = (0, 1) then 1 else 0) (0, 1) = -I := by
  simp [cohSol, divisor]

/-- **Counterexample (rational frequency, no solution).** For rational `ω = p/q` the zero-mean
monomial `e^{i(qθ − pψ)}` is in every `ℓ¹_r`, but `L_ω v = f` has no solution: the symbol
vanishes on that mode. -/
theorem no_solution_of_rat (ω : ℚ) :
    ∃ f : ℤ × ℤ → ℂ, f (0, 0) = 0 ∧ (∀ r, InWeighted r f) ∧
      ∀ v : ℤ × ℤ → ℂ, ¬ ∀ km, cohOp (ω : ℝ) v km = f km := by
  set km₀ : ℤ × ℤ := ((ω.den : ℤ), -ω.num)
  have hne : km₀ ≠ (0, 0) := by
    intro h
    have : (ω.den : ℤ) = 0 := congrArg Prod.fst h
    exact ω.den_nz (by exact_mod_cast this)
  refine ⟨fun km => if km = km₀ then 1 else 0, by simp [Ne.symm hne], fun r => ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := {km₀})
    intro km hkm
    simp only [Finset.mem_singleton] at hkm
    simp [hkm]
  · intro v hv
    have := hv km₀
    rw [cohOp_eq] at this
    have hd : divisor (ω : ℝ) km₀ = 0 := by
      simp only [divisor, km₀]
      push_cast
      rw [Rat.cast_def]
      field_simp
      ring
    simp [hd] at this

/-- **Necessity of a small-divisor lower bound.** If every single-mode zero-mean `f` admits a
solution `v` of `L_ω v = f` with `‖v‖_{r−δ} ≤ C ‖f‖_r`, then
`|m + kω| ≥ e^{−δ(|k|+|m|)} / C` on every nonzero mode. (So an estimate of the form of
`cohSol_estimate` forces a Diophantine-type condition.) -/
theorem divisor_lower_of_estimate {ω r δ C : ℝ}
    (hest : ∀ f : ℤ × ℤ → ℂ, f (0, 0) = 0 → InWeighted r f →
      ∃ v, InWeighted (r - δ) v ∧ (∀ km, cohOp ω v km = f km) ∧
        wnorm (r - δ) v ≤ C * wnorm r f)
    {km : ℤ × ℤ} (hkm : km ≠ (0, 0)) :
    Real.exp (-δ * modeSize km) ≤ C * |divisor ω km| := by
  set f : ℤ × ℤ → ℂ := fun j => if j = km then 1 else 0
  have hfin : ∀ j ∉ ({km} : Finset (ℤ × ℤ)), ‖f j‖ * weight r j = 0 := by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [f, hj]
  have hf : InWeighted r f := summable_of_ne_finset_zero hfin
  have hnf : wnorm r f = weight r km := by
    unfold wnorm
    rw [tsum_eq_sum hfin]
    simp [f]
  obtain ⟨v, hv, hsol, hle⟩ := hest f (by simp [f, Ne.symm hkm]) hf
  have h1 := hsol km
  rw [cohOp_eq] at h1
  simp only [f, ↓reduceIte] at h1
  -- `|d| |v_km| = 1`
  have hdv : |divisor ω km| * ‖v km‖ = 1 := by
    have := congrArg norm h1
    simpa [Complex.norm_real, mul_assoc] using this
  have hterm := norm_mul_weight_le_wnorm hv km
  rw [hnf] at hle
  have hw := weight_pos r km
  rw [weight_sub] at hterm
  -- multiply `‖v‖ w e^{−δs} ≤ C w` by `|d|`
  have hd0 : 0 ≤ |divisor ω km| := abs_nonneg _
  have := mul_le_mul_of_nonneg_left (hterm.trans hle) hd0
  have e : |divisor ω km| * (‖v km‖ * (weight r km * Real.exp (-δ * modeSize km))) =
      weight r km * Real.exp (-δ * modeSize km) := by
    rw [← mul_assoc, hdv, one_mul]
  rw [e] at this
  have : weight r km * Real.exp (-δ * modeSize km) ≤ weight r km * (C * |divisor ω km|) := by
    linarith
  exact le_of_mul_le_mul_left this hw

/-- **The estimate fails without the Diophantine hypothesis:** for rational `ω` no constant `C`
gives solutions with `‖v‖_{r−δ} ≤ C ‖f‖_r` for all zero-mean `f ∈ ℓ¹_r`. -/
theorem not_estimate_of_rat (ω : ℚ) (r δ C : ℝ) :
    ¬ ∀ f : ℤ × ℤ → ℂ, f (0, 0) = 0 → InWeighted r f →
      ∃ v, InWeighted (r - δ) v ∧ (∀ km, cohOp (ω : ℝ) v km = f km) ∧
        wnorm (r - δ) v ≤ C * wnorm r f := by
  intro hest
  set km₀ : ℤ × ℤ := ((ω.den : ℤ), -ω.num)
  have hne : km₀ ≠ (0, 0) := by
    intro h
    have : (ω.den : ℤ) = 0 := congrArg Prod.fst h
    exact ω.den_nz (by exact_mod_cast this)
  have h := divisor_lower_of_estimate hest hne
  have hd : divisor (ω : ℝ) km₀ = 0 := by
    simp only [divisor, km₀]
    push_cast
    rw [Rat.cast_def]
    field_simp
    ring
  rw [hd, abs_zero, mul_zero] at h
  exact absurd h (not_le.2 (Real.exp_pos _))

end LeanTheory.Theory.KAM
