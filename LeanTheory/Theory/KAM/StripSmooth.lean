/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.StripEval
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic elements are smooth functions on the torus (KAM route, K3 lemma 9, regularity)

For an analytic element `x` of the strip algebra (`Ana x`: a bound on a strip of positive width),
the function `F_x(θ, ψ) = ∑ x_{k,m} e^{i(kθ + mψ)}` on `ℝ²` is Fréchet differentiable with
derivative `(v₁, v₂) ↦ v₁ F_{∂_θ x} + v₂ F_{∂_ψ x}` (`hasFDerivAt_evalP`, termwise
differentiation, `hasFDerivAt_tsum`), and therefore `C^n` for every `n` (`contDiff_evalP`), since
`∂_θ x`, `∂_ψ x` are again analytic. It is `2π`-periodic in both angles (`evalP_periodic_θ`,
`evalP_periodic_ψ`).

**Sanity.** `evalP_one`: the unit is the constant function `1`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

open Complex WEll1Z2

/-- The function of `x` on `ℝ²`. -/
def evalP (x : FA) (p : ℝ × ℝ) : ℂ := eval x p.1 p.2

/-- The linear form `(v₁, v₂) ↦ i (k v₁ + m v₂)` of mode `n = (k, m)`. -/
def modeL (n : ℤ × ℤ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (I * n.1) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (I * n.2)

/-- `modeL n p = i (k θ + m ψ)`. -/
theorem modeL_apply (n : ℤ × ℤ) (p : ℝ × ℝ) :
    modeL n p = ((n.1 * p.1 + n.2 * p.2 : ℝ) : ℂ) * I := by
  rw [show modeL n p = p.1 • (I * n.1) + p.2 • (I * n.2) from rfl, Complex.real_smul,
    Complex.real_smul]
  push_cast; ring

/-- `‖modeL n‖ ≤ |k| + |m|`. -/
theorem norm_modeL_le (n : ℤ × ℤ) : ‖modeL n‖ ≤ modeSize n := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by unfold modeSize; positivity) fun v => ?_
  rw [modeL_apply, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |(v.1 : ℝ)| ≤ ‖v‖ := norm_fst_le v
  have h2 : |(v.2 : ℝ)| ≤ ‖v‖ := norm_snd_le v
  calc |(n.1 : ℝ) * v.1 + n.2 * v.2| ≤ |(n.1 : ℝ)| * |v.1| + |(n.2 : ℝ)| * |v.2| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |(n.1 : ℝ)| * ‖v‖ + |(n.2 : ℝ)| * ‖v‖ := by gcongr
    _ = modeSize n * ‖v‖ := by unfold modeSize; ring

/-- A mode is the exponential of its linear form. -/
theorem fourierMode_eq (n : ℤ × ℤ) (p : ℝ × ℝ) :
    fourierMode n p.1 p.2 = Complex.exp (modeL n p) := by
  rw [modeL_apply, fourierMode]

/-- The derivative of `F_x`: `(v₁, v₂) ↦ v₁ F_{∂_θ x} + v₂ F_{∂_ψ x}`. -/
def derivP (x : FA) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (eval (dS 1 0 x) p.1 p.2) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (eval (dS 0 1 x) p.1 p.2)

/-- Analytic elements have `‖x_n‖ (|k| + |m|)` summable. -/
theorem Ana.summable_modeSize {x : FA} (hx : Ana x) :
    Summable fun n => ‖coeff x n‖ * modeSize n := by
  obtain ⟨ρ, B, hρ, h⟩ := hx
  refine (h.1.mul_left (1 / (Real.exp 1 * ρ))).of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (modeSize_nonneg n)) fun n => ?_
  have hsup := pow_mul_exp_neg_le (modeSize_nonneg n) hρ 1
  simp only [pow_one, Nat.cast_one] at hsup
  have hw : weight ρ n * Real.exp (-ρ * modeSize n) = 1 := by
    rw [weight, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc ‖coeff x n‖ * modeSize n
      = ‖coeff x n‖ * modeSize n * (weight ρ n * Real.exp (-ρ * modeSize n)) := by
        rw [hw, mul_one]
    _ = ‖coeff x n‖ * weight ρ n * (modeSize n * Real.exp (-ρ * modeSize n)) := by ring
    _ ≤ ‖coeff x n‖ * weight ρ n * (1 / (Real.exp 1 * ρ)) := by
        gcongr; exact mul_nonneg (norm_nonneg _) (weight_pos ρ n).le
    _ = _ := by ring

/-- **`F_x` is Fréchet differentiable** for analytic `x`. -/
theorem hasFDerivAt_evalP {x : FA} (hx : Ana x) (p : ℝ × ℝ) :
    HasFDerivAt (evalP x) (derivP x p) p := by
  set g : ℤ × ℤ → ℝ × ℝ → ℂ := fun n q => coeff x n * Complex.exp (modeL n q) with hg
  set g' : ℤ × ℤ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ) :=
    fun n q => (coeff x n * Complex.exp (modeL n q)) • modeL n with hg'
  have hd : ∀ n q, HasFDerivAt (g n) (g' n q) q := fun n q => by
    have := ((modeL n).hasFDerivAt (x := q)).cexp.const_mul (coeff x n)
    simpa [hg, hg', smul_smul] using this
  have hb : ∀ n q, ‖g' n q‖ ≤ ‖coeff x n‖ * modeSize n := fun n q => by
    rw [hg', norm_smul, norm_mul, Complex.norm_exp, modeL_apply]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, Real.exp_zero]
    exact mul_le_mul_of_nonneg_left (norm_modeL_le n) (norm_nonneg _)
  have hs0 : Summable fun n => g n p := by
    have := summable_fourier hx.summable p.1 p.2
    simpa [hg, fourierMode_eq] using this
  have h := hasFDerivAt_tsum hx.summable_modeSize hd hb hs0 p
  have e1 : (fun y => ∑' n, g n y) = evalP x := by
    funext y; simp [hg, evalP, eval, fourierSum, fourierMode_eq]
  rw [e1] at h
  have hsum : Summable fun n => g' n p :=
    (hx.summable_modeSize).of_norm_bounded fun n => hb n p
  suffices hE : derivP x p = ∑' n, g' n p by rw [hE]; exact h
  refine ContinuousLinearMap.ext fun v => ?_
  rw [show (∑' n, g' n p) v = (ContinuousLinearMap.apply ℝ ℂ v) (∑' n, g' n p) from rfl,
    (ContinuousLinearMap.apply ℝ ℂ v).map_tsum hsum]
  rw [show derivP x p v = v.1 • eval (dS 1 0 x) p.1 p.2 + v.2 • eval (dS 0 1 x) p.1 p.2 from rfl]
  simp only [ContinuousLinearMap.apply_apply, hg']
  rw [eval, eval, hx.coeff_dS 1 0, hx.coeff_dS 0 1, Complex.real_smul, Complex.real_smul]
  simp only [fourierSum]
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_fourier ((inWeighted_zero_iff _).1 (hx.inW_dsym 1 0)) p.1 p.2).mul_left
      (v.1 : ℂ)).tsum_add ((summable_fourier ((inWeighted_zero_iff _).1 (hx.inW_dsym 0 1))
      p.1 p.2).mul_left (v.2 : ℂ))]
  refine tsum_congr fun n => ?_
  rw [show ((coeff x n * Complex.exp (modeL n p)) • modeL n) v =
    (coeff x n * Complex.exp (modeL n p)) * modeL n v from rfl, modeL_apply n v,
    fourierMode_eq]
  simp only [dsym]
  push_cast; ring

/-- `F_x` is continuous for analytic `x`. -/
theorem continuous_evalP {x : FA} (hx : Ana x) : Continuous (evalP x) :=
  continuous_iff_continuousAt.2 fun p => (hasFDerivAt_evalP hx p).continuousAt

/-- **Regularity: `F_x` is `C^n` for every `n`** (analytic `x`). -/
theorem contDiff_evalP : ∀ (n : ℕ) {x : FA}, Ana x → ContDiff ℝ n (evalP x)
  | 0, x, hx => contDiff_zero.2 (continuous_evalP hx)
  | n + 1, x, hx => by
    have hfd : fderiv ℝ (evalP x) = derivP x := funext fun p => (hasFDerivAt_evalP hx p).fderiv
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_evalP hx p).differentiableAt, fun h => by simp at h, ?_⟩
    rw [hfd]
    have e : derivP x = fun p =>
        ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.fst ℝ ℝ ℝ)
            (evalP (dS 1 0 x) p) +
          ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.snd ℝ ℝ ℝ)
            (evalP (dS 0 1 x) p) := by
      funext p; rfl
    rw [e]
    exact ((ContinuousLinearMap.contDiff _).comp (contDiff_evalP n (hx.d 1 0))).add
      ((ContinuousLinearMap.contDiff _).comp (contDiff_evalP n (hx.d 0 1)))

/-- `F_x` is `2π`-periodic in `θ`. -/
theorem eval_periodic_θ (x : FA) (θ ψ : ℝ) : eval x (θ + 2 * Real.pi) ψ = eval x θ ψ := by
  simp only [eval, fourierSum]
  refine tsum_congr fun n => ?_
  congr 1
  rw [fourierMode, fourierMode]
  have : ((n.1 * (θ + 2 * Real.pi) + n.2 * ψ : ℝ) : ℂ) * I =
      ((n.1 * θ + n.2 * ψ : ℝ) : ℂ) * I + (n.1 : ℤ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `F_x` is `2π`-periodic in `ψ`. -/
theorem eval_periodic_ψ (x : FA) (θ ψ : ℝ) : eval x θ (ψ + 2 * Real.pi) = eval x θ ψ := by
  simp only [eval, fourierSum]
  refine tsum_congr fun n => ?_
  congr 1
  rw [fourierMode, fourierMode]
  have : ((n.1 * θ + n.2 * (ψ + 2 * Real.pi) : ℝ) : ℂ) * I =
      ((n.1 * θ + n.2 * ψ : ℝ) : ℂ) * I + (n.2 : ℤ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Sanity: the unit is the constant function `1`. -/
theorem evalP_one (p : ℝ × ℝ) : evalP 1 p = 1 := eval_one p.1 p.2

end LeanTheory.Theory.KAM
