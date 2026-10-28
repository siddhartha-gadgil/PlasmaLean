/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.StripAlgebra
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Evaluation of the strip algebra: functions on the torus (KAM route, K3d)

An element `x` of `𝔸 = ℓ¹(ℤ²)` (`Theory/KAM/StripAlgebra`) represents the continuous function
`F_x(θ, ψ) = ∑ x_{k,m} e^{i(kθ + mψ)}` (`WEll1Z2.eval`). This file records that `x ↦ F_x` is an
**injective** ring homomorphism into functions, compatible with the multipliers and with
conjugation:

* `eval_add'`, `eval_mul` (from `WEll1Z2`), `eval_algebraMap`, `eval_inverse`, …;
* **uniqueness of Fourier coefficients** (`coeff_eq_integral`, `ext_eval`): the coefficients are
  recovered by `x_{k,m} = (4π²)⁻¹ ∫₀^{2π} ∫₀^{2π} F_x(θ, ψ) e^{−i(kθ + mψ)} dθ dψ`, so two elements
  with the same function are equal. Identities between elements of `𝔸` can therefore be checked
  pointwise;
* `eval_cj`: conjugation is complex conjugation of the function, so `x` is real
  (`IsReal`) iff `F_x` is real-valued (`isReal_iff_eval`);
* `hasDerivAt_eval_θ`, `hasDerivAt_eval_ψ`: for analytic `x`, `F_x` is differentiable with
  `∂_θ F_x = F_{dS 1 0 x}` and `∂_ψ F_x = F_{dS 0 1 x}` (termwise differentiation).

**Sanity.** `eval_one`, `eval_mode` (a mode is the exponential), `avg_eq_integral` (the average
is the mean value).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

open Complex WEll1Z2 MeasureTheory intervalIntegral

/-! ## Algebraic properties of evaluation -/

/-- The Fourier series of an absolutely summable family converges. -/
theorem summable_fourier {f : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖) (θ ψ : ℝ) :
    Summable fun n => f n * fourierMode n θ ψ :=
  Summable.of_norm (by simpa [norm_mul, norm_fourierMode] using hf)

/-- The function of a sum. -/
theorem eval_add' (x y : FA) (θ ψ : ℝ) : eval (x + y) θ ψ = eval x θ ψ + eval y θ ψ := by
  simp only [eval, fourierSum, coeff_add', Pi.add_apply, add_mul]
  exact (summable_fourier (summable_norm_coeff le_rfl x) θ ψ).tsum_add
    (summable_fourier (summable_norm_coeff le_rfl y) θ ψ)

/-- The function of a scalar multiple. -/
theorem eval_smul' (c : ℂ) (x : FA) (θ ψ : ℝ) : eval (c • x) θ ψ = c * eval x θ ψ := by
  simp only [eval, fourierSum, coeff_smul, mul_assoc]
  exact tsum_mul_left

/-- The function of a negation. -/
theorem eval_neg' (x : FA) (θ ψ : ℝ) : eval (-x) θ ψ = -eval x θ ψ := by
  have := eval_smul' (-1) x θ ψ; simpa using this

/-- The function of a difference. -/
theorem eval_sub' (x y : FA) (θ ψ : ℝ) : eval (x - y) θ ψ = eval x θ ψ - eval y θ ψ := by
  rw [sub_eq_add_neg, eval_add', eval_neg', ← sub_eq_add_neg]

/-- The function of `0`. -/
@[simp] theorem eval_zero' (θ ψ : ℝ) : eval (0 : FA) θ ψ = 0 := by
  simp [eval, fourierSum]

/-- The function of a constant. -/
theorem eval_algebraMap (c : ℂ) (θ ψ : ℝ) : eval (algebraMap ℂ FA c) θ ψ = c := by
  rw [Algebra.algebraMap_eq_smul_one, eval_smul', eval_one, mul_one]

/-- Evaluation as a ring homomorphism `𝔸 → ℂ` at a point. -/
def evalHom (θ ψ : ℝ) : FA →+* ℂ where
  toFun x := eval x θ ψ
  map_one' := eval_one θ ψ
  map_mul' x y := eval_mul x y θ ψ
  map_zero' := by simp [eval, fourierSum]
  map_add' x y := eval_add' x y θ ψ

/-- The function of a numeral. -/
@[simp] theorem eval_ofNat' (n : ℕ) [n.AtLeastTwo] (θ ψ : ℝ) :
    eval (no_index (OfNat.ofNat n : FA)) θ ψ = OfNat.ofNat n :=
  map_ofNat (evalHom θ ψ) n

/-- The function of an inverse. -/
theorem eval_inverse {x : FA} (hx : IsUnit x) (θ ψ : ℝ) :
    eval (Ring.inverse x) θ ψ = (eval x θ ψ)⁻¹ := by
  have := map_ringInverse (evalHom θ ψ) hx
  simpa [evalHom, Ring.inverse_eq_inv'] using this

/-- The function of a power. -/
theorem eval_pow' (x : FA) (n : ℕ) (θ ψ : ℝ) : eval (x ^ n) θ ψ = eval x θ ψ ^ n :=
  map_pow (evalHom θ ψ) x n

/-- Evaluation of polynomial expressions. -/
theorem eval_polyExpr {σ : Type*} (z : σ → FA) (θ ψ : ℝ) :
    ∀ e : PolyExpr ℂ σ, eval (PolyExpr.eval z e) θ ψ =
      PolyExpr.eval (A := ℂ) (fun i => eval (z i) θ ψ) e
  | .const c => by simp [PolyExpr.eval, eval_algebraMap]
  | .var i => rfl
  | .add p q => by
    simp only [PolyExpr.eval, eval_add', eval_polyExpr z θ ψ p, eval_polyExpr z θ ψ q]
  | .sub p q => by
    simp only [PolyExpr.eval, eval_sub', eval_polyExpr z θ ψ p, eval_polyExpr z θ ψ q]
  | .mul p q => by
    simp only [PolyExpr.eval, eval_mul, eval_polyExpr z θ ψ p, eval_polyExpr z θ ψ q]

/-! ## Uniqueness of Fourier coefficients -/

/-- `∫₀^{2π} e^{ijt} dt = 2π [j = 0]`. -/
theorem integral_exp_int (j : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (((j * t : ℝ) : ℂ) * I) =
      if j = 0 then 2 * Real.pi else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (j : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast h) I_ne_zero
    have e : (fun t : ℝ => Complex.exp (((j * t : ℝ) : ℂ) * I)) =
        fun t : ℝ => Complex.exp ((j : ℂ) * I * t) := by
      funext t; congr 1; push_cast; ring
    have h1 : Complex.exp ((j : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (j : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ) = (j : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I j
    rw [e, integral_exp_mul_complex hc, h1]
    simp

/-- Termwise integration of an absolutely summable series of unimodular-bounded continuous
functions over `[0, 2π]`. -/
theorem integral_tsum_of_bounded {g : ℤ × ℤ → ℂ} (hg : Summable fun n => ‖g n‖)
    {φ : ℤ × ℤ → ℝ → ℂ} (hφc : ∀ n, Continuous (φ n)) {C : ℝ}
    (hφb : ∀ n t, ‖φ n t‖ ≤ C) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n, g n * φ n t =
      ∑' n, g n * ∫ t in (0 : ℝ)..(2 * Real.pi), φ n t := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hφb 0 0)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * Real.pi) (F := fun n t => g n * φ n t)
    (f := fun t => ∑' n, g n * φ n t) (fun n _ => ‖g n‖ * C)
    (fun n => ((continuous_const.mul (hφc n)).aestronglyMeasurable))
    (fun n => ae_of_all _ fun t _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hφb n t) (norm_nonneg _))
    (ae_of_all _ fun t _ => hg.mul_right C)
    intervalIntegrable_const
    (ae_of_all _ fun t _ => (Summable.of_norm_bounded (hg.mul_right C) fun n => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hφb n t) (norm_nonneg _)).hasSum)
  rw [← h.tsum_eq]
  refine tsum_congr fun n => ?_
  exact intervalIntegral.integral_const_mul _ _

/-- The inner integral of a mode against `e^{−ikθ}`. -/
theorem integral_mode_θ (n : ℤ × ℤ) (k : ℤ) (ψ : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), fourierMode n θ ψ * Complex.exp (((-k * θ : ℝ) : ℂ) * I) =
      if n.1 = k then ((2 * Real.pi : ℝ) : ℂ) * Complex.exp (((n.2 * ψ : ℝ) : ℂ) * I) else 0 := by
  have e : (fun θ : ℝ => fourierMode n θ ψ * Complex.exp (((-k * θ : ℝ) : ℂ) * I)) =
      fun θ : ℝ => Complex.exp (((n.2 * ψ : ℝ) : ℂ) * I) *
        Complex.exp ((((n.1 - k : ℤ) * θ : ℝ) : ℂ) * I) := by
    funext θ
    simp only [fourierMode, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [e, intervalIntegral.integral_const_mul, integral_exp_int]
  by_cases h : n.1 = k
  · simp [h]; ring
  · have : n.1 - k ≠ 0 := sub_ne_zero.2 h
    simp [h, this]

/-- **Fourier coefficients from the function**:
`x_{k,m} = (4π²)⁻¹ ∫₀^{2π} ∫₀^{2π} F_x(θ, ψ) e^{−ikθ} e^{−imψ} dθ dψ`. -/
theorem coeff_eq_integral (x : FA) (k m : ℤ) :
    coeff x (k, m) = ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ *
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), (∫ θ in (0 : ℝ)..(2 * Real.pi),
        eval x θ ψ * Complex.exp (((-k * θ : ℝ) : ℂ) * I)) *
          Complex.exp (((-m * ψ : ℝ) : ℂ) * I) := by
  have hs := summable_norm_coeff le_rfl x
  have hmc : ∀ n : ℤ × ℤ, ∀ ψ : ℝ, Continuous fun θ =>
      fourierMode n θ ψ * Complex.exp (((-k * θ : ℝ) : ℂ) * I) := fun n ψ => by
    unfold fourierMode; fun_prop
  have hinner : ∀ ψ, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      eval x θ ψ * Complex.exp (((-k * θ : ℝ) : ℂ) * I) =
      ∑' n, coeff x n * (if n.1 = k then ((2 * Real.pi : ℝ) : ℂ) *
        Complex.exp (((n.2 * ψ : ℝ) : ℂ) * I) else 0) := by
    intro ψ
    simp only [eval, fourierSum]
    have e : ∀ θ, (∑' n, coeff x n * fourierMode n θ ψ) *
        Complex.exp (((-k * θ : ℝ) : ℂ) * I) =
        ∑' n, coeff x n * (fourierMode n θ ψ * Complex.exp (((-k * θ : ℝ) : ℂ) * I)) := by
      intro θ; rw [← tsum_mul_right]; simp only [mul_assoc]
    simp_rw [e]
    rw [integral_tsum_of_bounded hs (fun n => hmc n ψ) (C := 1) (fun n t => by
      rw [norm_mul, norm_fourierMode, Complex.norm_exp_ofReal_mul_I, one_mul])]
    simp_rw [integral_mode_θ]
  simp_rw [hinner]
  have e2 : ∀ ψ, (∑' n, coeff x n * (if n.1 = k then ((2 * Real.pi : ℝ) : ℂ) *
        Complex.exp (((n.2 * ψ : ℝ) : ℂ) * I) else 0)) *
        Complex.exp (((-m * ψ : ℝ) : ℂ) * I) =
      ∑' n, coeff x n * ((if n.1 = k then ((2 * Real.pi : ℝ) : ℂ) *
        Complex.exp (((n.2 * ψ : ℝ) : ℂ) * I) else 0) *
          Complex.exp (((-m * ψ : ℝ) : ℂ) * I)) := by
    intro ψ; rw [← tsum_mul_right]; simp only [mul_assoc]
  simp_rw [e2]
  rw [integral_tsum_of_bounded hs (C := 2 * Real.pi)
    (fun n => by split_ifs <;> fun_prop)
    (fun n t => by
      split_ifs
      · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        simp
      · simp [Real.pi_pos.le])]
  have hterm : ∀ n : ℤ × ℤ, coeff x n * ∫ ψ in (0 : ℝ)..(2 * Real.pi),
      (if n.1 = k then ((2 * Real.pi : ℝ) : ℂ) * Complex.exp (((n.2 * ψ : ℝ) : ℂ) * I) else 0) *
        Complex.exp (((-m * ψ : ℝ) : ℂ) * I) =
      if n = (k, m) then coeff x n * ((4 * Real.pi ^ 2 : ℝ) : ℂ) else 0 := by
    intro n
    by_cases h1 : n.1 = k
    · have e3 : (fun ψ : ℝ => (if n.1 = k then ((2 * Real.pi : ℝ) : ℂ) *
          Complex.exp (((n.2 * ψ : ℝ) : ℂ) * I) else 0) *
          Complex.exp (((-m * ψ : ℝ) : ℂ) * I)) =
          fun ψ : ℝ => ((2 * Real.pi : ℝ) : ℂ) *
            Complex.exp ((((n.2 - m : ℤ) * ψ : ℝ) : ℂ) * I) := by
        funext ψ
        simp only [h1, ↓reduceIte]
        rw [mul_assoc, ← Complex.exp_add]
        congr 2; push_cast; ring
      rw [e3, intervalIntegral.integral_const_mul, integral_exp_int]
      by_cases h2 : n.2 = m
      · have hn : n = (k, m) := Prod.ext h1 h2
        simp only [hn, sub_self, ite_true]
        push_cast; ring
      · have hn : n ≠ (k, m) := fun h => h2 (by rw [h])
        have : n.2 - m ≠ 0 := sub_ne_zero.2 h2
        simp [hn, this]
    · have hn : n ≠ (k, m) := fun h => h1 (by rw [h])
      simp [h1, hn]
  simp_rw [hterm]
  rw [tsum_ite_eq]
  have : ((4 * Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (4 * Real.pi ^ 2) ≠ 0)
  field_simp

/-- **Uniqueness of Fourier coefficients**: elements with the same function are equal. -/
theorem ext_eval {x y : FA} (h : ∀ θ ψ, eval x θ ψ = eval y θ ψ) : x = y :=
  ext_coeff fun n => by
    obtain ⟨k, m⟩ := n
    rw [coeff_eq_integral x, coeff_eq_integral y]
    simp_rw [h]

/-- The average is the mean value over the torus. -/
theorem avg_eq_integral (x : FA) :
    avg x = ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ *
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi), eval x θ ψ := by
  have := coeff_eq_integral x 0 0
  unfold avg; simpa using this

/-! ## Conjugation and reality -/

/-- Conjugation is complex conjugation of the function. -/
theorem eval_cj (x : FA) (θ ψ : ℝ) : eval (cj x) θ ψ = (starRingEnd ℂ) (eval x θ ψ) := by
  simp only [eval, fourierSum, coeff_cj, Complex.conj_tsum, map_mul]
  rw [← (Equiv.neg (ℤ × ℤ)).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, neg_neg, fourierMode, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg, Prod.snd_neg,
    Int.cast_neg]
  push_cast; ring

/-- **Reality** is real-valuedness of the function. -/
theorem isReal_iff_eval (x : FA) : IsReal x ↔ ∀ θ ψ, (starRingEnd ℂ) (eval x θ ψ) = eval x θ ψ := by
  constructor
  · intro h θ ψ; rw [← eval_cj, h]
  · intro h; exact ext_eval fun θ ψ => by rw [eval_cj, h]

/-- A real element has real values. -/
theorem IsReal.eval_im {x : FA} (h : IsReal x) (θ ψ : ℝ) : (WEll1Z2.eval x θ ψ).im = 0 := by
  have := (isReal_iff_eval x).1 h θ ψ
  have h2 := congrArg Complex.im this
  simp at h2; linarith

/-! ## Derivatives -/

/-- `∂_θ F_x = F_{dS 1 0 x}` for analytic `x`. -/
theorem hasDerivAt_eval_θ {x : FA} (hx : Ana x) (θ ψ : ℝ) :
    HasDerivAt (fun θ' => eval x θ' ψ) (eval (dS 1 0 x) θ ψ) θ := by
  have h1 : coeff (dS 1 0 x) = dθ (coeff x) := by
    rw [hx.coeff_dS]; funext n; simp [dsym, dθ]
  rw [eval, h1]
  exact hasDerivAt_fourierSum_θ hx.summable (by rw [← h1]; exact (hx.d 1 0).summable) θ ψ

/-- `∂_ψ F_x = F_{dS 0 1 x}` for analytic `x`. -/
theorem hasDerivAt_eval_ψ {x : FA} (hx : Ana x) (θ ψ : ℝ) :
    HasDerivAt (fun ψ' => eval x θ ψ') (eval (dS 0 1 x) θ ψ) ψ := by
  have h1 : coeff (dS 0 1 x) = dψ (coeff x) := by
    rw [hx.coeff_dS]; funext n; simp [dsym, dψ]
  rw [eval, h1]
  exact hasDerivAt_fourierSum_ψ hx.summable (by rw [← h1]; exact (hx.d 0 1).summable) θ ψ

/-- Sanity: a mode evaluates to the exponential. -/
theorem eval_mode (km : ℤ × ℤ) (θ ψ : ℝ) : eval (mode 0 km) θ ψ = fourierMode km θ ψ := by
  simp only [eval, fourierSum, coeff_mode]
  rw [tsum_eq_single km (fun n hn => by simp [hn])]
  simp

end LeanTheory.Theory.KAM
