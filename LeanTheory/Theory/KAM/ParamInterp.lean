/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.PolyExprS
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Interpolation in a parameter with an analytic remainder bound

A certified torus at finitely many values `x₀, …, x_{m−1}` of a parameter (for example a
coefficient `ρ` of the field) gives a certified torus for **every** parameter value in between,
if the quantity of interest is complex analytic in the parameter. This file provides the three
ingredients:

* `hasFDerivAt_invSqrt`: the inverse square root `a ↦ a^{−1/2}` of `Theory/KAM/InvSqrt` is
  Fréchet differentiable (with derivative `v ↦ −½ (a^{−1/2})³ v`) on `‖a − c‖ < c`, in every
  complete normed commutative `ℂ`-algebra; this follows from the second-order bound
  `norm_invSqrt_taylor_le`;
* `PolyExprS.differentiableAt_eval`: the evaluation `t ↦ P(x(t))` of a polynomial expression with
  inverse-square-root nodes is complex differentiable in a parameter `t ∈ ℂ` wherever the inputs
  are differentiable and the expression is valid at bounds of the inputs (`Valid a P`);
* `norm_sub_interp_le` (**interpolation with an analytic remainder**): if `f : ℂ → E` is complex
  differentiable on the closed disc `|t| ≤ R` with `‖f‖ ≤ M` on the circle, and weights `w_j`
  reproduce the monomials of degree `< m` at the nodes (`∑ⱼ wⱼ x_jⁿ = hⁿ`), then for
  `|h|, |x_j| ≤ ρ < R` and `∑ⱼ |wⱼ| ≤ Λ`:
  `‖f(h) − ∑ⱼ wⱼ f(xⱼ)‖ ≤ (1 + Λ) M q^m/(1 − q)`, `q = ρ/R`.
  The proof expands `f` in its Cauchy power series `∑ aₙ tⁿ` with `‖aₙ‖ ≤ M/Rⁿ`
  (`norm_cauchyPowerSeries_le`); the terms of degree `< m` cancel exactly.

**Sanity.** `interp_exact_const`: a constant function is reproduced exactly (remainder bound
`0` for `M = 0`); `hasFDerivAt_invSqrt_one`: at `a = c = 1` the derivative is `−½ · id`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

open Metric Asymptotics Filter Topology

/-! ## Differentiability of the inverse square root -/

section InvSqrtDiff

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]

/-- The derivative of `a ↦ a^{−1/2}` at `a`: `v ↦ −½ (a^{−1/2})³ v`. -/
def invSqrtD (c : ℝ) (a : A) : A →L[ℂ] A :=
  (-(1 / 2) : ℂ) • ContinuousLinearMap.mul ℂ A (invSqrt ℂ c a ^ 3)

/-- **The inverse square root is differentiable** on `‖a − c‖ < c`, with derivative
`v ↦ −½ (a^{−1/2})³ v`. -/
theorem hasFDerivAt_invSqrt {c : ℝ} {a : A} (h : ‖a - algebraMap ℂ A (c : ℂ)‖ < c) :
    HasFDerivAt (invSqrt ℂ c) (invSqrtD c a) a := by
  set d := ‖a - algebraMap ℂ A (c : ℂ)‖ with hd
  set m := (d + c) / 2 with hm
  have hmc : m < c := by rw [hm]; linarith
  have hdm : d < m := by rw [hm]; linarith
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun v : A => invSqrt ℂ c (a + v) - invSqrt ℂ c a - invSqrtD c a v) =O[𝓝 0]
      (fun v : A => ‖v‖ ^ 2) := by
    refine IsBigO.of_bound (3 * isqG c m ^ 5 / 4 / 2) ?_
    have hball : ball (0 : A) (m - d) ∈ 𝓝 (0 : A) := ball_mem_nhds _ (by linarith)
    filter_upwards [hball] with v hv
    rw [mem_ball, dist_zero_right] at hv
    have hb : ‖a + v - algebraMap ℂ A (c : ℂ)‖ ≤ m := by
      calc ‖a + v - algebraMap ℂ A (c : ℂ)‖ = ‖(a - algebraMap ℂ A (c : ℂ)) + v‖ := by
            congr 1; abel
        _ ≤ d + ‖v‖ := norm_add_le _ _
        _ ≤ m := by linarith
    have ht := norm_invSqrt_taylor_le (𝕜 := ℂ) hdm.le hb hmc
    have e : invSqrt ℂ c (a + v) - invSqrt ℂ c a - invSqrtD c a v =
        invSqrt ℂ c (a + v) - invSqrt ℂ c a - (-(1 / 2) : ℂ) • invSqrt ℂ c a ^ 3 * (a + v - a) := by
      simp [invSqrtD]
    rw [e, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ 3 * isqG c m ^ 5 / 4 * ‖a + v - a‖ ^ 2 / 2 := ht
      _ = 3 * isqG c m ^ 5 / 4 / 2 * ‖v‖ ^ 2 := by rw [add_sub_cancel_left]; ring
  exact hbig.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

/-- **Sanity**: at `a = c = 1` the derivative is `v ↦ −½ v`. -/
theorem hasFDerivAt_invSqrt_one :
    HasFDerivAt (invSqrt ℂ 1) ((-(1 / 2) : ℂ) • ContinuousLinearMap.id ℂ A) (1 : A) := by
  have h : ‖(1 : A) - algebraMap ℂ A ((1 : ℝ) : ℂ)‖ < 1 := by simp
  have h1 := hasFDerivAt_invSqrt h
  have e : invSqrt ℂ 1 (1 : A) = 1 := by
    have := invSqrt_algebraMap (𝕜 := ℂ) (A := A) 1
    simpa using this
  have e2 : invSqrtD 1 (1 : A) = (-(1 / 2) : ℂ) • ContinuousLinearMap.id ℂ A := by
    ext v; simp [invSqrtD, e]
  rwa [e2] at h1

end InvSqrtDiff

/-! ## Polynomial expressions in a complex parameter -/

namespace PolyExprS

variable {σ : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [NormOneClass A]
  [CompleteSpace A]

/-- **Evaluation is complex differentiable in a parameter**: if the inputs `t ↦ x t i` are
differentiable at `t₀` and bounded there by `a`, and `P` is valid at `a`, then `t ↦ P(x t)` is
differentiable at `t₀`. -/
theorem differentiableAt_eval {x : ℂ → σ → A} {t₀ : ℂ}
    (hx : ∀ i, DifferentiableAt ℂ (fun t => x t i) t₀) {a : σ → ℝ} (hb : ∀ i, ‖x t₀ i‖ ≤ a i) :
    ∀ {e : PolyExprS ℂ σ}, Valid a e → DifferentiableAt ℂ (fun t => eval (x t) e) t₀
  | .const c, _ => differentiableAt_const _
  | .var i, _ => hx i
  | .add p q, hv => (differentiableAt_eval hx hb hv.1).add (differentiableAt_eval hx hb hv.2)
  | .sub p q, hv => (differentiableAt_eval hx hb hv.1).sub (differentiableAt_eval hx hb hv.2)
  | .mul p q, hv => (differentiableAt_eval hx hb hv.1).mul (differentiableAt_eval hx hb hv.2)
  | .isqrt c d, hv => by
    have hd := differentiableAt_eval hx hb hv.1
    have hn : ‖algebraMap ℂ A (c : ℂ) + eval (x t₀) d - algebraMap ℂ A (c : ℂ)‖ < c := by
      rw [add_sub_cancel_left]; exact (norm_eval_le hb hv.1).trans_lt hv.2
    exact (hasFDerivAt_invSqrt hn).differentiableAt.comp t₀ ((differentiableAt_const _).add hd)

end PolyExprS

/-! ## Cauchy estimates and interpolation -/

section Interp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Cauchy coefficient bound and expansion**: if `f` is complex differentiable on the closed
disc `|t| ≤ R` and `‖f‖ ≤ M` on the circle, there are coefficients `aₙ` with `‖aₙ‖ ≤ M/Rⁿ` and
`f(t) = ∑ tⁿ aₙ` for `|t| < R`. -/
theorem exists_coeff_bound {f : ℂ → E} {R : NNReal} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (closedBall 0 R)) {M : ℝ}
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) :
    ∃ coef : ℕ → E, (∀ n, ‖coef n‖ ≤ M / (R : ℝ) ^ n) ∧
      ∀ t : ℂ, ‖t‖ < R → HasSum (fun n => t ^ n • coef n) (f t) := by
  have hp := hd.hasFPowerSeriesOnBall hR
  set p := cauchyPowerSeries f 0 R
  refine ⟨fun n => p n (fun _ => 1), fun n => ?_, fun t ht => ?_⟩
  · have h1 : ‖p n (fun _ => (1 : ℂ))‖ ≤ ‖p n‖ := by
      have := (p n).le_opNorm (fun _ => (1 : ℂ))
      simpa only [norm_one, Finset.prod_const_one, mul_one] using this
    refine h1.trans ((norm_cauchyPowerSeries_le f 0 R n).trans ?_)
    have hR' : (0 : ℝ) < R := hR
    have hint : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 R θ)‖) ≤ M * (2 * Real.pi) := by
      have hb : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi), ‖‖f (circleMap 0 R θ)‖‖ ≤ M := by
        intro θ _
        rw [norm_norm]
        exact hM _ (by simp [abs_of_pos hR'])
      have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hb
      rw [sub_zero, abs_of_pos (by positivity)] at h2
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans h2)
    have hpi : 0 < 2 * Real.pi := by positivity
    rw [abs_of_pos hR', inv_pow, div_eq_mul_inv]
    have hM0 : 0 ≤ M := by
      have := hM ((R : ℂ)) (by simp [abs_of_pos hR'])
      exact (norm_nonneg _).trans this
    gcongr
    calc (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 R θ)‖
        ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) := by gcongr
      _ = M := by field_simp
  · have hy : t ∈ Metric.eball (0 : ℂ) R := by
      rw [Metric.mem_eball, edist_zero_right]
      exact_mod_cast ht
    have hs := hp.hasSum hy
    rw [zero_add] at hs
    convert hs using 1
    funext n
    have := (p n).map_smul_univ (fun _ => t) (fun _ => (1 : ℂ))
    simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    rw [this]

/-- **Interpolation with an analytic remainder.** -/
theorem norm_sub_interp_le {f : ℂ → E} {R : NNReal} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (closedBall 0 R)) {M : ℝ}
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) {m : ℕ} (x w : Fin m → ℂ) (h : ℂ) {ρ Λ : ℝ}
    (hρR : ρ < R) (hx : ∀ j, ‖x j‖ ≤ ρ) (hh : ‖h‖ ≤ ρ) (hw : ∑ j, ‖w j‖ ≤ Λ)
    (hexact : ∀ n < m, ∑ j, w j * x j ^ n = h ^ n) :
    ‖f h - ∑ j, w j • f (x j)‖ ≤ (1 + Λ) * M * (ρ / R) ^ m / (1 - ρ / R) := by
  obtain ⟨coef, hc, hs⟩ := exists_coeff_bound hR hd hM
  have hR' : (0 : ℝ) < R := hR
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hh
  have hM0 : 0 ≤ M := by
    have := hM ((R : ℂ)) (by simp [abs_of_pos hR'])
    exact (norm_nonneg _).trans this
  have hΛ0 : 0 ≤ Λ := (Finset.sum_nonneg fun j _ => norm_nonneg (w j)).trans hw
  set q := ρ / R with hq
  have hq0 : 0 ≤ q := div_nonneg hρ0 hR'.le
  have hq1 : q < 1 := (div_lt_one hR').2 hρR
  -- the expansion of the combination
  have hsum : HasSum (fun n => (h ^ n - ∑ j, w j * x j ^ n) • coef n)
      (f h - ∑ j, w j • f (x j)) := by
    have h1 := hs h (hh.trans_lt hρR)
    have h2 : HasSum (fun n => ∑ j, w j • (x j ^ n • coef n)) (∑ j, w j • f (x j)) :=
      hasSum_sum fun j _ => (hs (x j) ((hx j).trans_lt hρR)).const_smul (w j)
    convert h1.sub h2 using 1
    funext n
    rw [sub_smul, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul]
  -- the majorant series
  set C := (1 + Λ) * M with hC
  have hC0 : 0 ≤ C := mul_nonneg (by linarith) hM0
  set g : ℕ → ℝ := fun n => if m ≤ n then C * q ^ n else 0 with hg
  have hgs : HasSum g (C * q ^ m / (1 - q)) := by
    rw [← hasSum_nat_add_iff' m]
    have e1 : ∑ i ∈ Finset.range m, g i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_range] at hi; simp [hg, not_le.2 hi]
    rw [e1, sub_zero]
    have e2 : (fun n => g (n + m)) = fun n => C * q ^ m * q ^ n := by
      funext n; simp only [hg, le_add_iff_nonneg_left, zero_le, ite_true]; ring
    rw [e2, div_eq_mul_inv]
    exact (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hbound : ∀ n, ‖(h ^ n - ∑ j, w j * x j ^ n) • coef n‖ ≤ g n := by
    intro n
    by_cases hn : m ≤ n
    · simp only [hg, hn, ite_true]
      rw [norm_smul]
      have hsc : ‖h ^ n - ∑ j, w j * x j ^ n‖ ≤ (1 + Λ) * ρ ^ n := by
        calc ‖h ^ n - ∑ j, w j * x j ^ n‖ ≤ ‖h ^ n‖ + ∑ j, ‖w j * x j ^ n‖ :=
              (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
          _ ≤ ρ ^ n + ∑ j, ‖w j‖ * ρ ^ n := by
              gcongr with j
              · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hh n
              · rw [norm_mul, norm_pow]
                exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hx j) n)
                  (norm_nonneg _)
          _ = ρ ^ n + (∑ j, ‖w j‖) * ρ ^ n := by rw [Finset.sum_mul]
          _ ≤ ρ ^ n + Λ * ρ ^ n := by gcongr
          _ = (1 + Λ) * ρ ^ n := by ring
      calc ‖h ^ n - ∑ j, w j * x j ^ n‖ * ‖coef n‖ ≤ ((1 + Λ) * ρ ^ n) * (M / (R : ℝ) ^ n) :=
            mul_le_mul hsc (hc n) (norm_nonneg _) (by positivity)
        _ = C * q ^ n := by rw [hC, hq, div_pow]; field_simp
    · simp only [hg, hn, ite_false]
      rw [hexact n (not_le.1 hn), sub_self, zero_smul, norm_zero]
  have := hsum.norm_le_of_bounded hgs hbound
  rw [hC] at this
  exact this

omit [CompleteSpace E] in
/-- **Sanity**: for the constant function `0` the interpolation error vanishes. -/
theorem interp_exact_const (x w : Fin 1 → ℂ) (h : ℂ) :
    ‖(fun _ : ℂ => (0 : E)) h - ∑ j, w j • (fun _ : ℂ => (0 : E)) (x j)‖ = 0 := by
  simp

end Interp

/-! ## The strip version: polynomial tori in a parameter -/

section Strip

open WEll1Z2

variable {σ : Type*}

/-- The value at the parameter `s` of a polynomial expression with an affine parameter term:
`T₀(x(s)) + κ s · T₁(x(s))`, `x(s)_i = ∑_k s^k Y_{k,i}` (in the strip algebra `𝔸`). -/
def interpF {K : ℕ} (Y : Fin K → σ → FA) (T₀ T₁ : PolyExprS ℂ σ) (κ s : ℝ) : FA :=
  PolyExprS.eval (fun i => ∑ k : Fin K, ((s : ℂ) ^ k.val) • Y k i) T₀ +
    (((κ * s : ℝ)) : ℂ) • PolyExprS.eval (fun i => ∑ k : Fin K, ((s : ℂ) ^ k.val) • Y k i) T₁

/-- **Interpolation in a parameter, strip version.** The inputs are polynomials of degree `< K` in
the parameter with strip bounds `‖Y_{k,i}‖_r ≤ b_{k,i}`; on the disc `|s| ≤ R` they are bounded by
`a`, at which `T₀, T₁` are valid, and `T̂₀(a) + κ R T̂₁(a) ≤ M`. Then the values at the nodes `x_j`
(bounded by `e_j`) and exact weights `w_j` bound the value at every `|h| ≤ ρ < R`:
`‖F(h)‖_r ≤ ∑ |w_j| e_j + (1 + Λ) M (ρ/R)^m/(1 − ρ/R)`. -/
theorem Bd_interp {r : ℝ} (hr : 0 ≤ r) {K : ℕ} (Y : Fin K → σ → FA) (b : Fin K → σ → ℝ)
    (hY : ∀ k i, Bd r (Y k i) (b k i)) {R : NNReal} (hR : 0 < R) {a : σ → ℝ}
    (ha : ∀ i, ∑ k : Fin K, (R : ℝ) ^ k.val * b k i ≤ a i) {T₀ T₁ : PolyExprS ℂ σ}
    (hv₀ : PolyExprS.Valid a T₀) (hv₁ : PolyExprS.Valid a T₁) {κ : ℝ} (hκ : 0 ≤ κ) {M : ℝ}
    (hM : PolyExprS.maj a T₀ + κ * R * PolyExprS.maj a T₁ ≤ M) {m : ℕ} (x w e : Fin m → ℝ)
    (h : ℝ) {ρ Λ : ℝ} (hρR : ρ < R) (hx : ∀ j, |x j| ≤ ρ) (hh : |h| ≤ ρ)
    (hw : ∑ j, |w j| ≤ Λ) (hexact : ∀ n < m, ∑ j, w j * x j ^ n = h ^ n)
    (he : ∀ j, Bd r (interpF Y T₀ T₁ κ (x j)) (e j)) :
    Bd r (interpF Y T₀ T₁ κ h)
      (∑ j, |w j| * e j + (1 + Λ) * M * (ρ / R) ^ m / (1 - ρ / R)) := by
  have : Fact (0 ≤ r) := ⟨hr⟩
  set Yl : Fin K → σ → WEll1Z2 r := fun k i => liftS (Y k i) (hY k i).1 with hYl
  set V : ℂ → σ → WEll1Z2 r := fun t i => ∑ k : Fin K, t ^ k.val • Yl k i with hV
  set f : ℂ → WEll1Z2 r := fun t => PolyExprS.eval (V t) T₀ +
    ((κ : ℂ) * t) • PolyExprS.eval (V t) T₁ with hf
  have hR' : (0 : ℝ) < R := hR
  have hb0 : ∀ k i, 0 ≤ b k i := fun k i => (hY k i).nonneg
  -- bounds of the inputs on the disc
  have hVb : ∀ t : ℂ, ‖t‖ ≤ R → ∀ i, ‖V t i‖ ≤ a i := by
    intro t ht i
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans (ha i))
    rw [norm_smul, norm_pow]
    have h1 : ‖Yl k i‖ ≤ b k i := by rw [hYl, norm_liftS]; exact (hY k i).2
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht _) h1 (norm_nonneg _) (by positivity)
  have hVd : ∀ i t, DifferentiableAt ℂ (fun t => V t i) t := fun i t => by
    simp only [hV]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_pow _).smul_const _
  -- differentiability on the closed disc
  have hd : DifferentiableOn ℂ f (closedBall 0 R) := by
    intro t ht
    rw [mem_closedBall, dist_zero_right] at ht
    have h0 := PolyExprS.differentiableAt_eval (hVd · t) (hVb t ht) hv₀
    have h1 := PolyExprS.differentiableAt_eval (hVd · t) (hVb t ht) hv₁
    exact (h0.add ((differentiableAt_const _ |>.mul differentiableAt_id).smul h1)
      ).differentiableWithinAt
  -- the bound on the circle
  have hMb : ∀ t ∈ sphere (0 : ℂ) R, ‖f t‖ ≤ M := by
    intro t ht
    rw [mem_sphere, dist_zero_right] at ht
    have hb := hVb t ht.le
    refine (norm_add_le _ _).trans (le_trans ?_ hM)
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ, ht]
    exact add_le_add (PolyExprS.norm_eval_le hb hv₀)
      (mul_le_mul_of_nonneg_left (PolyExprS.norm_eval_le hb hv₁) (by positivity))
  -- real points: `f` lifts `interpF`
  have hlift : ∀ s : ℝ, |s| ≤ ρ → toFA hr (f s) = interpF Y T₀ T₁ κ s := by
    intro s hs
    have hst : ‖(s : ℂ)‖ ≤ R := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hs.trans hρR.le
    have hb := hVb s hst
    have hV' : (fun i => toFA hr (V s i)) = fun i => ∑ k : Fin K, ((s : ℂ) ^ k.val) • Y k i := by
      funext i
      simp only [hV, map_sum, map_smul, hYl, toFA_liftS]
    simp only [hf, interpF, map_add, map_smul]
    rw [PolyExprS.eval_algHom (toFA hr) (continuous_toFA hr) hb hv₀,
      PolyExprS.eval_algHom (toFA hr) (continuous_toFA hr) hb hv₁, hV']
    push_cast; ring_nf
  have hnorm : ∀ s : ℝ, |s| ≤ ρ → ‖f s‖ = wnorm r (coeff (interpF Y T₀ T₁ κ s)) := by
    intro s hs
    rw [← hlift s hs, norm_eq_wnorm]
    congr 1; funext n; rw [coeff_toFA]
  -- interpolation
  have hint := norm_sub_interp_le hR hd hMb (fun j => (x j : ℂ)) (fun j => (w j : ℂ)) (h : ℂ)
    hρR (fun j => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx j)
    (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hh)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hw)
    (fun n hn => by exact_mod_cast hexact n hn)
  have hnode : ‖∑ j, (w j : ℂ) • f (x j)‖ ≤ ∑ j, |w j| * e j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hnorm _ (hx j)]
    exact mul_le_mul_of_nonneg_left (he j).2 (abs_nonneg _)
  have hfin : ‖f h‖ ≤ ∑ j, |w j| * e j + (1 + Λ) * M * (ρ / R) ^ m / (1 - ρ / R) := by
    have := norm_sub_norm_le (f h) (∑ j, (w j : ℂ) • f (x j))
    linarith
  rw [← hlift h hh]
  exact (Bd_toFA hr _).le hfin

end Strip

end LeanTheory.Theory.KAM
