/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.StripAlgebra
public import Mathlib.RingTheory.Binomial
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Inverse square roots in commutative Banach algebras (binomial series)

A modified field such as `B̃ = B + ρ ∇ × b` (`b = B/|B|`) involves `w = |B|⁻¹`, characterized by
`w² |B|² = 1`. This file constructs `a^{−1/2}` in
a complete normed commutative `𝕜`-algebra with `‖1‖ = 1` (`𝕜 = ℝ` or `ℂ`, via `RCLike`), in
particular in the strip algebra `𝔸 = FA = ℓ¹(ℤ²)` used by the KAM step, by the binomial series.

**Coefficients.** `isqCoef n = binom(−1/2, n)` (`Ring.choose`), with the recursion
`isqCoef_succ`, alternating signs and `|binom(−½, n)| ≤ 1` (`isqCoef_sign`), and the
Chu–Vandermonde identity `∑_{i+j=n} binom(−½,i) binom(−½,j) = (−1)ⁿ` (`isqCoef_vandermonde`).

**The unit series** `S(u) = ∑ binom(−½, n) uⁿ` (`isqSeries`), for `‖u‖ < 1`:
* `isqSeries_sq_mul`: `S(u)² (1 + u) = 1` (Cauchy product + Vandermonde);
* the derivative series `S₁ = ∑ (n+1) binom(−½,n+1) uⁿ` and `S₂` satisfy `S₁ = −½ S³`,
  `S₂ = ¾ S⁵` (`isqSeries1_eq`, `isqSeries2_eq`; proved algebraically from `(1 + u)S₁ = −½ S`);
* with `M(r) = (1 − r)^{−1/2}` (`isqMaj`, identified with `∑ |binom(−½,n)| rⁿ` by
  `hasSum_isqMaj`): `‖S(u)‖ ≤ M(r)`, `‖S(w) − S(z)‖ ≤ ½ M(R)³ ‖w − z‖`,
  `‖S(w) − S(z) − S₁(z)(w − z)‖ ≤ ½ · ¾ M(R)⁵ ‖w − z‖²` (`norm_isqSeries_le`,
  `norm_isqSeries_sub_le`, `norm_isqSeries_taylor_le`).

**The inverse square root** `invSqrt 𝕜 c a = c^{−1/2} S((a − c)/c)` for real `c > 0` and
`‖a − c‖ < c`. With `g_c(t) = (c − t)^{−1/2}` (`isqG`) and `‖a − c‖, ‖b − c‖ ≤ m < c`:
* `invSqrt_sq_mul`: `(a^{−1/2})² a = 1`;
* `norm_invSqrt_le`: `‖a^{−1/2}‖ ≤ g_c(m)`;
* `norm_invSqrt_sub_le` (Lipschitz): `‖a^{−1/2} − b^{−1/2}‖ ≤ ½ g_c(m)³ ‖a − b‖`;
* `norm_invSqrt_deriv_le`: the derivative `h ↦ −½ (a^{−1/2})³ h` has norm `≤ ½ g_c(m)³`;
* `norm_invSqrt_taylor_le`:
  `‖b^{−1/2} − a^{−1/2} + ½ (a^{−1/2})³ (b − a)‖ ≤ ½ · ¾ g_c(m)⁵ ‖b − a‖²`.

**Points.** `map_invSqrt`: continuous algebra homomorphisms commute with `invSqrt`.
`isqSeries_real_eq`: for real `|t| < 1`, `S(t) = (1 + t)^{−1/2}` with the positive root (fixed
by the intermediate value theorem). `algHom_invSqrt`: if `φ : A →ₐ[𝕜] 𝕜` (e.g. evaluation at a
point) has `φ a = r` real, then `r > 0` and `φ(a^{−1/2}) = 1/√r`.

**Strip algebra.** `Bd.invSqrt`, `Bd.invSqrt_sub`, `Bd.invSqrt_taylor`: the same bounds for the
strip norms `Bd ρ` of `FA`, by lifting to `ℓ¹_ρ(ℤ²)` (`continuous_toFA`).

**Sanity.** `isqCoef_one`, `isqCoef_two`, `isqSeries_zero`, `invSqrt_algebraMap` (`a = c` gives
`c^{−1/2}`), the fixture `invSqrt_quarter` (`(1/4)^{−1/2} = 2` from the series at `c = 1`), and
the rejected fixture `invSqrt_boundary_fails` (for `‖a − c‖ ≥ c`, e.g. `a = 0` or `a = −1`
with `c = 1`, no `y` satisfies `y² a = 1`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

open Finset

/-! ## The binomial coefficients `binom(−1/2, n)` -/

/-- The binomial coefficient `binom(−1/2, n) = (−1)ⁿ (2n choose n)/4ⁿ`. -/
def isqCoef (n : ℕ) : ℝ := Ring.choose (-(1 / 2) : ℝ) n

/-- `binom(−1/2, 0) = 1`. -/
@[simp] theorem isqCoef_zero : isqCoef 0 = 1 := by simp [isqCoef]

/-- The recursion `(n + 1) binom(−1/2, n + 1) = binom(−1/2, n) (−1/2 − n)`. -/
theorem isqCoef_succ (n : ℕ) :
    ((n : ℝ) + 1) * isqCoef (n + 1) = isqCoef n * (-(1 / 2) - n) := by
  have := Ring.choose_smul_choose (-(1 / 2) : ℝ) (Nat.le_succ n)
  simp only [Nat.choose_succ_self_right, nsmul_eq_mul] at this
  simpa [isqCoef] using this

/-- Sanity: `binom(−1/2, 1) = −1/2`. -/
theorem isqCoef_one : isqCoef 1 = -(1 / 2) := by
  have := isqCoef_succ 0
  simpa using this

/-- **Chu–Vandermonde** for `−1/2 + (−1/2) = −1`: `∑_{i+j=n} binom(−½,i) binom(−½,j) = (−1)ⁿ`. -/
theorem isqCoef_vandermonde (n : ℕ) :
    ∑ ij ∈ antidiagonal n, isqCoef ij.1 * isqCoef ij.2 = (-1) ^ n := by
  have h := Ring.add_choose_eq (r := (-(1 / 2) : ℝ)) (s := -(1 / 2)) n (Commute.refl _)
  have h2 : (-(1 / 2) : ℝ) + -(1 / 2) = -1 := by norm_num
  rw [h2, Ring.choose_neg, add_sub_cancel_left, Ring.choose_natCast, Nat.choose_self] at h
  simp only [isqCoef, ← h, Nat.cast_one, Int.negOnePow, Units.smul_def]
  simp

/-- The signs alternate and the sizes decrease: `0 ≤ (−1)ⁿ binom(−½, n) ≤ 1`. -/
theorem isqCoef_sign (n : ℕ) : 0 ≤ (-1) ^ n * isqCoef n ∧ (-1) ^ n * isqCoef n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := isqCoef_succ n
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hb : isqCoef (n + 1) = isqCoef n * (-(1 / 2) - n) / (n + 1) := by
      rw [eq_div_iff hn.ne']; linarith
    have e : (-1) ^ (n + 1) * isqCoef (n + 1) =
        ((-1) ^ n * isqCoef n) * ((n + 1 / 2) / (n + 1)) := by
      rw [hb, pow_succ]; ring
    rw [e]
    have h1 : 0 ≤ ((n : ℝ) + 1 / 2) / (n + 1) := by positivity
    have h2 : ((n : ℝ) + 1 / 2) / (n + 1) ≤ 1 := by rw [div_le_one hn]; linarith
    exact ⟨mul_nonneg ih.1 h1, by nlinarith [ih.1, ih.2]⟩

/-- `|binom(−½, n)| = (−1)ⁿ binom(−½, n)`. -/
theorem abs_isqCoef (n : ℕ) : |isqCoef n| = (-1) ^ n * isqCoef n := by
  rw [← abs_of_nonneg (isqCoef_sign n).1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- `|binom(−½, n)| ≤ 1`. -/
theorem abs_isqCoef_le_one (n : ℕ) : |isqCoef n| ≤ 1 := by
  rw [abs_isqCoef]; exact (isqCoef_sign n).2

/-- First-derivative coefficients `(n + 1) binom(−½, n + 1)`. -/
def isqCoef1 (n : ℕ) : ℝ := ((n : ℝ) + 1) * isqCoef (n + 1)

/-- Second-derivative coefficients `(n + 2)(n + 1) binom(−½, n + 2)`. -/
def isqCoef2 (n : ℕ) : ℝ := ((n : ℝ) + 2) * ((n + 1) * isqCoef (n + 2))

/-! ## Scalar power series in a Banach algebra -/

section Series

variable (𝕜 : Type*) [RCLike 𝕜] {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]

/-- The power series `∑ fₙ uⁿ` with real coefficients, in a normed `𝕜`-algebra. -/
def rser (f : ℕ → ℝ) (u : A) : A := ∑' n, ((f n : ℝ) : 𝕜) • u ^ n

variable {𝕜}
variable [NormOneClass A]

/-- Absolute convergence for coefficients of at most quadratic growth and `‖u‖ < 1`. -/
theorem summable_rser {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C * ((n : ℝ) ^ 2 + 1)) {u : A}
    (hu : ‖u‖ < 1) : Summable fun n => ‖((f n : ℝ) : 𝕜) • u ^ n‖ := by
  have h0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 2 (r := ‖u‖) (by rwa [norm_norm])
  have hs2 := summable_geometric_of_lt_one h0 hu
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((hs1.add hs2).mul_left C)
  rw [norm_smul, RCLike.norm_ofReal]
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hf 0); simp at this; linarith
  calc |f n| * ‖u ^ n‖ ≤ (C * ((n : ℝ) ^ 2 + 1)) * ‖u‖ ^ n :=
        mul_le_mul (hf n) (norm_pow_le _ _) (norm_nonneg _) (by positivity)
    _ = C * ((n : ℝ) ^ 2 * ‖u‖ ^ n + ‖u‖ ^ n) := by ring

/-- Quadratic growth of `binom(−½, n)`. -/
theorem isqCoef_growth (n : ℕ) : |isqCoef n| ≤ 1 * ((n : ℝ) ^ 2 + 1) := by
  have := abs_isqCoef_le_one n
  nlinarith [sq_nonneg (n : ℝ)]

/-- Quadratic growth of the first-derivative coefficients. -/
theorem isqCoef1_growth (n : ℕ) : |isqCoef1 n| ≤ 2 * ((n : ℝ) ^ 2 + 1) := by
  have := abs_isqCoef_le_one (n + 1)
  rw [isqCoef1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg ((n : ℝ) - 1), abs_nonneg (isqCoef (n + 1))]

/-- Quadratic growth of the second-derivative coefficients. -/
theorem isqCoef2_growth (n : ℕ) : |isqCoef2 n| ≤ 3 * ((n : ℝ) ^ 2 + 1) := by
  have := abs_isqCoef_le_one (n + 2)
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [isqCoef2, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  have h1 : ((n : ℝ) + 2) * (n + 1) ≤ 3 * ((n : ℝ) ^ 2 + 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; norm_num
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  calc ((n : ℝ) + 2) * ((n + 1) * |isqCoef (n + 2)|) = ((n : ℝ) + 2) * (n + 1) *
        |isqCoef (n + 2)| := by ring
    _ ≤ ((n : ℝ) + 2) * (n + 1) * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ ≤ _ := by linarith

variable [CompleteSpace A]

omit [NormOneClass A] in
/-- Multiplication of a power series by `1 + u`: if `q₀ = p₀` and `q_{n+1} = p_{n+1} + pₙ`, then
`(∑ pₙ uⁿ)(1 + u) = ∑ qₙ uⁿ`. -/
theorem rser_mul_one_add {p q : ℕ → ℝ} {u : A}
    (hp : Summable fun n => ‖((p n : ℝ) : 𝕜) • u ^ n‖)
    (h0 : q 0 = p 0) (hs : ∀ n, q (n + 1) = p (n + 1) + p n) :
    rser 𝕜 p u * (1 + u) = rser 𝕜 q u := by
  have hp' : Summable fun n => ((p n : ℝ) : 𝕜) • u ^ n := hp.of_norm
  have hps : Summable fun n => ((p (n + 1) : ℝ) : 𝕜) • u ^ (n + 1) :=
    hp'.comp_injective (add_left_injective 1)
  have key : ∀ n, u * (((p n : ℝ) : 𝕜) • u ^ n) = ((p n : ℝ) : 𝕜) • u ^ (n + 1) := by
    intro n; rw [mul_smul_comm, pow_succ, mul_comm u]
  have hpu : Summable fun n => ((p n : ℝ) : 𝕜) • u ^ (n + 1) :=
    (hp'.mul_left u).congr key
  have hq : Summable fun n => ((q n : ℝ) : 𝕜) • u ^ n := by
    refine (summable_nat_add_iff (f := fun n => ((q n : ℝ) : 𝕜) • u ^ n) 1).1
      ((hps.add hpu).congr fun n => ?_)
    simp only [hs, RCLike.ofReal_add, add_smul]
  have hum : u * rser 𝕜 p u = ∑' n, ((p n : ℝ) : 𝕜) • u ^ (n + 1) := by
    rw [rser, ← hp'.tsum_mul_left]
    exact congrArg tsum (funext key)
  have e1 : rser 𝕜 q u = ((q 0 : ℝ) : 𝕜) • u ^ 0 +
      ∑' n, ((q (n + 1) : ℝ) : 𝕜) • u ^ (n + 1) := hq.tsum_eq_zero_add
  have e2 : rser 𝕜 p u = ((p 0 : ℝ) : 𝕜) • u ^ 0 +
      ∑' n, ((p (n + 1) : ℝ) : 𝕜) • u ^ (n + 1) := hp'.tsum_eq_zero_add
  have e3 : ∑' n, ((q (n + 1) : ℝ) : 𝕜) • u ^ (n + 1) =
      ∑' n, ((p (n + 1) : ℝ) : 𝕜) • u ^ (n + 1) + ∑' n, ((p n : ℝ) : 𝕜) • u ^ (n + 1) := by
    rw [← hps.tsum_add hpu]
    congr 1; funext n; simp only [hs, RCLike.ofReal_add, add_smul]
  rw [mul_add, mul_one, mul_comm, hum, e1, e3, e2, h0, add_assoc]

omit [NormOneClass A] [CompleteSpace A] in
/-- Scaling the coefficients scales the series. -/
theorem rser_mul_left (c : ℝ) (f : ℕ → ℝ) (u : A) :
    rser 𝕜 (fun n => c * f n) u = (c : 𝕜) • rser 𝕜 f u := by
  rw [rser, rser, ← tsum_const_smul'']
  congr 1; funext n; rw [RCLike.ofReal_mul, mul_smul]

variable (𝕜) in
/-- The binomial series `S(u) = ∑ binom(−½, n) uⁿ` of `(1 + u)^{−1/2}`. -/
def isqSeries (u : A) : A := rser 𝕜 isqCoef u

/-- **The defining identity** `S(u)² (1 + u) = 1` for `‖u‖ < 1`. -/
theorem isqSeries_sq_mul {u : A} (hu : ‖u‖ < 1) : isqSeries 𝕜 u ^ 2 * (1 + u) = 1 := by
  have hs := summable_rser (𝕜 := 𝕜) isqCoef_growth hu
  have hsq : isqSeries 𝕜 u ^ 2 = rser 𝕜 (fun n => (-1) ^ n) u := by
    rw [sq, isqSeries, rser, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs, rser]
    congr 1; funext n
    rw [← isqCoef_vandermonde n, RCLike.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.mem_antidiagonal] at hkl
    rw [smul_mul_smul_comm, ← pow_add, hkl, RCLike.ofReal_mul]
  have hp : Summable fun n => ‖(((-1 : ℝ) ^ n : ℝ) : 𝕜) • u ^ n‖ :=
    summable_rser (C := 1) (fun n => by
      rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]; nlinarith [sq_nonneg (n : ℝ)]) hu
  rw [hsq, rser_mul_one_add (q := fun n => if n = 0 then 1 else 0) hp (by simp)
    (fun n => by simp [pow_succ])]
  rw [rser, tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- `(n + 2) binom(−½, n + 2) = binom(−½, n + 1)(−3/2 − n)`. -/
theorem isqCoef_succ_succ (n : ℕ) :
    ((n : ℝ) + 2) * isqCoef (n + 2) = isqCoef (n + 1) * (-(3 / 2) - n) := by
  have := isqCoef_succ (n + 1)
  push_cast at this
  linear_combination this

/-- `(n + 3) binom(−½, n + 3) = binom(−½, n + 2)(−5/2 − n)`. -/
theorem isqCoef_succ_succ_succ (n : ℕ) :
    ((n : ℝ) + 3) * isqCoef (n + 3) = isqCoef (n + 2) * (-(5 / 2) - n) := by
  have := isqCoef_succ (n + 2)
  push_cast at this
  linear_combination this

/-- `binom(−½, 2) = 3/8`. -/
theorem isqCoef_two : isqCoef 2 = 3 / 8 := by
  have := isqCoef_succ_succ 0
  rw [isqCoef_one] at this
  norm_num at this
  linarith

/-- The derivative series satisfies `S₁(u)(1 + u) = −½ S(u)`. -/
theorem isqSeries1_mul_one_add {u : A} (hu : ‖u‖ < 1) :
    rser 𝕜 isqCoef1 u * (1 + u) = ((-(1 / 2) : ℝ) : 𝕜) • isqSeries 𝕜 u := by
  have hp := summable_rser (𝕜 := 𝕜) isqCoef1_growth hu
  rw [rser_mul_one_add (q := fun n => -(1 / 2) * isqCoef n) hp, rser_mul_left, isqSeries]
  · simp [isqCoef1, isqCoef_one]
  · intro n
    simp only [isqCoef1, Nat.add_assoc, Nat.reduceAdd]
    have := isqCoef_succ_succ n
    push_cast
    linear_combination (-1 : ℝ) * this

/-- The second-derivative series satisfies `S₂(u)(1 + u) = −(3/2) S₁(u)`. -/
theorem isqSeries2_mul_one_add {u : A} (hu : ‖u‖ < 1) :
    rser 𝕜 isqCoef2 u * (1 + u) = ((-(3 / 2) : ℝ) : 𝕜) • rser 𝕜 isqCoef1 u := by
  have hp := summable_rser (𝕜 := 𝕜) isqCoef2_growth hu
  rw [rser_mul_one_add (q := fun n => -(3 / 2) * isqCoef1 n) hp, rser_mul_left]
  · norm_num [isqCoef2, isqCoef1, isqCoef_one, isqCoef_two]
  · intro n
    simp only [isqCoef1, isqCoef2, Nat.add_assoc, Nat.reduceAdd]
    have := isqCoef_succ_succ_succ n
    push_cast
    linear_combination (-((n : ℝ) + 2)) * this

/-- Closed form of the derivative series: `S₁(u) = −½ S(u)³`. -/
theorem isqSeries1_eq {u : A} (hu : ‖u‖ < 1) :
    rser 𝕜 isqCoef1 u = ((-(1 / 2) : ℝ) : 𝕜) • isqSeries 𝕜 u ^ 3 := by
  have h1 := isqSeries_sq_mul (𝕜 := 𝕜) hu
  have h2 := isqSeries1_mul_one_add (𝕜 := 𝕜) hu
  calc rser 𝕜 isqCoef1 u = rser 𝕜 isqCoef1 u * (1 + u) * isqSeries 𝕜 u ^ 2 := by
        rw [mul_assoc, mul_comm (1 + u), h1, mul_one]
    _ = _ := by rw [h2, smul_mul_assoc]; ring_nf

/-- Closed form of the second-derivative series: `S₂(u) = (3/4) S(u)⁵`. -/
theorem isqSeries2_eq {u : A} (hu : ‖u‖ < 1) :
    rser 𝕜 isqCoef2 u = ((3 / 4 : ℝ) : 𝕜) • isqSeries 𝕜 u ^ 5 := by
  have h1 := isqSeries_sq_mul (𝕜 := 𝕜) hu
  have h2 := isqSeries2_mul_one_add (𝕜 := 𝕜) hu
  calc rser 𝕜 isqCoef2 u = rser 𝕜 isqCoef2 u * (1 + u) * isqSeries 𝕜 u ^ 2 := by
        rw [mul_assoc, mul_comm (1 + u), h1, mul_one]
    _ = _ := by
        rw [h2, isqSeries1_eq hu, smul_mul_assoc, smul_mul_assoc, smul_smul]; ring_nf
        congr 1; push_cast; ring

end Series

/-! ## Elementary power estimates -/

section Powers

variable {A : Type*} [NormedCommRing A] [NormOneClass A]

/-- `‖w^{n+1} − z^{n+1}‖ ≤ (n + 1) Rⁿ ‖w − z‖` when `‖w‖, ‖z‖ ≤ R`. -/
theorem norm_pow_succ_sub_pow_succ_le {w z : A} {R : ℝ} (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R)
    (n : ℕ) : ‖w ^ (n + 1) - z ^ (n + 1)‖ ≤ (n + 1) * R ^ n * ‖w - z‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  induction n with
  | zero => simp
  | succ n ih =>
    have e : w ^ (n + 1 + 1) - z ^ (n + 1 + 1) =
        w * (w ^ (n + 1) - z ^ (n + 1)) + (w - z) * z ^ (n + 1) := by ring
    rw [e]
    have hzn : ‖z ^ (n + 1)‖ ≤ R ^ (n + 1) :=
      (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hz _)
    calc _ ≤ ‖w‖ * ‖w ^ (n + 1) - z ^ (n + 1)‖ + ‖w - z‖ * ‖z ^ (n + 1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ R * ((n + 1) * R ^ n * ‖w - z‖) + ‖w - z‖ * R ^ (n + 1) :=
          add_le_add (mul_le_mul hw ih (norm_nonneg _) hR)
            (mul_le_mul_of_nonneg_left hzn (norm_nonneg _))
      _ = _ := by push_cast; ring

/-- Second-order remainder of a power:
`‖w^{n+2} − z^{n+2} − (n + 2) z^{n+1}(w − z)‖ ≤ ½ (n + 2)(n + 1) Rⁿ ‖w − z‖²`. -/
theorem norm_pow_taylor_le {w z : A} {R : ℝ} (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖w ^ (n + 2) - z ^ (n + 2) - ((n : A) + 2) * z ^ (n + 1) * (w - z)‖ ≤
      ((n : ℝ) + 2) * (n + 1) / 2 * R ^ n * ‖w - z‖ ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  induction n with
  | zero =>
    have e : w ^ (0 + 2) - z ^ (0 + 2) - (((0 : ℕ) : A) + 2) * z ^ (0 + 1) * (w - z) =
        (w - z) ^ 2 := by push_cast; ring
    rw [e]; simpa using norm_pow_le (w - z) 2
  | succ n ih =>
    have e : w ^ (n + 1 + 2) - z ^ (n + 1 + 2) - (((n + 1 : ℕ) : A) + 2) * z ^ (n + 1 + 1) *
        (w - z) = w * (w ^ (n + 2) - z ^ (n + 2) - ((n : A) + 2) * z ^ (n + 1) * (w - z)) +
          ((n : A) + 2) * z ^ (n + 1) * (w - z) ^ 2 := by push_cast; ring
    rw [e]
    have hzn : ‖z ^ (n + 1)‖ ≤ R ^ (n + 1) :=
      (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hz _)
    have hc : ‖((n : A) + 2)‖ ≤ (n : ℝ) + 2 := by
      have := Nat.norm_cast_le (α := A) (n + 2)
      push_cast at this; simpa using this
    have hk : ‖(w - z) ^ 2‖ ≤ ‖w - z‖ ^ 2 := norm_pow_le _ _
    calc _ ≤ ‖w‖ * ‖w ^ (n + 2) - z ^ (n + 2) - ((n : A) + 2) * z ^ (n + 1) * (w - z)‖ +
          ‖((n : A) + 2)‖ * ‖z ^ (n + 1)‖ * ‖(w - z) ^ 2‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _)
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _))))
      _ ≤ R * (((n : ℝ) + 2) * (n + 1) / 2 * R ^ n * ‖w - z‖ ^ 2) +
          ((n : ℝ) + 2) * R ^ (n + 1) * ‖w - z‖ ^ 2 := by
          gcongr
      _ = _ := by push_cast; ring

end Powers

/-! ## The scalar majorant `(1 − r)^{−1/2}` -/

section Majorant

/-- The majorant function `M(r) = (1 − r)^{−1/2}` (positive square root). -/
def isqMaj (r : ℝ) : ℝ := (Real.sqrt (1 - r))⁻¹

/-- `M(r) ≥ 0`. -/
theorem isqMaj_nonneg (r : ℝ) : 0 ≤ isqMaj r := inv_nonneg.2 (Real.sqrt_nonneg _)

/-- `M(r)² (1 − r) = 1` for `r < 1`. -/
theorem isqMaj_sq_mul {r : ℝ} (hr : r < 1) : isqMaj r ^ 2 * (1 - r) = 1 := by
  rw [isqMaj, inv_pow, Real.sq_sqrt (by linarith)]
  field_simp [show (1 - r) ≠ 0 by linarith]

/-- `M` is monotone on `(−∞, 1)`. -/
theorem isqMaj_mono {r r' : ℝ} (h : r ≤ r') (hr' : r' < 1) : isqMaj r ≤ isqMaj r' := by
  unfold isqMaj
  have h1 : 0 < Real.sqrt (1 - r') := Real.sqrt_pos.2 (by linarith)
  exact inv_anti₀ h1 (Real.sqrt_le_sqrt (by linarith))

/-- On `[0, 1)` the binomial series at `−r` has nonnegative terms `|binom(−½, n)| rⁿ`. -/
theorem isqCoef_mul_neg_pow (n : ℕ) (r : ℝ) :
    isqCoef n * (-r) ^ n = |isqCoef n| * r ^ n := by
  rw [abs_isqCoef, neg_pow]; ring

/-- `binom(−½, n + 1)(−1)ⁿ = −|binom(−½, n + 1)|`. -/
theorem isqCoef1_mul_neg_pow (n : ℕ) (r : ℝ) :
    isqCoef1 n * (-r) ^ n = -(|isqCoef1 n| * r ^ n) := by
  rw [isqCoef1, abs_mul, abs_isqCoef, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1), neg_pow,
    pow_succ]
  ring

/-- `binom(−½, n + 2)(−1)ⁿ = |binom(−½, n + 2)|`. -/
theorem isqCoef2_mul_neg_pow (n : ℕ) (r : ℝ) :
    isqCoef2 n * (-r) ^ n = |isqCoef2 n| * r ^ n := by
  rw [isqCoef2, abs_mul, abs_mul, abs_isqCoef, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1), neg_pow, pow_succ, pow_succ]
  ring

/-- In `ℝ`, `S(−r) = M(r)` for `0 ≤ r < 1`. -/
theorem isqSeries_neg_real {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    isqSeries ℝ (-r) = isqMaj r := by
  have hu : ‖-r‖ < 1 := by rw [norm_neg, Real.norm_of_nonneg hr0]; exact hr
  have h1 := isqSeries_sq_mul (𝕜 := ℝ) hu
  have hnn : 0 ≤ isqSeries ℝ (-r) := by
    rw [isqSeries, rser]
    refine tsum_nonneg fun n => ?_
    simp only [RCLike.ofReal_real_eq_id, id, smul_eq_mul, isqCoef_mul_neg_pow]
    positivity
  have h2 := isqMaj_sq_mul hr
  rw [← sub_eq_add_neg] at h1
  have : isqSeries ℝ (-r) ^ 2 = isqMaj r ^ 2 := by
    have hpos : (1 - r) ≠ 0 := by linarith
    have e1 : isqSeries ℝ (-r) ^ 2 = 1 / (1 - r) := by rw [eq_div_iff hpos]; exact h1
    have e2 : isqMaj r ^ 2 = 1 / (1 - r) := by rw [eq_div_iff hpos]; exact h2
    rw [e1, e2]
  exact (pow_left_inj₀ hnn (isqMaj_nonneg r) two_ne_zero).1 this

/-- The majorant series: `∑ |binom(−½, n)| rⁿ = M(r)` for `0 ≤ r < 1`. -/
theorem hasSum_isqMaj {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    HasSum (fun n => |isqCoef n| * r ^ n) (isqMaj r) := by
  have hu : ‖-r‖ < 1 := by rw [norm_neg, Real.norm_of_nonneg hr0]; exact hr
  have hs := (summable_rser (𝕜 := ℝ) isqCoef_growth hu).of_norm
  have := hs.hasSum
  rw [← isqSeries_neg_real hr0 hr, isqSeries, rser]
  simpa only [RCLike.ofReal_real_eq_id, id, smul_eq_mul, isqCoef_mul_neg_pow] using this

/-- The first-derivative majorant series: `∑ (n+1)|binom(−½, n+1)| rⁿ = ½ M(r)³`. -/
theorem hasSum_isqMaj1 {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    HasSum (fun n => |isqCoef1 n| * r ^ n) (isqMaj r ^ 3 / 2) := by
  have hu : ‖-r‖ < 1 := by rw [norm_neg, Real.norm_of_nonneg hr0]; exact hr
  have hs := (summable_rser (𝕜 := ℝ) isqCoef1_growth hu).of_norm
  have h1 := hs.hasSum.neg
  have e := isqSeries1_eq (𝕜 := ℝ) hu
  rw [rser] at e
  rw [e, isqSeries_neg_real hr0 hr] at h1
  simp only [RCLike.ofReal_real_eq_id, id, smul_eq_mul, isqCoef1_mul_neg_pow, neg_neg] at h1
  convert h1 using 1; ring

/-- The second-derivative majorant series: `∑ (n+2)(n+1)|binom(−½, n+2)| rⁿ = ¾ M(r)⁵`. -/
theorem hasSum_isqMaj2 {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    HasSum (fun n => |isqCoef2 n| * r ^ n) (3 * isqMaj r ^ 5 / 4) := by
  have hu : ‖-r‖ < 1 := by rw [norm_neg, Real.norm_of_nonneg hr0]; exact hr
  have hs := (summable_rser (𝕜 := ℝ) isqCoef2_growth hu).of_norm
  have h1 := hs.hasSum
  have e := isqSeries2_eq (𝕜 := ℝ) hu
  rw [rser] at e
  rw [e, isqSeries_neg_real hr0 hr] at h1
  simp only [RCLike.ofReal_real_eq_id, id, smul_eq_mul, isqCoef2_mul_neg_pow] at h1
  convert h1 using 1; ring

end Majorant

/-! ## Norm estimates for the binomial series -/

section SeriesBounds

variable {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  [NormOneClass A] [CompleteSpace A]

/-- `HasSum` form of the binomial series. -/
theorem hasSum_isqSeries {u : A} (hu : ‖u‖ < 1) :
    HasSum (fun n => ((isqCoef n : ℝ) : 𝕜) • u ^ n) (isqSeries 𝕜 u) :=
  (summable_rser (𝕜 := 𝕜) isqCoef_growth hu).of_norm.hasSum

/-- `HasSum` form of the derivative series. -/
theorem hasSum_isqSeries1 {u : A} (hu : ‖u‖ < 1) :
    HasSum (fun n => ((isqCoef1 n : ℝ) : 𝕜) • u ^ n) (rser 𝕜 isqCoef1 u) :=
  (summable_rser (𝕜 := 𝕜) isqCoef1_growth hu).of_norm.hasSum

omit [CompleteSpace A] in
/-- **Norm bound** `‖S(u)‖ ≤ M(r) = (1 − r)^{−1/2}` for `‖u‖ ≤ r < 1`. -/
theorem norm_isqSeries_le {u : A} {r : ℝ} (hu : ‖u‖ ≤ r) (hr : r < 1) :
    ‖isqSeries 𝕜 u‖ ≤ isqMaj r := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hu
  refine tsum_of_norm_bounded (hasSum_isqMaj hr0 hr) fun n => ?_
  rw [norm_smul, RCLike.norm_ofReal]
  exact mul_le_mul_of_nonneg_left ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hu _))
    (abs_nonneg _)

/-- **Lipschitz bound** `‖S(w) − S(z)‖ ≤ ½ M(R)³ ‖w − z‖` for `‖w‖, ‖z‖ ≤ R < 1`. -/
theorem norm_isqSeries_sub_le {w z : A} {R : ℝ} (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R) (hR : R < 1) :
    ‖isqSeries 𝕜 w - isqSeries 𝕜 z‖ ≤ isqMaj R ^ 3 / 2 * ‖w - z‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hw
  have hF := (hasSum_isqSeries (𝕜 := 𝕜) (hw.trans_lt hR)).sub
    (hasSum_isqSeries (𝕜 := 𝕜) (hz.trans_lt hR))
  have hF1 := (hasSum_nat_add_iff' 1).2 hF
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, sub_self, sub_zero] at hF1
  refine hF1.norm_le_of_bounded ((hasSum_isqMaj1 hR0 hR).mul_right ‖w - z‖) fun n => ?_
  rw [← smul_sub, norm_smul, RCLike.norm_ofReal, isqCoef1, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  calc |isqCoef (n + 1)| * ‖w ^ (n + 1) - z ^ (n + 1)‖ ≤
      |isqCoef (n + 1)| * ((n + 1) * R ^ n * ‖w - z‖) :=
        mul_le_mul_of_nonneg_left (norm_pow_succ_sub_pow_succ_le hw hz n) (abs_nonneg _)
    _ = _ := by ring

/-- **Second-order bound** `‖S(w) − S(z) − S₁(z)(w − z)‖ ≤ ⅜ M(R)⁵ ‖w − z‖²` for
`‖w‖, ‖z‖ ≤ R < 1` (here `⅜ M⁵ = ½ · ¾ M⁵` is half the second-derivative majorant). -/
theorem norm_isqSeries_taylor_le {w z : A} {R : ℝ} (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R) (hR : R < 1) :
    ‖isqSeries 𝕜 w - isqSeries 𝕜 z - rser 𝕜 isqCoef1 z * (w - z)‖ ≤
      3 * isqMaj R ^ 5 / 4 * ‖w - z‖ ^ 2 / 2 := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hw
  have hF := (hasSum_isqSeries (𝕜 := 𝕜) (hw.trans_lt hR)).sub
    (hasSum_isqSeries (𝕜 := 𝕜) (hz.trans_lt hR))
  have hF2 := (hasSum_nat_add_iff' 2).2 hF
  have hG := (hasSum_isqSeries1 (𝕜 := 𝕜) (hz.trans_lt hR)).mul_right (w - z)
  have hG1 := (hasSum_nat_add_iff' 1).2 hG
  have hD := hF2.sub hG1
  have e : isqSeries 𝕜 w - isqSeries 𝕜 z - ∑ i ∈ Finset.range 2,
      (((isqCoef i : ℝ) : 𝕜) • w ^ i - ((isqCoef i : ℝ) : 𝕜) • z ^ i) -
      (rser 𝕜 isqCoef1 z * (w - z) - ∑ i ∈ Finset.range 1,
        ((isqCoef1 i : ℝ) : 𝕜) • z ^ i * (w - z)) =
      isqSeries 𝕜 w - isqSeries 𝕜 z - rser 𝕜 isqCoef1 z * (w - z) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, isqCoef1]
    simp only [pow_zero, pow_one, sub_self, zero_add, CharP.cast_eq_zero]
    rw [← smul_sub, one_mul, smul_mul_assoc, one_mul]; abel
  rw [e] at hD
  refine hD.norm_le_of_bounded
    (((hasSum_isqMaj2 hR0 hR).mul_right (‖w - z‖ ^ 2)).div_const 2) fun n => ?_
  have e2 : ((isqCoef (n + 2) : ℝ) : 𝕜) • w ^ (n + 2) - ((isqCoef (n + 2) : ℝ) : 𝕜) • z ^ (n + 2)
      - ((isqCoef1 (n + 1) : ℝ) : 𝕜) • z ^ (n + 1) * (w - z) =
      ((isqCoef (n + 2) : ℝ) : 𝕜) •
        (w ^ (n + 2) - z ^ (n + 2) - ((n : A) + 2) * z ^ (n + 1) * (w - z)) := by
    simp only [isqCoef1, Algebra.smul_def, Nat.add_assoc, Nat.reduceAdd]
    push_cast
    ring
  rw [e2, norm_smul, RCLike.norm_ofReal, isqCoef2, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  calc |isqCoef (n + 2)| * ‖w ^ (n + 2) - z ^ (n + 2) - ((n : A) + 2) * z ^ (n + 1) * (w - z)‖
      ≤ |isqCoef (n + 2)| * (((n : ℝ) + 2) * (n + 1) / 2 * R ^ n * ‖w - z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_pow_taylor_le hw hz n) (abs_nonneg _)
    _ = _ := by ring

end SeriesBounds

/-! ## The inverse square root `a^{−1/2}` near a positive scalar `c` -/

/-- The scalar majorant `g_c(t) = (c − t)^{−1/2}` (zero when `t ≥ c`). -/
def isqG (c t : ℝ) : ℝ := (Real.sqrt (c - t))⁻¹

/-- `g_c(t) ≥ 0`. -/
theorem isqG_nonneg (c t : ℝ) : 0 ≤ isqG c t := inv_nonneg.2 (Real.sqrt_nonneg _)

/-- `g_c` is monotone on `(−∞, c)`. -/
theorem isqG_mono {c t t' : ℝ} (h : t ≤ t') (ht' : t' < c) : isqG c t ≤ isqG c t' := by
  unfold isqG
  have h1 : 0 < Real.sqrt (c - t') := Real.sqrt_pos.2 (by linarith)
  exact inv_anti₀ h1 (Real.sqrt_le_sqrt (by linarith))

/-- Scaling: `c^{−1/2} M(t/c) = g_c(t)` for `c > 0`. -/
theorem isqG_eq {c t : ℝ} (hc : 0 < c) : (Real.sqrt c)⁻¹ * isqMaj (t / c) = isqG c t := by
  rw [isqMaj, isqG, ← mul_inv, ← Real.sqrt_mul hc.le]
  congr 2; field_simp

/-- `(c^{−1/2})² = c⁻¹`. -/
theorem inv_sqrt_sq {c : ℝ} (hc : 0 ≤ c) : ((Real.sqrt c)⁻¹) ^ 2 = c⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hc]

section InvSqrt

variable (𝕜 : Type*) [RCLike 𝕜] {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]

/-- **The inverse square root** `a^{−1/2} = c^{−1/2} ∑ₙ binom(−½, n) ((a − c)/c)ⁿ`, meaningful
for `‖a − c‖ < c` with `c > 0` real. -/
def invSqrt (c : ℝ) (a : A) : A :=
  (((Real.sqrt c)⁻¹ : ℝ) : 𝕜) • isqSeries 𝕜 (((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)))

variable {𝕜} [NormOneClass A]

omit [NormOneClass A] in
/-- The normalized variable `u = (a − c)/c` has `‖u‖ = ‖a − c‖/c`. -/
theorem norm_isqArg {c : ℝ} (hc : 0 < c) (a : A) :
    ‖(((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)))‖ = ‖a - algebraMap 𝕜 A (c : 𝕜)‖ / c := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hc), inv_mul_eq_div]

omit [NormOneClass A] in
/-- `a = c (1 + u)` with `u = (a − c)/c`. -/
theorem eq_smul_one_add_isqArg {c : ℝ} (hc : 0 < c) (a : A) :
    a = ((c : ℝ) : 𝕜) • (1 + ((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜))) := by
  rw [smul_add, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hc.ne', RCLike.ofReal_one,
    one_smul, ← Algebra.algebraMap_eq_smul_one]
  abel

variable [CompleteSpace A]

/-- **The defining identity** `(a^{−1/2})² · a = 1` for `‖a − c‖ < c`. -/
theorem invSqrt_sq_mul {c : ℝ} {a : A} (h : ‖a - algebraMap 𝕜 A (c : 𝕜)‖ < c) :
    invSqrt 𝕜 c a ^ 2 * a = 1 := by
  have hc : 0 < c := (norm_nonneg _).trans_lt h
  have hu : ‖(((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)))‖ < 1 := by
    rw [norm_isqArg hc, div_lt_one hc]; exact h
  have h1 := isqSeries_sq_mul (𝕜 := 𝕜) hu
  rw [congrArg (invSqrt 𝕜 c a ^ 2 * ·) (eq_smul_one_add_isqArg (𝕜 := 𝕜) hc a)]
  rw [invSqrt, smul_pow, smul_mul_smul_comm, h1, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    inv_sqrt_sq hc.le, inv_mul_cancel₀ hc.ne', RCLike.ofReal_one, one_smul]

omit [CompleteSpace A] in
/-- **Norm bound** `‖a^{−1/2}‖ ≤ (c − m)^{−1/2}` when `‖a − c‖ ≤ m < c`. -/
theorem norm_invSqrt_le {c m : ℝ} {a : A} (h : ‖a - algebraMap 𝕜 A (c : 𝕜)‖ ≤ m) (hm : m < c) :
    ‖invSqrt 𝕜 c a‖ ≤ isqG c m := by
  have hc : 0 < c := ((norm_nonneg _).trans h).trans_lt hm
  have hu : ‖(((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)))‖ ≤ m / c := by
    rw [norm_isqArg hc]; exact div_le_div_of_nonneg_right h hc.le
  have hmc : m / c < 1 := by rw [div_lt_one hc]; exact hm
  rw [invSqrt, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)),
    ← isqG_eq hc]
  exact mul_le_mul_of_nonneg_left (norm_isqSeries_le hu hmc) (inv_nonneg.2 (Real.sqrt_nonneg _))

/-- **Lipschitz bound** `‖a^{−1/2} − b^{−1/2}‖ ≤ L ‖a − b‖` with `L = ½ (c − m)^{−3/2}`, when
`‖a − c‖, ‖b − c‖ ≤ m < c`. -/
theorem norm_invSqrt_sub_le {c m : ℝ} {a b : A} (ha : ‖a - algebraMap 𝕜 A (c : 𝕜)‖ ≤ m)
    (hb : ‖b - algebraMap 𝕜 A (c : 𝕜)‖ ≤ m) (hm : m < c) :
    ‖invSqrt 𝕜 c a - invSqrt 𝕜 c b‖ ≤ isqG c m ^ 3 / 2 * ‖a - b‖ := by
  have hc : 0 < c := ((norm_nonneg _).trans ha).trans_lt hm
  have hua : ‖(((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)))‖ ≤ m / c := by
    rw [norm_isqArg hc]; exact div_le_div_of_nonneg_right ha hc.le
  have hub : ‖(((c⁻¹ : ℝ) : 𝕜) • (b - algebraMap 𝕜 A (c : 𝕜)))‖ ≤ m / c := by
    rw [norm_isqArg hc]; exact div_le_div_of_nonneg_right hb hc.le
  have hmc : m / c < 1 := by rw [div_lt_one hc]; exact hm
  have hdiff : ((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)) -
      ((c⁻¹ : ℝ) : 𝕜) • (b - algebraMap 𝕜 A (c : 𝕜)) = ((c⁻¹ : ℝ) : 𝕜) • (a - b) := by
    rw [← smul_sub, sub_sub_sub_cancel_right]
  have hs : 0 ≤ (Real.sqrt c)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [invSqrt, invSqrt, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hs]
  have h1 := norm_isqSeries_sub_le (𝕜 := 𝕜) hua hub hmc
  rw [hdiff, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hc)] at h1
  calc (Real.sqrt c)⁻¹ * ‖_‖ ≤ (Real.sqrt c)⁻¹ * (isqMaj (m / c) ^ 3 / 2 * (c⁻¹ * ‖a - b‖)) :=
        mul_le_mul_of_nonneg_left h1 hs
    _ = ((Real.sqrt c)⁻¹ * isqMaj (m / c)) ^ 3 / 2 * ‖a - b‖ := by
        rw [← inv_sqrt_sq hc.le]; ring
    _ = _ := by rw [isqG_eq hc]

omit [CompleteSpace A] in
/-- **Derivative bound**: the derivative `h ↦ −½ (a^{−1/2})³ h` has norm at most
`½ (c − m)^{−3/2}` when `‖a − c‖ ≤ m < c`. -/
theorem norm_invSqrt_deriv_le {c m : ℝ} {a : A} (h : ‖a - algebraMap 𝕜 A (c : 𝕜)‖ ≤ m)
    (hm : m < c) : ‖(-(1 / 2) : 𝕜) • invSqrt 𝕜 c a ^ 3‖ ≤ isqG c m ^ 3 / 2 := by
  rw [norm_smul, norm_neg, norm_div, norm_one, RCLike.norm_ofNat]
  have := (norm_pow_le (invSqrt 𝕜 c a) 3).trans
    (pow_le_pow_left₀ (norm_nonneg _) (norm_invSqrt_le h hm) 3)
  linarith

/-- **Second-order (Taylor) bound**:
`‖b^{−1/2} − a^{−1/2} + ½ (a^{−1/2})³ (b − a)‖ ≤ ½ · ¾ (c − m)^{−5/2} ‖b − a‖²`
when `‖a − c‖, ‖b − c‖ ≤ m < c`. -/
theorem norm_invSqrt_taylor_le {c m : ℝ} {a b : A} (ha : ‖a - algebraMap 𝕜 A (c : 𝕜)‖ ≤ m)
    (hb : ‖b - algebraMap 𝕜 A (c : 𝕜)‖ ≤ m) (hm : m < c) :
    ‖invSqrt 𝕜 c b - invSqrt 𝕜 c a - (-(1 / 2) : 𝕜) • invSqrt 𝕜 c a ^ 3 * (b - a)‖ ≤
      3 * isqG c m ^ 5 / 4 * ‖b - a‖ ^ 2 / 2 := by
  have hc : 0 < c := ((norm_nonneg _).trans ha).trans_lt hm
  set ua : A := ((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)) with hua_def
  set ub : A := ((c⁻¹ : ℝ) : 𝕜) • (b - algebraMap 𝕜 A (c : 𝕜)) with hub_def
  have hua : ‖ua‖ ≤ m / c := by
    rw [norm_isqArg hc]; exact div_le_div_of_nonneg_right ha hc.le
  have hub : ‖ub‖ ≤ m / c := by
    rw [norm_isqArg hc]; exact div_le_div_of_nonneg_right hb hc.le
  have hmc : m / c < 1 := by rw [div_lt_one hc]; exact hm
  have hdiff : ub - ua = ((c⁻¹ : ℝ) : 𝕜) • (b - a) := by
    rw [hua_def, hub_def, ← smul_sub, sub_sub_sub_cancel_right]
  have hs : 0 ≤ (Real.sqrt c)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have h1 := norm_isqSeries_taylor_le (𝕜 := 𝕜) hub hua hmc
  rw [isqSeries1_eq ((hua.trans_lt hmc))] at h1
  set s : ℝ := (Real.sqrt c)⁻¹ with hs_def
  have hsc : s ^ 2 = c⁻¹ := inv_sqrt_sq hc.le
  have key : invSqrt 𝕜 c b - invSqrt 𝕜 c a - (-(1 / 2) : 𝕜) • invSqrt 𝕜 c a ^ 3 * (b - a) =
      (s : 𝕜) • (isqSeries 𝕜 ub - isqSeries 𝕜 ua -
        ((-(1 / 2) : ℝ) : 𝕜) • isqSeries 𝕜 ua ^ 3 * (ub - ua)) := by
    rw [invSqrt, invSqrt, ← hua_def, ← hub_def, hdiff, ← hs_def]
    have hsc' : ((c⁻¹ : ℝ) : 𝕜) = (s : 𝕜) ^ 2 := by rw [← hsc]; push_cast; ring
    rw [hsc']
    push_cast
    simp only [Algebra.smul_def, map_pow, map_neg]
    ring
  rw [key, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hs, hdiff]
  rw [hdiff, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hc)] at h1
  calc s * ‖_‖ ≤ s * (3 * isqMaj (m / c) ^ 5 / 4 * (c⁻¹ * ‖b - a‖) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h1 hs
    _ = 3 * (s * isqMaj (m / c)) ^ 5 / 4 * ‖b - a‖ ^ 2 / 2 := by
        rw [← hsc]; ring
    _ = _ := by rw [hs_def, isqG_eq hc]

/-- Continuous algebra homomorphisms commute with `invSqrt` (in the convergence domain). -/
theorem map_invSqrt {B : Type*} [NormedCommRing B] [NormedAlgebra 𝕜 B] (f : A →ₐ[𝕜] B)
    (hf : Continuous f) {c : ℝ} {a : A} (h : ‖a - algebraMap 𝕜 A (c : 𝕜)‖ < c) :
    f (invSqrt 𝕜 c a) = invSqrt 𝕜 c (f a) := by
  have hc : 0 < c := (norm_nonneg _).trans_lt h
  have hu : ‖(((c⁻¹ : ℝ) : 𝕜) • (a - algebraMap 𝕜 A (c : 𝕜)))‖ < 1 := by
    rw [norm_isqArg hc, div_lt_one hc]; exact h
  have hs := (hasSum_isqSeries (𝕜 := 𝕜) hu).map f hf
  have e : (⇑f ∘ fun n => ((isqCoef n : ℝ) : 𝕜) • (((c⁻¹ : ℝ) : 𝕜) •
      (a - algebraMap 𝕜 A (c : 𝕜))) ^ n) =
      fun n => ((isqCoef n : ℝ) : 𝕜) • (((c⁻¹ : ℝ) : 𝕜) • (f a - algebraMap 𝕜 B (c : 𝕜))) ^ n := by
    funext n; simp [map_smul, map_pow, map_sub, AlgHom.commutes]
  rw [e] at hs
  rw [invSqrt, invSqrt, map_smul]
  congr 1
  exact hs.tsum_eq.symm

end InvSqrt

/-! ## Real values and evaluation at points -/

section RealValues

/-- The real binomial series at `t ∈ (−1, 1)` is the positive inverse square root:
`S(t) = (1 + t)^{−1/2}` (the sign is fixed by continuity and the intermediate value theorem). -/
theorem isqSeries_real_eq {t : ℝ} (ht : |t| < 1) : isqSeries ℝ t = (Real.sqrt (1 + t))⁻¹ := by
  have hsq : ∀ s ∈ Set.Icc (0 : ℝ) 1, isqSeries ℝ (s * t) ^ 2 * (1 + s * t) = 1 := by
    intro s hs
    refine isqSeries_sq_mul ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1]
    calc s * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
      _ < 1 := by linarith
  have hcont : ContinuousOn (fun s : ℝ => isqSeries ℝ (s * t)) (Set.Icc 0 1) := by
    simp only [isqSeries, rser]
    refine continuousOn_tsum (fun n => (by fun_prop :
      Continuous fun s : ℝ => ((isqCoef n : ℝ) : ℝ) • (s * t) ^ n).continuousOn)
      (hasSum_isqMaj (abs_nonneg t) ht).summable (fun n s hs => ?_)
    rw [norm_smul, RCLike.norm_ofReal, norm_pow, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hs.1 (abs_nonneg t)) ?_ n)
      (abs_nonneg _)
    calc s * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
      _ = |t| := one_mul _
  have h0 : isqSeries ℝ ((0 : ℝ) * t) = 1 := by
    rw [zero_mul, isqSeries, rser, tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp
  have hpos : 0 < isqSeries ℝ t := by
    by_contra hneg
    push Not at hneg
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont
      (show (0 : ℝ) ∈ Set.Icc (isqSeries ℝ (1 * t)) (isqSeries ℝ (0 * t)) by
        rw [one_mul, h0]; exact ⟨hneg, zero_le_one⟩)
    have := hsq s hs
    rw [show isqSeries ℝ (s * t) = 0 from hs0] at this
    simp at this
  have h1 := hsq 1 ⟨zero_le_one, le_rfl⟩
  rw [one_mul] at h1
  have h1t : 0 < 1 + t := by have := neg_abs_le t; linarith
  have e1 : isqSeries ℝ t ^ 2 = ((Real.sqrt (1 + t))⁻¹) ^ 2 := by
    rw [inv_sqrt_sq h1t.le]; exact eq_inv_of_mul_eq_one_left h1
  exact (pow_left_inj₀ hpos.le (inv_nonneg.2 (Real.sqrt_nonneg _)) two_ne_zero).1 e1

/-- In `ℝ`, `invSqrt` is the positive inverse square root: `invSqrt c r = 1/√r` when
`|r − c| < c`. -/
theorem invSqrt_real {c r : ℝ} (h : |r - c| < c) : invSqrt ℝ c r = (Real.sqrt r)⁻¹ := by
  have hc : 0 < c := (abs_nonneg _).trans_lt h
  have ht : |c⁻¹ * (r - c)| < 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hc), inv_mul_lt_iff₀ hc, mul_one]; exact h
  have hr : 0 < r := by have := neg_abs_le (r - c); linarith
  simp only [invSqrt, RCLike.ofReal_real_eq_id, id, smul_eq_mul, Algebra.algebraMap_self,
    RingHom.id_apply]
  rw [isqSeries_real_eq ht, ← mul_inv, ← Real.sqrt_mul hc.le]
  congr 2; field_simp; ring

/-- The complex (or `RCLike`) binomial series at a real point is the real one. -/
theorem isqSeries_ofReal {𝕜 : Type*} [RCLike 𝕜] (t : ℝ) :
    isqSeries 𝕜 (t : 𝕜) = ((isqSeries ℝ t : ℝ) : 𝕜) := by
  simp only [isqSeries, rser, RCLike.ofReal_real_eq_id, id, smul_eq_mul, RCLike.ofReal_tsum,
    RCLike.ofReal_mul, RCLike.ofReal_pow]

/-- `invSqrt` at a real point of `𝕜` is the real `invSqrt`. -/
theorem invSqrt_ofReal {𝕜 : Type*} [RCLike 𝕜] (c r : ℝ) :
    invSqrt 𝕜 c (r : 𝕜) = ((invSqrt ℝ c r : ℝ) : 𝕜) := by
  have e : (((c⁻¹ : ℝ) : 𝕜) • ((r : 𝕜) - algebraMap 𝕜 𝕜 (c : 𝕜))) =
      ((c⁻¹ * (r - c) : ℝ) : 𝕜) := by
    simp only [Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]; push_cast; ring
  rw [invSqrt, invSqrt, e, isqSeries_ofReal]
  simp only [RCLike.ofReal_real_eq_id, id, smul_eq_mul, Algebra.algebraMap_self,
    RingHom.id_apply, RCLike.ofReal_mul]

/-- **Evaluation commutes with `invSqrt`**: if `φ : A → 𝕜` is an algebra homomorphism (e.g.
evaluation of a Fourier series at a point) and `φ a = r` is real, then `r > 0` and
`φ(a^{−1/2}) = 1/√r`. (Characters of a Banach algebra are automatically continuous with
`‖φ‖ ≤ 1`.) -/
theorem algHom_invSqrt {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    [NormOneClass A] [CompleteSpace A] {c : ℝ} {a : A} (h : ‖a - algebraMap 𝕜 A (c : 𝕜)‖ < c)
    (φ : A →ₐ[𝕜] 𝕜) {r : ℝ} (hr : φ a = r) :
    0 < r ∧ φ (invSqrt 𝕜 c a) = (((Real.sqrt r)⁻¹ : ℝ) : 𝕜) := by
  have hφ : Continuous φ := AddMonoidHomClass.continuous_of_bound φ 1 fun x => by
    rw [one_mul]; exact AlgHom.norm_apply_le_self φ x
  have hrc : |r - c| < c := by
    have h1 := AlgHom.norm_apply_le_self φ (a - algebraMap 𝕜 A (c : 𝕜))
    rw [map_sub, AlgHom.commutes, hr, Algebra.algebraMap_self, RingHom.id_apply,
      ← RCLike.ofReal_sub, RCLike.norm_ofReal] at h1
    exact h1.trans_lt h
  have hc : 0 < c := (abs_nonneg _).trans_lt hrc
  refine ⟨by have := neg_abs_le (r - c); linarith, ?_⟩
  rw [map_invSqrt φ hφ h, hr, ← invSqrt_real hrc, invSqrt_ofReal]

end RealValues

/-! ## Sanity checks -/

section Sanity

/-- Sanity: `S(0) = 1`. -/
theorem isqSeries_zero {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedCommRing A]
    [NormedAlgebra 𝕜 A] : isqSeries 𝕜 (0 : A) = 1 := by
  rw [isqSeries, rser, tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- Sanity (degenerate case): `invSqrt c (c·1) = c^{−1/2}·1`. -/
theorem invSqrt_algebraMap {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedCommRing A]
    [NormedAlgebra 𝕜 A] (c : ℝ) :
    invSqrt 𝕜 c (algebraMap 𝕜 A (c : 𝕜)) = algebraMap 𝕜 A (((Real.sqrt c)⁻¹ : ℝ) : 𝕜) := by
  rw [invSqrt, sub_self, smul_zero, isqSeries_zero, Algebra.algebraMap_eq_smul_one]

/-- Sanity (accepted fixture): `(1/4)^{−1/2} = 2`, computed by the series centred at `c = 1`. -/
theorem invSqrt_quarter : invSqrt ℝ 1 (1 / 4 : ℝ) = 2 := by
  rw [invSqrt_real (by norm_num [abs_of_neg])]
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- Rejected fixture: the hypothesis `‖a − c‖ < c` cannot be dropped. For `a = 0`, `c = 1`
(so `‖a − c‖ = c`) no element `y` satisfies `y² a = 1`; for `a = −1` (`‖a − c‖ = 2 > c`) no
real `y` does either. -/
theorem invSqrt_boundary_fails :
    ‖(0 : ℝ) - algebraMap ℝ ℝ 1‖ = 1 ∧ (∀ y : ℝ, y ^ 2 * 0 ≠ 1) ∧
      ‖(-1 : ℝ) - algebraMap ℝ ℝ 1‖ = 2 ∧ (∀ y : ℝ, y ^ 2 * (-1) ≠ 1) := by
  refine ⟨by norm_num, fun y => by simp, by norm_num, fun y => ?_⟩
  nlinarith [sq_nonneg y]

end Sanity


/-! ## The strip algebra `𝔸 = ℓ¹(ℤ²)` used by the KAM step -/

section Strip

open WEll1Z2

/-- `toFA` is continuous (it does not increase norms). -/
theorem continuous_toFA {ρ : ℝ} (hρ : 0 ≤ ρ) : Continuous (toFA hρ) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  refine AddMonoidHomClass.continuous_of_bound (toFA hρ) 1 fun x => ?_
  rw [one_mul, norm_eq_wnorm]
  exact ((Bd_toFA hρ x).mono hρ le_rfl).2

/-- A strip bound on the image of `z` under `toFA` bounds the norm of `z`. -/
theorem norm_le_of_Bd_toFA {ρ B : ℝ} (hρ : 0 ≤ ρ) {z : WEll1Z2 ρ} (h : Bd ρ (toFA hρ z) B) :
    ‖z‖ ≤ B := by
  rw [norm_eq_wnorm]
  have e : coeff (toFA hρ z) = coeff z := funext (coeff_toFA hρ z)
  rw [← e]; exact h.2

/-- Lifting an element close to a constant to the strip space `ℓ¹_ρ(ℤ²)`. -/
theorem exists_lift_of_Bd_sub {ρ m : ℝ} [hρ' : Fact (0 ≤ ρ)] (hρ : 0 ≤ ρ) {x : FA} {c : ℂ}
    (hx : Bd ρ (x - algebraMap ℂ FA c) m) :
    ∃ xl : WEll1Z2 ρ, toFA hρ xl = x ∧ ‖xl - algebraMap ℂ (WEll1Z2 ρ) c‖ ≤ m := by
  have hw : InWeighted ρ (coeff x) := by
    have h1 := (hx.add (Bd_algebraMap ρ c)).1
    simpa using h1
  refine ⟨liftS x hw, toFA_liftS hρ x hw, norm_le_of_Bd_toFA hρ ?_⟩
  rw [map_sub, AlgHom.commutes, toFA_liftS]
  exact hx

/-- **Strip norm bound for `invSqrt`**: if `‖x − c‖_ρ ≤ m < c` then
`‖x^{−1/2}‖_ρ ≤ (c − m)^{−1/2}`. -/
theorem Bd.invSqrt {ρ m c : ℝ} (hρ : 0 ≤ ρ) {x : FA}
    (hx : Bd ρ (x - algebraMap ℂ FA (c : ℂ)) m) (hm : m < c) :
    Bd ρ (KAM.invSqrt ℂ c x) (isqG c m) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨xl, hmap, hsub⟩ := exists_lift_of_Bd_sub hρ hx
  rw [← hmap, ← map_invSqrt (toFA hρ) (continuous_toFA hρ) (hsub.trans_lt hm)]
  exact (Bd_toFA hρ _).le (norm_invSqrt_le hsub hm)

/-- **Strip Lipschitz bound for `invSqrt`**: if `‖x − c‖_ρ, ‖y − c‖_ρ ≤ m < c` and
`‖x − y‖_ρ ≤ B` then `‖x^{−1/2} − y^{−1/2}‖_ρ ≤ ½ (c − m)^{−3/2} B`. -/
theorem Bd.invSqrt_sub {ρ m c B : ℝ} (hρ : 0 ≤ ρ) {x y : FA}
    (hx : Bd ρ (x - algebraMap ℂ FA (c : ℂ)) m) (hy : Bd ρ (y - algebraMap ℂ FA (c : ℂ)) m)
    (hm : m < c) (hxy : Bd ρ (x - y) B) :
    Bd ρ (KAM.invSqrt ℂ c x - KAM.invSqrt ℂ c y) (isqG c m ^ 3 / 2 * B) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨xl, hmx, hsx⟩ := exists_lift_of_Bd_sub hρ hx
  obtain ⟨yl, hmy, hsy⟩ := exists_lift_of_Bd_sub hρ hy
  have hd : ‖xl - yl‖ ≤ B := norm_le_of_Bd_toFA hρ (by rw [map_sub, hmx, hmy]; exact hxy)
  rw [← hmx, ← hmy, ← map_invSqrt (toFA hρ) (continuous_toFA hρ) (hsx.trans_lt hm),
    ← map_invSqrt (toFA hρ) (continuous_toFA hρ) (hsy.trans_lt hm), ← map_sub]
  refine (Bd_toFA hρ _).le ((norm_invSqrt_sub_le hsx hsy hm).trans ?_)
  exact mul_le_mul_of_nonneg_left hd (by have := isqG_nonneg c m; positivity)

/-- **Strip Taylor bound for `invSqrt`**: if `‖x − c‖_ρ, ‖y − c‖_ρ ≤ m < c` and
`‖y − x‖_ρ ≤ B` then `‖y^{−1/2} − x^{−1/2} + ½ (x^{−1/2})³ (y − x)‖_ρ ≤ ⅜ (c − m)^{−5/2} B²`. -/
theorem Bd.invSqrt_taylor {ρ m c B : ℝ} (hρ : 0 ≤ ρ) {x y : FA}
    (hx : Bd ρ (x - algebraMap ℂ FA (c : ℂ)) m) (hy : Bd ρ (y - algebraMap ℂ FA (c : ℂ)) m)
    (hm : m < c) (hxy : Bd ρ (y - x) B) :
    Bd ρ (KAM.invSqrt ℂ c y - KAM.invSqrt ℂ c x -
      (-(1 / 2) : ℂ) • KAM.invSqrt ℂ c x ^ 3 * (y - x)) (3 * isqG c m ^ 5 / 4 * B ^ 2 / 2) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨xl, hmx, hsx⟩ := exists_lift_of_Bd_sub hρ hx
  obtain ⟨yl, hmy, hsy⟩ := exists_lift_of_Bd_sub hρ hy
  have hd : ‖yl - xl‖ ≤ B := norm_le_of_Bd_toFA hρ (by rw [map_sub, hmx, hmy]; exact hxy)
  rw [← hmx, ← hmy, ← map_invSqrt (toFA hρ) (continuous_toFA hρ) (hsx.trans_lt hm),
    ← map_invSqrt (toFA hρ) (continuous_toFA hρ) (hsy.trans_lt hm), ← map_pow, ← map_smul,
    ← map_sub, ← map_sub, ← map_mul, ← map_sub]
  refine (Bd_toFA hρ _).le ((norm_invSqrt_taylor_le hsx hsy hm).trans ?_)
  have := isqG_nonneg c m
  gcongr

end Strip

end LeanTheory.Theory.KAM
