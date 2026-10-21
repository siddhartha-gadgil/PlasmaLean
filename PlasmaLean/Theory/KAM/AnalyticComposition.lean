/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.InvSqrt
public import PlasmaLean.Theory.KAM.StripEval

/-!
# Analytic composition in Banach algebras (KAM for non-polynomial fields)

The KAM step of `Design/KamFlow*` composes the field with the torus through polynomial
expressions (`PolyExpr`, `PolyExprS`). The coil field (`after-kam.md`, §2.2, target 1 option (a))
is not polynomial, so this file provides the analytic replacement: a two-variable power series
with Banach-algebra coefficients obeying **Cauchy majorants**. Mathlib has no multivariable
"holomorphic ⇒ power series" theorem (no Hartogs/Osgood, no polydisc Cauchy formula), so the
coefficients `c_α = ∂^αX(K₀)/α!` are part of the interface; producing them for the coil field
(polydisc Cauchy estimates for the complex Biot–Savart field plus Paley–Wiener) is later work.

**Series** (a complete normed commutative ring `A` with `‖1‖ = 1`):
* `Majorized c C d`: `‖c_α‖ ≤ C/d^{α₁+α₂}`;
* `comp c h = ∑ c_α h₁^{α₁} h₂^{α₂}`, `d1`, `d2` (termwise partial derivatives), `dcomp c h k =
  d1 c h · k₁ + d2 c h · k₂`.

**Bounds** for `‖hᵢ‖ ≤ s < d` (resp. `‖hᵢ‖ + ‖kᵢ‖ ≤ s < d`), with `x = s/d`:
* `comp_summable_and_le`: `‖comp c h‖ ≤ C/(1 − x)²`;
* `d1_summable_and_le`, `d2_summable_and_le`: `‖∂ᵢX‖ ≤ C/(d(1 − x)³)`;
* `norm_comp_sub_le` (Lipschitz): `‖comp c (h+k) − comp c h‖ ≤ C/(d(1 − x)³) (‖k₁‖ + ‖k₂‖)`;
* `norm_d1_sub_le`, `norm_d2_sub_le`: `‖∂ᵢX(h+k) − ∂ᵢX(h)‖ ≤ M₂ (‖k₁‖ + ‖k₂‖)`,
  `M₂ = 2C/(d²(1 − x)⁴)`;
* **`comp_taylor`**: `‖comp c (h+k) − comp c h − dcomp c h k‖ ≤ ½M₂ (‖k₁‖ + ‖k₂‖)²`
  (`½M₂ = 16C/d²` at `s = d/2`).
The proofs use the one-variable monomial estimates of `InvSqrt` and the scalar majorants
`p₀ = xᵃ`, `p₁ = a x^{a−1}`, `p₂ = a(a−1)/2 x^{a−2}` with sums `1/(1 − x)^{1,2,3}`.

**Strip algebra.** `bd_comp`, `bd_d1`, `bd_d2`, `bd_comp_taylor`: the same bounds in the strip
norms `Bd ρ` of `FA` (lifting to `ℓ¹_ρ(ℤ²)` and `toFA_comp`, `toFA_d1`, `toFA_d2`).
`AnaFieldAt ρ C d X`: Taylor coefficients along the torus with strip majorants and pointwise
convergence to the field `X`; **`AnaFieldAt.comp_eval`**: the composition evaluates to
`X(K₀ + h)` at every point of the real torus.

**Sanity.** `comp_zero_series`, `comp_zero` (`h = 0` gives `c₀₀`), `comp_const`,
`comp_monomial` (the polynomial case), and the rejected fixture `not_summable_at_radius`
(`c_α = 1`, `d = 1`: divergence at `h = (1, 0)`, so the radius condition is needed).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM.AnalyticComposition

open Finset

/-! ## Scalar majorant sequences -/

/-- The majorant `p₀(x, a) = xᵃ` of `‖zᵃ‖`. -/
def p0 (x : ℝ) (a : ℕ) : ℝ := x ^ a

/-- The majorant `p₁(x, a) = a x^{a−1}` of the first derivative of `zᵃ`. -/
def p1 (x : ℝ) (a : ℕ) : ℝ := (a : ℝ) * x ^ (a - 1)

/-- The majorant `p₂(x, a) = a(a−1)/2 · x^{a−2}` of half the second derivative of `zᵃ`. -/
def p2 (x : ℝ) (a : ℕ) : ℝ := (a : ℝ) * ((a : ℝ) - 1) / 2 * x ^ (a - 2)

/-- `p₀ ≥ 0` for `x ≥ 0`. -/
theorem p0_nonneg {x : ℝ} (hx : 0 ≤ x) (a : ℕ) : 0 ≤ p0 x a := pow_nonneg hx a

/-- `p₁ ≥ 0` for `x ≥ 0`. -/
theorem p1_nonneg {x : ℝ} (hx : 0 ≤ x) (a : ℕ) : 0 ≤ p1 x a := by
  unfold p1; positivity

/-- `p₂ ≥ 0` for `x ≥ 0`. -/
theorem p2_nonneg {x : ℝ} (hx : 0 ≤ x) (a : ℕ) : 0 ≤ p2 x a := by
  unfold p2
  rcases a with _ | a
  · simp
  · push_cast; have : (0 : ℝ) ≤ a := a.cast_nonneg
    have : 0 ≤ ((a : ℝ) + 1) * ((a : ℝ) + 1 - 1) / 2 := by nlinarith
    positivity

/-- `∑ xᵃ = 1/(1 − x)`. -/
theorem hasSum_p0 {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : HasSum (p0 x) (1 / (1 - x)) := by
  rw [one_div]; exact hasSum_geometric_of_lt_one hx0 hx

/-- `∑ a x^{a−1} = 1/(1 − x)²`. -/
theorem hasSum_p1 {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : HasSum (p1 x) (1 / (1 - x) ^ 2) := by
  have hn : ‖x‖ < 1 := by rwa [Real.norm_of_nonneg hx0]
  have h := hasSum_choose_mul_geometric_of_norm_lt_one 1 hn
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, p1, Nat.cast_zero, zero_mul, sub_zero]
  refine h.congr_fun fun n => ?_
  simp [Nat.choose_one_right]

/-- `∑ a(a−1)/2 · x^{a−2} = 1/(1 − x)³`. -/
theorem hasSum_p2 {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : HasSum (p2 x) (1 / (1 - x) ^ 3) := by
  have hn : ‖x‖ < 1 := by rwa [Real.norm_of_nonneg hx0]
  have h := hasSum_choose_mul_geometric_of_norm_lt_one 2 hn
  rw [← hasSum_nat_add_iff' 2]
  simp only [p2, sum_range_succ, range_zero, sum_empty]
  norm_num
  rw [show ((1 - x) ^ 3)⁻¹ = 1 / (1 - x) ^ (2 + 1) by norm_num]
  refine h.congr_fun fun n => ?_
  rw [Nat.cast_choose_two]
  push_cast; ring

/-- Scaling of `p₀`: `p₀(s, a) = dᵃ p₀(s/d, a)`. -/
theorem p0_scale {d : ℝ} (hd : 0 < d) (s : ℝ) (a : ℕ) : p0 s a = d ^ a * p0 (s / d) a := by
  unfold p0; rw [div_pow]; field_simp

/-- Scaling of `p₁`: `p₁(s, a) d = dᵃ p₁(s/d, a)`. -/
theorem p1_scale {d : ℝ} (hd : 0 < d) (s : ℝ) (a : ℕ) :
    p1 s a * d ^ 1 = d ^ a * p1 (s / d) a := by
  unfold p1
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel, div_pow]; field_simp; ring

/-- Scaling of `p₂`: `p₂(s, a) d² = dᵃ p₂(s/d, a)`. -/
theorem p2_scale {d : ℝ} (hd : 0 < d) (s : ℝ) (a : ℕ) :
    p2 s a * d ^ 2 = d ^ a * p2 (s / d) a := by
  unfold p2
  rcases a with _ | _ | a
  · simp
  · simp
  · simp only [show a + 1 + 1 - 2 = a by omega, div_pow]; field_simp; ring

/-- Bookkeeping for the majorants: `C/d^{a+b} · (P Q) = C P' Q'/d^{i+j}` when
`P dⁱ = dᵃ P'` and `Q dʲ = dᵇ Q'`. -/
theorem scale_mul {C d P Q P' Q' : ℝ} {a b i j : ℕ} (hd : 0 < d) (hP : P * d ^ i = d ^ a * P')
    (hQ : Q * d ^ j = d ^ b * Q') :
    C / d ^ (a + b) * (P * Q) = C * (P' * Q') / d ^ (i + j) := by
  rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity), pow_add, pow_add]
  linear_combination (C * Q * d ^ j) * hP + (C * d ^ a * P') * hQ

/-- Sums over `ℕ × ℕ` of products of non-negative summable sequences. -/
theorem hasSum_prod_mul {f g : ℕ → ℝ} {F G : ℝ} (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hf : HasSum f F) (hg : HasSum g G) : HasSum (fun α : ℕ × ℕ => f α.1 * g α.2) (F * G) := by
  refine hf.mul hg (summable_mul_of_summable_norm ?_ ?_)
  · simpa [Real.norm_of_nonneg (hf0 _)] using hf.summable
  · simpa [Real.norm_of_nonneg (hg0 _)] using hg.summable

/-! ## One-variable power estimates in a Banach algebra -/

section Powers

variable {A : Type*} [NormedCommRing A] [NormOneClass A]

/-- `‖zᵃ‖ ≤ p₀(R, a)` for `‖z‖ ≤ R`. -/
theorem norm_pow_le_p0 {z : A} {R : ℝ} (hz : ‖z‖ ≤ R) (a : ℕ) : ‖z ^ a‖ ≤ p0 R a :=
  (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hz _)

/-- `‖a z^{a−1}‖ ≤ p₁(R, a)` for `‖z‖ ≤ R`. -/
theorem norm_cast_mul_pow_le_p1 {z : A} {R : ℝ} (hz : ‖z‖ ≤ R) (a : ℕ) :
    ‖(a : A) * z ^ (a - 1)‖ ≤ p1 R a := by
  have hc : ‖(a : A)‖ ≤ a := by simpa using Nat.norm_cast_le (α := A) a
  exact (norm_mul_le _ _).trans (mul_le_mul hc (norm_pow_le_p0 hz _) (norm_nonneg _)
    (Nat.cast_nonneg _))

/-- `‖wᵃ − zᵃ‖ ≤ p₁(R, a) ‖w − z‖` for `‖w‖, ‖z‖ ≤ R`. -/
theorem norm_pow_sub_le_p1 {w z : A} {R : ℝ} (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R) (a : ℕ) :
    ‖w ^ a - z ^ a‖ ≤ p1 R a * ‖w - z‖ := by
  rcases a with _ | a
  · simp [p1]
  · have := norm_pow_succ_sub_pow_succ_le hw hz a
    simpa [p1] using this

/-- `‖wᵃ − zᵃ − a z^{a−1}(w − z)‖ ≤ p₂(R, a) ‖w − z‖²` for `‖w‖, ‖z‖ ≤ R`. -/
theorem norm_pow_taylor_le_p2 {w z : A} {R : ℝ} (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R) (a : ℕ) :
    ‖w ^ a - z ^ a - (a : A) * z ^ (a - 1) * (w - z)‖ ≤ p2 R a * ‖w - z‖ ^ 2 := by
  rcases a with _ | _ | a
  · simp [p2]
  · simp [p2]
  · have := norm_pow_taylor_le hw hz a
    have e : ((a + 1 + 1 : ℕ) : A) = (a : A) + 2 := by push_cast; ring
    rw [e, show a + 1 + 1 - 1 = a + 1 by omega, show a + 1 + 1 = a + 2 by omega]
    refine this.trans (le_of_eq ?_)
    simp only [p2, show a + 2 - 2 = a by omega]; push_cast; ring

/-- First-order bracket of a monomial `z₁ᵃ z₂ᵇ`:
`W₁ᵃW₂ᵇ − Z₁ᵃZ₂ᵇ = (W₁ᵃ − Z₁ᵃ)W₂ᵇ + Z₁ᵃ(W₂ᵇ − Z₂ᵇ)` and its majorant. -/
theorem norm_mono_sub_le {Z₁ Z₂ W₁ W₂ : A} {s : ℝ} (hZ₁ : ‖Z₁‖ ≤ s) (hZ₂ : ‖Z₂‖ ≤ s)
    (hW₁ : ‖W₁‖ ≤ s) (hW₂ : ‖W₂‖ ≤ s) (a b : ℕ) :
    ‖W₁ ^ a * W₂ ^ b - Z₁ ^ a * Z₂ ^ b‖ ≤
      p1 s a * ‖W₁ - Z₁‖ * p0 s b + p0 s a * (p1 s b * ‖W₂ - Z₂‖) := by
  have hs : 0 ≤ s := (norm_nonneg _).trans hZ₁
  rw [show W₁ ^ a * W₂ ^ b - Z₁ ^ a * Z₂ ^ b =
    (W₁ ^ a - Z₁ ^ a) * W₂ ^ b + Z₁ ^ a * (W₂ ^ b - Z₂ ^ b) by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_pow_sub_le_p1 hW₁ hZ₁ a)
      (norm_pow_le_p0 hW₂ b) (norm_nonneg _)
      (mul_nonneg (p1_nonneg hs _) (norm_nonneg _)))
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_pow_le_p0 hZ₁ a)
      (norm_pow_sub_le_p1 hW₂ hZ₂ b) (norm_nonneg _) (p0_nonneg hs _))

/-- Second-order bracket of a monomial `z₁ᵃ z₂ᵇ` (the Taylor remainder, split into three
pieces) and its majorant `p₂p₀ t₁² + p₁p₁ t₁t₂ + p₀p₂ t₂²`. -/
theorem norm_mono_taylor_le {Z₁ Z₂ W₁ W₂ : A} {s : ℝ} (hZ₁ : ‖Z₁‖ ≤ s) (hZ₂ : ‖Z₂‖ ≤ s)
    (hW₁ : ‖W₁‖ ≤ s) (hW₂ : ‖W₂‖ ≤ s) (a b : ℕ) :
    ‖(W₁ ^ a - Z₁ ^ a - (a : A) * Z₁ ^ (a - 1) * (W₁ - Z₁)) * W₂ ^ b +
        (a : A) * Z₁ ^ (a - 1) * (W₁ - Z₁) * (W₂ ^ b - Z₂ ^ b) +
        Z₁ ^ a * (W₂ ^ b - Z₂ ^ b - (b : A) * Z₂ ^ (b - 1) * (W₂ - Z₂))‖ ≤
      p2 s a * ‖W₁ - Z₁‖ ^ 2 * p0 s b + p1 s a * ‖W₁ - Z₁‖ * (p1 s b * ‖W₂ - Z₂‖) +
        p0 s a * (p2 s b * ‖W₂ - Z₂‖ ^ 2) := by
  have hs : 0 ≤ s := (norm_nonneg _).trans hZ₁
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_pow_taylor_le_p2 hW₁ hZ₁ a)
      (norm_pow_le_p0 hW₂ b) (norm_nonneg _) (by have := p2_nonneg hs a; positivity))
  · refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_cast_mul_pow_le_p1 hZ₁ a) (norm_nonneg _))) (norm_pow_sub_le_p1 hW₂ hZ₂ b)
      (norm_nonneg _) (mul_nonneg (p1_nonneg hs _) (norm_nonneg _)))
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_pow_le_p0 hZ₁ a)
      (norm_pow_taylor_le_p2 hW₂ hZ₂ b) (norm_nonneg _) (p0_nonneg hs _))

end Powers

/-- `a p₁(s, a−1) = 2 p₂(s, a)`. -/
theorem cast_mul_p1_pred (s : ℝ) (a : ℕ) : (a : ℝ) * p1 s (a - 1) = 2 * p2 s a := by
  unfold p1 p2
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel, show a + 1 - 2 = a - 1 by omega]; push_cast; ring

/-- `a p₀(s, a−1) = p₁(s, a)`. -/
theorem cast_mul_p0_pred (s : ℝ) (a : ℕ) : (a : ℝ) * p0 s (a - 1) = p1 s a := rfl

/-- `‖a y‖ ≤ a ‖y‖` in a normed ring with `‖1‖ = 1`. -/
theorem norm_natCast_mul_le {A : Type*} [NormedRing A] [NormOneClass A] (a : ℕ) (y : A) :
    ‖(a : A) * y‖ ≤ a * ‖y‖ := by
  have hc : ‖(a : A)‖ ≤ a := by simpa using Nat.norm_cast_le (α := A) a
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

/-- A non-negative majorant `C/d^{a+b} · P(a) Q(b)` with scaled sums: if `P(a) dⁱ = dᵃ P'(a)`,
`Q(b) dʲ = dᵇ Q'(b)` and `∑ P' = F`, `∑ Q' = G`, the double series sums to `C F G / d^{i+j}`. -/
theorem hasSum_majorant {C d F G : ℝ} {i j : ℕ} {P Q P' Q' : ℕ → ℝ} (hd : 0 < d)
    (hP : ∀ a, P a * d ^ i = d ^ a * P' a) (hQ : ∀ b, Q b * d ^ j = d ^ b * Q' b)
    (hP0 : ∀ a, 0 ≤ P' a) (hQ0 : ∀ b, 0 ≤ Q' b) (hF : HasSum P' F) (hG : HasSum Q' G) :
    HasSum (fun α : ℕ × ℕ => C / d ^ (α.1 + α.2) * (P α.1 * Q α.2))
      (C * (F * G) / d ^ (i + j)) := by
  have e : (fun α : ℕ × ℕ => C / d ^ (α.1 + α.2) * (P α.1 * Q α.2)) =
      fun α => C * (P' α.1 * Q' α.2) / d ^ (i + j) :=
    funext fun α => scale_mul hd (hP α.1) (hQ α.2)
  rw [e]
  exact ((hasSum_prod_mul hP0 hQ0 hF hG).mul_left C).div_const _

/-- `p₀` in the form required by `hasSum_majorant`. -/
theorem p0_scale' {d : ℝ} (hd : 0 < d) (s : ℝ) (a : ℕ) : p0 s a * d ^ 0 = d ^ a * p0 (s / d) a := by
  rw [pow_zero, mul_one, p0_scale hd]

/-! ## Two-variable power series with Banach-algebra coefficients -/

section Series

variable {A : Type*} [NormedCommRing A] [NormOneClass A] [CompleteSpace A]

/-- **Cauchy-type majorants** `‖c_α‖ ≤ C / d^{|α|}`: the coefficients `c_α = ∂^α X/α!` of a
field `X` analytic and bounded by `C` on a polydisc of radius `d` (around the torus). -/
def Majorized (c : ℕ × ℕ → A) (C d : ℝ) : Prop := ∀ α : ℕ × ℕ, ‖c α‖ ≤ C / d ^ (α.1 + α.2)

/-- The composition `X(K₀ + h) = ∑_α c_α h₁^{α₁} h₂^{α₂}`. -/
def comp (c : ℕ × ℕ → A) (h : A × A) : A := ∑' α : ℕ × ℕ, c α * h.1 ^ α.1 * h.2 ^ α.2

/-- The first partial derivative `∂₁X(K₀ + h) = ∑_α α₁ c_α h₁^{α₁−1} h₂^{α₂}`. -/
def d1 (c : ℕ × ℕ → A) (h : A × A) : A :=
  ∑' α : ℕ × ℕ, (α.1 : A) * c α * h.1 ^ (α.1 - 1) * h.2 ^ α.2

/-- The second partial derivative `∂₂X(K₀ + h) = ∑_α α₂ c_α h₁^{α₁} h₂^{α₂−1}`. -/
def d2 (c : ℕ × ℕ → A) (h : A × A) : A :=
  ∑' α : ℕ × ℕ, (α.2 : A) * c α * h.1 ^ α.1 * h.2 ^ (α.2 - 1)

/-- The derivative `DX(K₀ + h) k = ∂₁X k₁ + ∂₂X k₂`. -/
def dcomp (c : ℕ × ℕ → A) (h k : A × A) : A := d1 c h * k.1 + d2 c h * k.2

variable {c : ℕ × ℕ → A} {C d s : ℝ}

omit [NormOneClass A] [CompleteSpace A] in
/-- The majorant constant is non-negative. -/
theorem Majorized.C_nonneg (hc : Majorized c C d) : 0 ≤ C := by
  have h0 : ‖c (0, 0)‖ ≤ C := by simpa using hc (0, 0)
  exact (norm_nonneg _).trans h0

omit [NormOneClass A] in
/-- Comparison with a summable majorant: summability and the norm bound. -/
theorem summable_and_norm_le {f : ℕ × ℕ → A} {g : ℕ × ℕ → ℝ} {G : ℝ} (hfg : ∀ α, ‖f α‖ ≤ g α)
    (hg : HasSum g G) : Summable f ∧ ‖∑' α, f α‖ ≤ G :=
  ⟨Summable.of_norm_bounded hg.summable hfg, tsum_of_norm_bounded hg hfg⟩

omit [NormOneClass A] [CompleteSpace A] in
/-- `‖c_α‖ X ≤ C/d^{|α|} X` for `X ≥ 0`. -/
theorem Majorized.mul_le (hc : Majorized c C d) (α : ℕ × ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ‖c α‖ * X ≤ C / d ^ (α.1 + α.2) * X := mul_le_mul_of_nonneg_right (hc α) hX

omit [NormOneClass A] [CompleteSpace A] in
/-- `‖c_α Y‖ ≤ C/d^{|α|} B` when `‖Y‖ ≤ B`. -/
theorem Majorized.norm_mul_le (hc : Majorized c C d) (α : ℕ × ℕ) {Y : A} {B : ℝ}
    (hY : ‖Y‖ ≤ B) : ‖c α * Y‖ ≤ C / d ^ (α.1 + α.2) * B :=
  (_root_.norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hY (norm_nonneg _)).trans
    (hc.mul_le α ((norm_nonneg _).trans hY)))

section Bounds

variable (hd : 0 < d) (hc : Majorized c C d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hc hs0 hsd

omit hc in
/-- `0 ≤ s/d < 1`. -/
theorem ratio_mem : 0 ≤ s / d ∧ s / d < 1 :=
  ⟨div_nonneg hs0 hd.le, (div_lt_one hd).2 hsd⟩

/-- Term-wise bound and summability of the composition series for `‖hᵢ‖ ≤ s < d`. -/
theorem comp_summable_and_le {h : A × A} (h1 : ‖h.1‖ ≤ s) (h2 : ‖h.2‖ ≤ s) :
    Summable (fun α : ℕ × ℕ => c α * h.1 ^ α.1 * h.2 ^ α.2) ∧
      ‖comp c h‖ ≤ C / (1 - s / d) ^ 2 := by
  obtain ⟨hx0, hx1⟩ := ratio_mem hd hs0 hsd
  have hg := hasSum_majorant (C := C) hd (p0_scale' hd s) (p0_scale' hd s) (p0_nonneg hx0)
    (p0_nonneg hx0) (hasSum_p0 hx0 hx1) (hasSum_p0 hx0 hx1)
  have hb : ∀ α : ℕ × ℕ, ‖c α * h.1 ^ α.1 * h.2 ^ α.2‖ ≤
      C / d ^ (α.1 + α.2) * (p0 s α.1 * p0 s α.2) := fun α => by
    rw [mul_assoc]
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (mul_le_mul
      (norm_pow_le_p0 h1 _) (norm_pow_le_p0 h2 _) (norm_nonneg _) (p0_nonneg hs0 _)))
      (norm_nonneg _)).trans ?_
    exact hc.mul_le α (mul_nonneg (p0_nonneg hs0 _) (p0_nonneg hs0 _))
  obtain ⟨hsum, hle⟩ := summable_and_norm_le hb hg
  refine ⟨hsum, hle.trans (le_of_eq ?_)⟩
  have : 1 - s / d ≠ 0 := by linarith
  field_simp
  simp

/-- Bound and summability of the `∂₁` series: `‖∂₁X(K₀ + h)‖ ≤ C/(d(1 − s/d)³)`. -/
theorem d1_summable_and_le {h : A × A} (h1 : ‖h.1‖ ≤ s) (h2 : ‖h.2‖ ≤ s) :
    Summable (fun α : ℕ × ℕ => (α.1 : A) * c α * h.1 ^ (α.1 - 1) * h.2 ^ α.2) ∧
      ‖d1 c h‖ ≤ C / (d * (1 - s / d) ^ 3) := by
  obtain ⟨hx0, hx1⟩ := ratio_mem hd hs0 hsd
  have hg := hasSum_majorant (C := C) hd (p1_scale hd s) (p0_scale' hd s) (p1_nonneg hx0)
    (p0_nonneg hx0) (hasSum_p1 hx0 hx1) (hasSum_p0 hx0 hx1)
  have hb : ∀ α : ℕ × ℕ, ‖(α.1 : A) * c α * h.1 ^ (α.1 - 1) * h.2 ^ α.2‖ ≤
      C / d ^ (α.1 + α.2) * (p1 s α.1 * p0 s α.2) := fun α => by
    rw [show (α.1 : A) * c α * h.1 ^ (α.1 - 1) * h.2 ^ α.2 =
      c α * ((α.1 : A) * h.1 ^ (α.1 - 1) * h.2 ^ α.2) by ring]
    exact hc.norm_mul_le α ((norm_mul_le _ _).trans (mul_le_mul (norm_cast_mul_pow_le_p1 h1 _)
      (norm_pow_le_p0 h2 _) (norm_nonneg _) (p1_nonneg hs0 _)))
  obtain ⟨hsum, hle⟩ := summable_and_norm_le hb hg
  refine ⟨hsum, hle.trans (le_of_eq ?_)⟩
  have : 1 - s / d ≠ 0 := by linarith
  field_simp; ring

/-- Bound and summability of the `∂₂` series: `‖∂₂X(K₀ + h)‖ ≤ C/(d(1 − s/d)³)`. -/
theorem d2_summable_and_le {h : A × A} (h1 : ‖h.1‖ ≤ s) (h2 : ‖h.2‖ ≤ s) :
    Summable (fun α : ℕ × ℕ => (α.2 : A) * c α * h.1 ^ α.1 * h.2 ^ (α.2 - 1)) ∧
      ‖d2 c h‖ ≤ C / (d * (1 - s / d) ^ 3) := by
  obtain ⟨hx0, hx1⟩ := ratio_mem hd hs0 hsd
  have hg := hasSum_majorant (C := C) hd (p0_scale' hd s) (p1_scale hd s) (p0_nonneg hx0)
    (p1_nonneg hx0) (hasSum_p0 hx0 hx1) (hasSum_p1 hx0 hx1)
  have hb : ∀ α : ℕ × ℕ, ‖(α.2 : A) * c α * h.1 ^ α.1 * h.2 ^ (α.2 - 1)‖ ≤
      C / d ^ (α.1 + α.2) * (p0 s α.1 * p1 s α.2) := fun α => by
    rw [show (α.2 : A) * c α * h.1 ^ α.1 * h.2 ^ (α.2 - 1) =
      c α * (h.1 ^ α.1 * ((α.2 : A) * h.2 ^ (α.2 - 1))) by ring]
    exact hc.norm_mul_le α ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le_p0 h1 _)
      (norm_cast_mul_pow_le_p1 h2 _) (norm_nonneg _) (p0_nonneg hs0 _)))
  obtain ⟨hsum, hle⟩ := summable_and_norm_le hb hg
  refine ⟨hsum, hle.trans (le_of_eq ?_)⟩
  have : 1 - s / d ≠ 0 := by linarith
  field_simp; ring

/-- **Lipschitz bound** for the composition: for `‖hᵢ‖ + ‖kᵢ‖ ≤ s < d`,
`‖X(K₀ + h + k) − X(K₀ + h)‖ ≤ M₁ (‖k₁‖ + ‖k₂‖)` with `M₁ = C/(d(1 − s/d)³)`. -/
theorem norm_comp_sub_le {h k : A × A} (h1 : ‖h.1‖ + ‖k.1‖ ≤ s) (h2 : ‖h.2‖ + ‖k.2‖ ≤ s) :
    ‖comp c (h + k) - comp c h‖ ≤ C / (d * (1 - s / d) ^ 3) * (‖k.1‖ + ‖k.2‖) := by
  obtain ⟨hx0, hx1⟩ := ratio_mem hd hs0 hsd
  have hZ1 : ‖h.1‖ ≤ s := by linarith [norm_nonneg k.1]
  have hZ2 : ‖h.2‖ ≤ s := by linarith [norm_nonneg k.2]
  have hW1 : ‖(h + k).1‖ ≤ s := (norm_add_le _ _).trans h1
  have hW2 : ‖(h + k).2‖ ≤ s := (norm_add_le _ _).trans h2
  obtain ⟨sW, -⟩ := comp_summable_and_le hd hc hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := comp_summable_and_le hd hc hs0 hsd hZ1 hZ2
  have e : comp c (h + k) - comp c h = ∑' α : ℕ × ℕ,
      c α * ((h + k).1 ^ α.1 * (h + k).2 ^ α.2 - h.1 ^ α.1 * h.2 ^ α.2) := by
    rw [comp, comp, ← sW.tsum_sub sZ]
    exact tsum_congr fun α => by ring
  have hg1 := hasSum_majorant (C := C) hd (p1_scale hd s) (p0_scale' hd s) (p1_nonneg hx0)
    (p0_nonneg hx0) (hasSum_p1 hx0 hx1) (hasSum_p0 hx0 hx1)
  have hg2 := hasSum_majorant (C := C) hd (p0_scale' hd s) (p1_scale hd s) (p0_nonneg hx0)
    (p1_nonneg hx0) (hasSum_p0 hx0 hx1) (hasSum_p1 hx0 hx1)
  have hg := (hg1.mul_right ‖k.1‖).add (hg2.mul_right ‖k.2‖)
  have hb : ∀ α : ℕ × ℕ, ‖c α * ((h + k).1 ^ α.1 * (h + k).2 ^ α.2 - h.1 ^ α.1 * h.2 ^ α.2)‖ ≤
      C / d ^ (α.1 + α.2) * (p1 s α.1 * p0 s α.2) * ‖k.1‖ +
        C / d ^ (α.1 + α.2) * (p0 s α.1 * p1 s α.2) * ‖k.2‖ := fun α => by
    refine (hc.norm_mul_le α (norm_mono_sub_le hZ1 hZ2 hW1 hW2 α.1 α.2)).trans (le_of_eq ?_)
    simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_left]; ring
  rw [e]
  refine (summable_and_norm_le hb hg).2.trans (le_of_eq ?_)
  have : 1 - s / d ≠ 0 := by linarith
  field_simp; ring

/-- **Second-order Taylor estimate** (`comp_taylor`): for `‖hᵢ‖ + ‖kᵢ‖ ≤ s < d`,
`‖X(K₀ + h + k) − X(K₀ + h) − DX(K₀ + h) k‖ ≤ ½ M₂ (‖k₁‖ + ‖k₂‖)²` with
`½ M₂ = C/(d²(1 − s/d)⁴)` (`= 16 C/d²` at `s = d/2`). -/
theorem comp_taylor {h k : A × A} (h1 : ‖h.1‖ + ‖k.1‖ ≤ s) (h2 : ‖h.2‖ + ‖k.2‖ ≤ s) :
    ‖comp c (h + k) - comp c h - dcomp c h k‖ ≤
      C / (d ^ 2 * (1 - s / d) ^ 4) * (‖k.1‖ + ‖k.2‖) ^ 2 := by
  obtain ⟨hx0, hx1⟩ := ratio_mem hd hs0 hsd
  have hZ1 : ‖h.1‖ ≤ s := by linarith [norm_nonneg k.1]
  have hZ2 : ‖h.2‖ ≤ s := by linarith [norm_nonneg k.2]
  have hW1 : ‖(h + k).1‖ ≤ s := (norm_add_le _ _).trans h1
  have hW2 : ‖(h + k).2‖ ≤ s := (norm_add_le _ _).trans h2
  obtain ⟨sW, -⟩ := comp_summable_and_le hd hc hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := comp_summable_and_le hd hc hs0 hsd hZ1 hZ2
  obtain ⟨sD1, -⟩ := d1_summable_and_le hd hc hs0 hsd hZ1 hZ2
  obtain ⟨sD2, -⟩ := d2_summable_and_le hd hc hs0 hsd hZ1 hZ2
  set W := h + k
  have e : comp c W - comp c h - dcomp c h k = ∑' α : ℕ × ℕ, c α *
      ((W.1 ^ α.1 - h.1 ^ α.1 - (α.1 : A) * h.1 ^ (α.1 - 1) * (W.1 - h.1)) * W.2 ^ α.2 +
        (α.1 : A) * h.1 ^ (α.1 - 1) * (W.1 - h.1) * (W.2 ^ α.2 - h.2 ^ α.2) +
        h.1 ^ α.1 * (W.2 ^ α.2 - h.2 ^ α.2 - (α.2 : A) * h.2 ^ (α.2 - 1) * (W.2 - h.2))) := by
    have hs := (sW.hasSum.sub sZ.hasSum).sub
      ((sD1.hasSum.mul_right k.1).add (sD2.hasSum.mul_right k.2))
    rw [comp, comp, dcomp, d1, d2, ← hs.tsum_eq]
    refine tsum_congr fun α => ?_
    have hk1 : k.1 = W.1 - h.1 := by simp [W]
    have hk2 : k.2 = W.2 - h.2 := by simp [W]
    rw [hk1, hk2]; ring
  have hg1 := hasSum_majorant (C := C) hd (p2_scale hd s) (p0_scale' hd s) (p2_nonneg hx0)
    (p0_nonneg hx0) (hasSum_p2 hx0 hx1) (hasSum_p0 hx0 hx1)
  have hg2 := hasSum_majorant (C := C) hd (p1_scale hd s) (p1_scale hd s) (p1_nonneg hx0)
    (p1_nonneg hx0) (hasSum_p1 hx0 hx1) (hasSum_p1 hx0 hx1)
  have hg3 := hasSum_majorant (C := C) hd (p0_scale' hd s) (p2_scale hd s) (p0_nonneg hx0)
    (p2_nonneg hx0) (hasSum_p0 hx0 hx1) (hasSum_p2 hx0 hx1)
  have hg := ((hg1.mul_right (‖k.1‖ ^ 2)).add (hg2.mul_right (‖k.1‖ * ‖k.2‖))).add
    (hg3.mul_right (‖k.2‖ ^ 2))
  have hW1k : W.1 - h.1 = k.1 := by simp [W]
  have hW2k : W.2 - h.2 = k.2 := by simp [W]
  rw [e]
  refine (summable_and_norm_le (fun α => (hc.norm_mul_le α
    (norm_mono_taylor_le hZ1 hZ2 hW1 hW2 α.1 α.2)).trans (le_of_eq ?_)) hg).2.trans ?_
  · rw [hW1k, hW2k]; ring
  · have h1x : 0 < 1 - s / d := by linarith
    have hC := hc.C_nonneg
    have ht : 0 ≤ ‖k.1‖ * ‖k.2‖ := by positivity
    have hK : 0 ≤ C / (d ^ 2 * (1 - s / d) ^ 4) := by positivity
    have e2 : C * (1 / (1 - s / d) ^ 3 * (1 / (1 - s / d))) / d ^ (2 + 0) * ‖k.1‖ ^ 2 +
        C * (1 / (1 - s / d) ^ 2 * (1 / (1 - s / d) ^ 2)) / d ^ (1 + 1) * (‖k.1‖ * ‖k.2‖) +
        C * (1 / (1 - s / d) * (1 / (1 - s / d) ^ 3)) / d ^ (0 + 2) * ‖k.2‖ ^ 2 =
        C / (d ^ 2 * (1 - s / d) ^ 4) * (‖k.1‖ ^ 2 + ‖k.1‖ * ‖k.2‖ + ‖k.2‖ ^ 2) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hK

/-- **Lipschitz bound for `∂₁X`**: for `‖hᵢ‖ + ‖kᵢ‖ ≤ s < d`,
`‖∂₁X(K₀ + h + k) − ∂₁X(K₀ + h)‖ ≤ M₂ (‖k₁‖ + ‖k₂‖)` with `M₂ = 2C/(d²(1 − s/d)⁴)`. -/
theorem norm_d1_sub_le {h k : A × A} (h1 : ‖h.1‖ + ‖k.1‖ ≤ s) (h2 : ‖h.2‖ + ‖k.2‖ ≤ s) :
    ‖d1 c (h + k) - d1 c h‖ ≤ 2 * C / (d ^ 2 * (1 - s / d) ^ 4) * (‖k.1‖ + ‖k.2‖) := by
  obtain ⟨hx0, hx1⟩ := ratio_mem hd hs0 hsd
  have hZ1 : ‖h.1‖ ≤ s := by linarith [norm_nonneg k.1]
  have hZ2 : ‖h.2‖ ≤ s := by linarith [norm_nonneg k.2]
  have hW1 : ‖(h + k).1‖ ≤ s := (norm_add_le _ _).trans h1
  have hW2 : ‖(h + k).2‖ ≤ s := (norm_add_le _ _).trans h2
  obtain ⟨sW, -⟩ := d1_summable_and_le hd hc hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := d1_summable_and_le hd hc hs0 hsd hZ1 hZ2
  have e : d1 c (h + k) - d1 c h = ∑' α : ℕ × ℕ, c α * ((α.1 : A) *
      ((h + k).1 ^ (α.1 - 1) * (h + k).2 ^ α.2 - h.1 ^ (α.1 - 1) * h.2 ^ α.2)) := by
    rw [d1, d1, ← sW.tsum_sub sZ]
    exact tsum_congr fun α => by ring
  have hg1 := hasSum_majorant (C := C) hd (p2_scale hd s) (p0_scale' hd s) (p2_nonneg hx0)
    (p0_nonneg hx0) (hasSum_p2 hx0 hx1) (hasSum_p0 hx0 hx1)
  have hg2 := hasSum_majorant (C := C) hd (p1_scale hd s) (p1_scale hd s) (p1_nonneg hx0)
    (p1_nonneg hx0) (hasSum_p1 hx0 hx1) (hasSum_p1 hx0 hx1)
  have hg := (hg1.mul_right (2 * ‖k.1‖)).add (hg2.mul_right ‖k.2‖)
  have hb : ∀ α : ℕ × ℕ, ‖c α * ((α.1 : A) *
      ((h + k).1 ^ (α.1 - 1) * (h + k).2 ^ α.2 - h.1 ^ (α.1 - 1) * h.2 ^ α.2))‖ ≤
      C / d ^ (α.1 + α.2) * (p2 s α.1 * p0 s α.2) * (2 * ‖k.1‖) +
        C / d ^ (α.1 + α.2) * (p1 s α.1 * p1 s α.2) * ‖k.2‖ := fun α => by
    refine (hc.norm_mul_le α ((norm_natCast_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_mono_sub_le hZ1 hZ2 hW1 hW2 (α.1 - 1) α.2) (Nat.cast_nonneg _)))).trans
      (le_of_eq ?_)
    simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_left]
    have e1 := cast_mul_p1_pred s α.1
    have e0 := cast_mul_p0_pred s α.1
    linear_combination (C / d ^ (α.1 + α.2) * ‖k.1‖ * p0 s α.2) * e1 +
      (C / d ^ (α.1 + α.2) * p1 s α.2 * ‖k.2‖) * e0
  rw [e]
  refine (summable_and_norm_le hb hg).2.trans ?_
  have h1x : 0 < 1 - s / d := by linarith
  have hC := hc.C_nonneg
  have e2 : C * (1 / (1 - s / d) ^ 3 * (1 / (1 - s / d))) / d ^ (2 + 0) * (2 * ‖k.1‖) +
      C * (1 / (1 - s / d) ^ 2 * (1 / (1 - s / d) ^ 2)) / d ^ (1 + 1) * ‖k.2‖ =
      C / (d ^ 2 * (1 - s / d) ^ 4) * (2 * ‖k.1‖ + ‖k.2‖) := by
    field_simp
  have hK : 0 ≤ C / (d ^ 2 * (1 - s / d) ^ 4) := by positivity
  calc _ = C / (d ^ 2 * (1 - s / d) ^ 4) * (2 * ‖k.1‖ + ‖k.2‖) := e2
    _ ≤ C / (d ^ 2 * (1 - s / d) ^ 4) * (2 * (‖k.1‖ + ‖k.2‖)) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg k.1, norm_nonneg k.2]) hK
    _ = _ := by ring

/-- **Lipschitz bound for `∂₂X`**: for `‖hᵢ‖ + ‖kᵢ‖ ≤ s < d`,
`‖∂₂X(K₀ + h + k) − ∂₂X(K₀ + h)‖ ≤ M₂ (‖k₁‖ + ‖k₂‖)` with `M₂ = 2C/(d²(1 − s/d)⁴)`. -/
theorem norm_d2_sub_le {h k : A × A} (h1 : ‖h.1‖ + ‖k.1‖ ≤ s) (h2 : ‖h.2‖ + ‖k.2‖ ≤ s) :
    ‖d2 c (h + k) - d2 c h‖ ≤ 2 * C / (d ^ 2 * (1 - s / d) ^ 4) * (‖k.1‖ + ‖k.2‖) := by
  obtain ⟨hx0, hx1⟩ := ratio_mem hd hs0 hsd
  have hZ1 : ‖h.1‖ ≤ s := by linarith [norm_nonneg k.1]
  have hZ2 : ‖h.2‖ ≤ s := by linarith [norm_nonneg k.2]
  have hW1 : ‖(h + k).1‖ ≤ s := (norm_add_le _ _).trans h1
  have hW2 : ‖(h + k).2‖ ≤ s := (norm_add_le _ _).trans h2
  obtain ⟨sW, -⟩ := d2_summable_and_le hd hc hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := d2_summable_and_le hd hc hs0 hsd hZ1 hZ2
  have e : d2 c (h + k) - d2 c h = ∑' α : ℕ × ℕ, c α * ((α.2 : A) *
      ((h + k).1 ^ α.1 * (h + k).2 ^ (α.2 - 1) - h.1 ^ α.1 * h.2 ^ (α.2 - 1))) := by
    rw [d2, d2, ← sW.tsum_sub sZ]
    exact tsum_congr fun α => by ring
  have hg1 := hasSum_majorant (C := C) hd (p1_scale hd s) (p1_scale hd s) (p1_nonneg hx0)
    (p1_nonneg hx0) (hasSum_p1 hx0 hx1) (hasSum_p1 hx0 hx1)
  have hg2 := hasSum_majorant (C := C) hd (p0_scale' hd s) (p2_scale hd s) (p0_nonneg hx0)
    (p2_nonneg hx0) (hasSum_p0 hx0 hx1) (hasSum_p2 hx0 hx1)
  have hg := (hg1.mul_right ‖k.1‖).add (hg2.mul_right (2 * ‖k.2‖))
  have hb : ∀ α : ℕ × ℕ, ‖c α * ((α.2 : A) *
      ((h + k).1 ^ α.1 * (h + k).2 ^ (α.2 - 1) - h.1 ^ α.1 * h.2 ^ (α.2 - 1)))‖ ≤
      C / d ^ (α.1 + α.2) * (p1 s α.1 * p1 s α.2) * ‖k.1‖ +
        C / d ^ (α.1 + α.2) * (p0 s α.1 * p2 s α.2) * (2 * ‖k.2‖) := fun α => by
    refine (hc.norm_mul_le α ((norm_natCast_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_mono_sub_le hZ1 hZ2 hW1 hW2 α.1 (α.2 - 1)) (Nat.cast_nonneg _)))).trans
      (le_of_eq ?_)
    simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_left]
    have e1 := cast_mul_p1_pred s α.2
    have e0 := cast_mul_p0_pred s α.2
    linear_combination (C / d ^ (α.1 + α.2) * ‖k.1‖ * p1 s α.1) * e0 +
      (C / d ^ (α.1 + α.2) * p0 s α.1 * ‖k.2‖) * e1
  rw [e]
  refine (summable_and_norm_le hb hg).2.trans ?_
  have h1x : 0 < 1 - s / d := by linarith
  have hC := hc.C_nonneg
  have e2 : C * (1 / (1 - s / d) ^ 2 * (1 / (1 - s / d) ^ 2)) / d ^ (1 + 1) * ‖k.1‖ +
      C * (1 / (1 - s / d) * (1 / (1 - s / d) ^ 3)) / d ^ (0 + 2) * (2 * ‖k.2‖) =
      C / (d ^ 2 * (1 - s / d) ^ 4) * (‖k.1‖ + 2 * ‖k.2‖) := by
    field_simp
  have hK : 0 ≤ C / (d ^ 2 * (1 - s / d) ^ 4) := by positivity
  calc _ = C / (d ^ 2 * (1 - s / d) ^ 4) * (‖k.1‖ + 2 * ‖k.2‖) := e2
    _ ≤ C / (d ^ 2 * (1 - s / d) ^ 4) * (2 * (‖k.1‖ + ‖k.2‖)) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg k.1, norm_nonneg k.2]) hK
    _ = _ := by ring

end Bounds

/-! ### Sanity checks -/

omit [NormOneClass A] [CompleteSpace A] in
/-- Sanity: the zero series composes to `0`. -/
theorem comp_zero_series (h : A × A) : comp (fun _ => (0 : A)) h = 0 := by simp [comp]

omit [NormOneClass A] [CompleteSpace A] in
/-- Sanity: at `h = 0` the composition is the constant coefficient `c₀₀ = X(K₀)`. -/
theorem comp_zero (c : ℕ × ℕ → A) : comp c 0 = c (0, 0) := by
  rw [comp, tsum_eq_single (0, 0)]
  · simp
  · rintro ⟨a, b⟩ hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have hb : b ≠ 0 := by rintro rfl; exact hab rfl
      simp [zero_pow hb]
    · simp [zero_pow ha.ne']

omit [NormOneClass A] [CompleteSpace A] in
/-- Sanity: a single monomial `e z₁ᵃ z₂ᵇ` composes to `e h₁ᵃ h₂ᵇ` (the polynomial case). -/
theorem comp_monomial (e : A) (a b : ℕ) (h : A × A) :
    comp (fun α => if α = (a, b) then e else 0) h = e * h.1 ^ a * h.2 ^ b := by
  rw [comp, tsum_eq_single (a, b)]
  · simp
  · intro α hα; simp [hα]

omit [NormOneClass A] [CompleteSpace A] in
/-- Sanity: a series with only `c₀₀ = e` is the constant `e`. -/
theorem comp_const (e : A) (h : A × A) :
    comp (fun α => if α = (0, 0) then e else 0) h = e := by
  rw [comp_monomial]; simp

/-- Rejected fixture: the radius condition `‖hᵢ‖ < d` cannot be dropped. The coefficients
`c_α = 1` are majorized with `C = d = 1`, but at `h = (1, 0)` the series diverges. -/
theorem not_summable_at_radius :
    Majorized (fun _ : ℕ × ℕ => (1 : ℂ)) 1 1 ∧
      ¬ Summable (fun α : ℕ × ℕ => (1 : ℂ) * (1 : ℂ) ^ α.1 * (0 : ℂ) ^ α.2) := by
  refine ⟨fun α => by simp, fun hs => ?_⟩
  have hinj : Function.Injective (fun a : ℕ => ((a, 0) : ℕ × ℕ)) := fun a b h => by
    simpa using h
  have := hs.comp_injective hinj
  simp only [Function.comp_def, one_pow, mul_one, pow_zero] at this
  exact one_ne_zero ((summable_const_iff 1).1 this)

end Series

/-! ## The torus algebra: strip bounds and evaluation -/

section Torus

open WEll1Z2

variable {ρ : ℝ}

/-- `toFA` commutes with convergent sums. -/
theorem toFA_tsum (hρ : 0 ≤ ρ) [Fact (0 ≤ ρ)] {f : ℕ × ℕ → WEll1Z2 ρ} (hf : Summable f) :
    toFA hρ (∑' α, f α) = ∑' α, toFA hρ (f α) :=
  ((hf.hasSum.map (toFA hρ) (continuous_toFA hρ)).tsum_eq).symm

/-- Lifting a strip bound to `ℓ¹_ρ(ℤ²)`. -/
theorem exists_lift (hρ : 0 ≤ ρ) [Fact (0 ≤ ρ)] {x : FA} {B : ℝ} (hx : Bd ρ x B) :
    ∃ y : WEll1Z2 ρ, toFA hρ y = x ∧ ‖y‖ ≤ B :=
  ⟨liftS x hx.1, toFA_liftS hρ x hx.1, by rw [norm_liftS]; exact hx.2⟩

variable {c : ℕ × ℕ → FA} {C d s : ℝ}

/-- Lifted data: majorized coefficients and a lifted argument. -/
theorem lift_series (hρ : 0 ≤ ρ) [Fact (0 ≤ ρ)]
    (hc : ∀ α : ℕ × ℕ, Bd ρ (c α) (C / d ^ (α.1 + α.2))) :
    ∃ cl : ℕ × ℕ → WEll1Z2 ρ, c = (fun α => toFA hρ (cl α)) ∧ Majorized cl C d := by
  choose cl h1 h2 using fun α => exists_lift hρ (hc α)
  exact ⟨cl, funext fun α => (h1 α).symm, h2⟩

/-- `toFA` commutes with the composition series (on its convergence domain). -/
theorem toFA_comp (hρ : 0 ≤ ρ) [Fact (0 ≤ ρ)] (cl : ℕ × ℕ → WEll1Z2 ρ) (h : WEll1Z2 ρ × WEll1Z2 ρ)
    (hs : Summable fun α : ℕ × ℕ => cl α * h.1 ^ α.1 * h.2 ^ α.2) :
    toFA hρ (comp cl h) = comp (fun α => toFA hρ (cl α)) (toFA hρ h.1, toFA hρ h.2) := by
  rw [comp, toFA_tsum hρ hs, comp]; simp

/-- `toFA` commutes with the `∂₁` series. -/
theorem toFA_d1 (hρ : 0 ≤ ρ) [Fact (0 ≤ ρ)] (cl : ℕ × ℕ → WEll1Z2 ρ) (h : WEll1Z2 ρ × WEll1Z2 ρ)
    (hs : Summable fun α : ℕ × ℕ => (α.1 : WEll1Z2 ρ) * cl α * h.1 ^ (α.1 - 1) * h.2 ^ α.2) :
    toFA hρ (d1 cl h) = d1 (fun α => toFA hρ (cl α)) (toFA hρ h.1, toFA hρ h.2) := by
  rw [d1, toFA_tsum hρ hs, d1]; simp

/-- `toFA` commutes with the `∂₂` series. -/
theorem toFA_d2 (hρ : 0 ≤ ρ) [Fact (0 ≤ ρ)] (cl : ℕ × ℕ → WEll1Z2 ρ) (h : WEll1Z2 ρ × WEll1Z2 ρ)
    (hs : Summable fun α : ℕ × ℕ => (α.2 : WEll1Z2 ρ) * cl α * h.1 ^ α.1 * h.2 ^ (α.2 - 1)) :
    toFA hρ (d2 cl h) = d2 (fun α => toFA hρ (cl α)) (toFA hρ h.1, toFA hρ h.2) := by
  rw [d2, toFA_tsum hρ hs, d2]; simp

section BdBounds

variable (hρ : 0 ≤ ρ) (hd : 0 < d) (hc : ∀ α : ℕ × ℕ, Bd ρ (c α) (C / d ^ (α.1 + α.2)))
  (hs0 : 0 ≤ s) (hsd : s < d)
include hρ hd hc hs0 hsd

/-- **Strip bound of the composition**: `Bd ρ hᵢ s`, `s < d` give
`Bd ρ (X(K₀ + h)) (C/(1 − s/d)²)`. -/
theorem bd_comp {h₁ h₂ : FA} (h1 : Bd ρ h₁ s) (h2 : Bd ρ h₂ s) :
    Bd ρ (comp c (h₁, h₂)) (C / (1 - s / d) ^ 2) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨cl, rfl, hcl⟩ := lift_series hρ hc
  obtain ⟨l₁, rfl, n₁⟩ := exists_lift hρ h1
  obtain ⟨l₂, rfl, n₂⟩ := exists_lift hρ h2
  obtain ⟨hs, hle⟩ := comp_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd n₁ n₂
  rw [← toFA_comp hρ cl (l₁, l₂) hs]
  exact (Bd_toFA hρ _).le hle

/-- **Strip bound of `∂₁X`**: `Bd ρ (∂₁X(K₀ + h)) (C/(d(1 − s/d)³))`. -/
theorem bd_d1 {h₁ h₂ : FA} (h1 : Bd ρ h₁ s) (h2 : Bd ρ h₂ s) :
    Bd ρ (d1 c (h₁, h₂)) (C / (d * (1 - s / d) ^ 3)) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨cl, rfl, hcl⟩ := lift_series hρ hc
  obtain ⟨l₁, rfl, n₁⟩ := exists_lift hρ h1
  obtain ⟨l₂, rfl, n₂⟩ := exists_lift hρ h2
  obtain ⟨hs, hle⟩ := d1_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd n₁ n₂
  rw [← toFA_d1 hρ cl (l₁, l₂) hs]
  exact (Bd_toFA hρ _).le hle

/-- **Strip bound of `∂₂X`**: `Bd ρ (∂₂X(K₀ + h)) (C/(d(1 − s/d)³))`. -/
theorem bd_d2 {h₁ h₂ : FA} (h1 : Bd ρ h₁ s) (h2 : Bd ρ h₂ s) :
    Bd ρ (d2 c (h₁, h₂)) (C / (d * (1 - s / d) ^ 3)) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨cl, rfl, hcl⟩ := lift_series hρ hc
  obtain ⟨l₁, rfl, n₁⟩ := exists_lift hρ h1
  obtain ⟨l₂, rfl, n₂⟩ := exists_lift hρ h2
  obtain ⟨hs, hle⟩ := d2_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd n₁ n₂
  rw [← toFA_d2 hρ cl (l₁, l₂) hs]
  exact (Bd_toFA hρ _).le hle

/-- **Strip Taylor estimate** (`comp_taylor` in `Bd ρ` form): with `Bd ρ hᵢ bᵢ`,
`Bd ρ kᵢ tᵢ`, `bᵢ + tᵢ ≤ s < d`,
`Bd ρ (X(K₀ + h + k) − X(K₀ + h) − DX(K₀ + h) k) (C/(d²(1 − s/d)⁴) · (t₁ + t₂)²)`. -/
theorem bd_comp_taylor {h₁ h₂ k₁ k₂ : FA} {b₁ b₂ t₁ t₂ : ℝ} (h1 : Bd ρ h₁ b₁) (h2 : Bd ρ h₂ b₂)
    (k1 : Bd ρ k₁ t₁) (k2 : Bd ρ k₂ t₂) (hb₁ : b₁ + t₁ ≤ s) (hb₂ : b₂ + t₂ ≤ s) :
    Bd ρ (comp c (h₁ + k₁, h₂ + k₂) - comp c (h₁, h₂) - dcomp c (h₁, h₂) (k₁, k₂))
      (C / (d ^ 2 * (1 - s / d) ^ 4) * (t₁ + t₂) ^ 2) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  obtain ⟨cl, rfl, hcl⟩ := lift_series hρ hc
  obtain ⟨l₁, rfl, n₁⟩ := exists_lift hρ h1
  obtain ⟨l₂, rfl, n₂⟩ := exists_lift hρ h2
  obtain ⟨m₁, rfl, o₁⟩ := exists_lift hρ k1
  obtain ⟨m₂, rfl, o₂⟩ := exists_lift hρ k2
  have q1 : ‖(l₁, l₂).1‖ + ‖(m₁, m₂).1‖ ≤ s := by simp only; linarith
  have q2 : ‖(l₁, l₂).2‖ + ‖(m₁, m₂).2‖ ≤ s := by simp only; linarith
  have hZ1 : ‖l₁‖ ≤ s := by linarith [norm_nonneg m₁]
  have hZ2 : ‖l₂‖ ≤ s := by linarith [norm_nonneg m₂]
  have hW1 : ‖l₁ + m₁‖ ≤ s := (norm_add_le _ _).trans q1
  have hW2 : ‖l₂ + m₂‖ ≤ s := (norm_add_le _ _).trans q2
  obtain ⟨sW, -⟩ := comp_summable_and_le (h := (l₁ + m₁, l₂ + m₂)) hd hcl hs0 hsd hW1 hW2
  obtain ⟨sZ, -⟩ := comp_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd hZ1 hZ2
  obtain ⟨sD1, -⟩ := d1_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd hZ1 hZ2
  obtain ⟨sD2, -⟩ := d2_summable_and_le (h := (l₁, l₂)) hd hcl hs0 hsd hZ1 hZ2
  have e : comp (fun α => toFA hρ (cl α)) (toFA hρ l₁ + toFA hρ m₁, toFA hρ l₂ + toFA hρ m₂) -
      comp (fun α => toFA hρ (cl α)) (toFA hρ l₁, toFA hρ l₂) -
      dcomp (fun α => toFA hρ (cl α)) (toFA hρ l₁, toFA hρ l₂) (toFA hρ m₁, toFA hρ m₂) =
      toFA hρ (comp cl ((l₁, l₂) + (m₁, m₂)) - comp cl (l₁, l₂) - dcomp cl (l₁, l₂) (m₁, m₂)) := by
    rw [map_sub, map_sub, dcomp, dcomp, map_add, map_mul, map_mul,
      toFA_d1 hρ cl _ sD1, toFA_d2 hρ cl _ sD2, toFA_comp hρ cl _ sZ,
      Prod.mk_add_mk, toFA_comp hρ cl _ sW, map_add, map_add]
  rw [e]
  refine (Bd_toFA hρ _).le ((comp_taylor hd hcl hs0 hsd q1 q2).trans ?_)
  have hK : 0 ≤ C / (d ^ 2 * (1 - s / d) ^ 4) := by
    have := (show 0 < 1 - s / d by rw [sub_pos, div_lt_one hd]; exact hsd)
    have hC := hcl.C_nonneg
    positivity
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 2) hK
  simp only; linarith

end BdBounds

/-! ### Analytic fields along a torus -/

/-- **An analytic field along the torus** (the interface replacing `PolyExpr`). For a field
`X` analytic and bounded by `C` on the polydiscs of radius `d` around the torus image, written
in local form `X θ ψ z₁ z₂ = X(K₀₁(θ,ψ) + z₁, K₀₂(θ,ψ) + z₂, ψ)`, the Taylor coefficients
`c_α(θ,ψ) = ∂^α X(K₀(θ,ψ), ψ)/α!` are elements of the strip algebra with Cauchy majorants
`‖c_α‖_ρ ≤ C/d^{|α|}`, and the Taylor series converges pointwise to `X`. -/
structure AnaFieldAt (ρ C d : ℝ) (X : ℝ → ℝ → ℂ → ℂ → ℂ) where
  /-- The Taylor coefficients along the torus. -/
  c : ℕ × ℕ → FA
  /-- The Cauchy majorants in the strip norm. -/
  bound : ∀ α : ℕ × ℕ, Bd ρ (c α) (C / d ^ (α.1 + α.2))
  /-- Pointwise convergence of the Taylor series to the field. -/
  hasSum_eval : ∀ (θ ψ : ℝ) (z₁ z₂ : ℂ), ‖z₁‖ < d → ‖z₂‖ < d →
    HasSum (fun α : ℕ × ℕ => WEll1Z2.eval (c α) θ ψ * z₁ ^ α.1 * z₂ ^ α.2) (X θ ψ z₁ z₂)

/-- The composition `X ∘ (K₀ + h)` as an element of the strip algebra. -/
def AnaFieldAt.compFA {ρ C d : ℝ} {X : ℝ → ℝ → ℂ → ℂ → ℂ} (F : AnaFieldAt ρ C d X)
    (h : FA × FA) : FA := comp F.c h

/-- Evaluation at a point is continuous on `𝔸` (it is bounded by the norm). -/
theorem continuous_evalHom (θ ψ : ℝ) : Continuous (evalHom θ ψ) :=
  AddMonoidHomClass.continuous_of_bound (evalHom θ ψ) 1 fun x => by
    rw [one_mul, norm_eq_wnorm]
    exact (norm_fourierSum_le le_rfl (inWeighted_coeff x) θ ψ).1

/-- A strip bound bounds the values on the real torus. -/
theorem norm_eval_le_of_Bd (hρ : 0 ≤ ρ) {x : FA} {B : ℝ} (hx : Bd ρ x B) (θ ψ : ℝ) :
    ‖WEll1Z2.eval x θ ψ‖ ≤ B := by
  obtain ⟨h1, h2⟩ := norm_fourierSum_le hρ hx.1 θ ψ
  exact h1.trans (h2.trans hx.2)

/-- **The composition evaluates to the field**: for `Bd ρ hᵢ b` with `b < d`,
`(X ∘ (K₀ + h))(θ, ψ) = X(K₀(θ,ψ) + h(θ,ψ), ψ)`. -/
theorem AnaFieldAt.comp_eval {X : ℝ → ℝ → ℂ → ℂ → ℂ} (F : AnaFieldAt ρ C d X) (hρ : 0 ≤ ρ)
    (hd : 0 < d) {h : FA × FA} {b : ℝ} (h1 : Bd ρ h.1 b) (h2 : Bd ρ h.2 b) (hb : b < d)
    (θ ψ : ℝ) :
    WEll1Z2.eval (F.compFA h) θ ψ =
      X θ ψ (WEll1Z2.eval h.1 θ ψ) (WEll1Z2.eval h.2 θ ψ) := by
  have hb0 : 0 ≤ b := h1.nonneg
  have hmaj : Majorized F.c C d := fun α => by
    rw [norm_eq_wnorm]; exact ((F.bound α).mono hρ le_rfl).2
  have n1 : ‖h.1‖ ≤ b := by rw [norm_eq_wnorm]; exact (h1.mono hρ le_rfl).2
  have n2 : ‖h.2‖ ≤ b := by rw [norm_eq_wnorm]; exact (h2.mono hρ le_rfl).2
  obtain ⟨hs, -⟩ := comp_summable_and_le hd hmaj hb0 hb n1 n2
  have hmap := hs.hasSum.map (evalHom θ ψ) (continuous_evalHom θ ψ)
  have e : (⇑(evalHom θ ψ) ∘ fun α : ℕ × ℕ => F.c α * h.1 ^ α.1 * h.2 ^ α.2) =
      fun α => WEll1Z2.eval (F.c α) θ ψ * WEll1Z2.eval h.1 θ ψ ^ α.1 *
        WEll1Z2.eval h.2 θ ψ ^ α.2 := by
    funext α; simp [map_mul, map_pow]; rfl
  rw [e] at hmap
  have hX := F.hasSum_eval θ ψ _ _ ((norm_eval_le_of_Bd hρ h1 θ ψ).trans_lt hb)
    ((norm_eval_le_of_Bd hρ h2 θ ψ).trans_lt hb)
  exact hmap.unique hX

end Torus

end PlasmaLean.Theory.KAM.AnalyticComposition
