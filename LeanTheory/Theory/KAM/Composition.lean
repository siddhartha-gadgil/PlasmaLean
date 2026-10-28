/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.WeightedEll1Z2

/-!
# Composition of polynomials with Banach-algebra elements

Composition estimates for `X ∘ K`
when `X` is polynomial (or polynomial divided by a polynomial `D`) and the torus `K` has
coefficients in a commutative Banach algebra such as `ℓ¹_r(ℤ²)` (`WEll1Z2 r`).

**Polynomial expressions.** `PolyExpr 𝕜 σ` is the syntax of polynomial expressions with
constants in a normed field `𝕜` and variables indexed by `σ` (`const`, `var`, `add`, `sub`,
`mul`; powers by `PolyExpr.npow`). It is evaluated in any normed commutative `𝕜`-algebra `A`
(`eval`). Keeping the *syntax* (rather than an `MvPolynomial`) makes the majorants follow the
way the polynomial is written, which is how explicit vector fields are usually given.

**Majorants.** For `a : σ → ℝ` (a bound on the variables' norms), `maj a e` is `e` evaluated with
every constant replaced by its norm and every subtraction by an addition: the majorant
polynomial `P̂`. `majD a b e` is its directional derivative `P̂'(a)·b` and `majD2 a b e` its second
directional derivative `P̂''(a)[b, b]` (both defined by the product rule). All three are monotone
in nonnegative arguments (`maj_mono`, `majD_mono`, `majD2_mono`).

**Main estimates.** With `‖x i‖ ≤ a i` and `‖h i‖ ≤ b i`:
* (a) `norm_eval_le`: `‖P(x)‖ ≤ P̂(a)`;
* `norm_deriv_le`: `‖DP(x)h‖ ≤ P̂'(a)·b`, where `DP(x)h = deriv x h e` is the algebraic
  directional derivative (product rule; linear in `h`: `deriv_add`, `deriv_smul`);
* `norm_eval_add_sub_le` (Lipschitz): `‖P(x + h) − P(x)‖ ≤ P̂'(a + b)·b`;
* (b) `norm_taylor_le` (Taylor with remainder):
  `‖P(x + h) − P(x) − DP(x)h‖ ≤ ½ P̂''(a + b)[b, b]`.
These are exact algebraic statements (no calculus): the remainder of a product satisfies
`R(uv) = Du·(v' − v) + R(u)·v' + u·R(v)`.

**Inverses.** `inverse_bound`: in a complete normed `𝕜`-algebra with `‖1‖ = 1`, if
`‖d − d̄·1‖ < ‖d̄‖` for a scalar `d̄` then `d` is a unit and
`‖d⁻¹‖ ≤ 1/(‖d̄‖ − ‖d − d̄·1‖)` (Neumann series). `norm_inverse_sub_inverse_le`:
`‖d'⁻¹ − d⁻¹‖ ≤ ‖d⁻¹‖‖d'⁻¹‖‖d' − d‖` and `norm_quot_sub_quot_le`: the corresponding bound for
quotients `n'·d'⁻¹ − n·d⁻¹`. Everything specializes to `WEll1Z2 r` (`r ≥ 0`).

**Sanity.** `maj_const`, `maj_npow`, the square `x²` (`deriv_sq`, `majD2_sq`: the remainder
bound is exact, `(x+h)² − x² − 2xh = h²` and `½ P̂'' = b²`), and the rejected fixture
`not_norm_eval_le_signed` (the majorant must use `|c|`: the signed evaluation `1 − 2·1 = −1`
does not bound `‖1 + 2‖`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

/-- Polynomial expressions with constants in `𝕜` and variables indexed by `σ`. -/
inductive PolyExpr (𝕜 : Type*) (σ : Type*) where
  /-- A constant. -/
  | const (c : 𝕜)
  /-- A variable. -/
  | var (i : σ)
  /-- Sum. -/
  | add (p q : PolyExpr 𝕜 σ)
  /-- Difference. -/
  | sub (p q : PolyExpr 𝕜 σ)
  /-- Product. -/
  | mul (p q : PolyExpr 𝕜 σ)

namespace PolyExpr

variable {𝕜 : Type*} [NormedField 𝕜] {σ : Type*}

/-- Powers `p^k = (…(1·p)·p…)·p`. -/
def npow (p : PolyExpr 𝕜 σ) : ℕ → PolyExpr 𝕜 σ
  | 0 => const 1
  | k + 1 => mul (npow p k) p

section Majorants

/-- The majorant polynomial `P̂(a)`: constants replaced by their norms, `−` by `+`. -/
def maj (a : σ → ℝ) : PolyExpr 𝕜 σ → ℝ
  | const c => ‖c‖
  | var i => a i
  | add p q => maj a p + maj a q
  | sub p q => maj a p + maj a q
  | mul p q => maj a p * maj a q

/-- The directional derivative `P̂'(a)·b` of the majorant (product rule). -/
def majD (a b : σ → ℝ) : PolyExpr 𝕜 σ → ℝ
  | const _ => 0
  | var i => b i
  | add p q => majD a b p + majD a b q
  | sub p q => majD a b p + majD a b q
  | mul p q => majD a b p * maj a q + maj a p * majD a b q

/-- The second directional derivative `P̂''(a)[b, b]` of the majorant. -/
def majD2 (a b : σ → ℝ) : PolyExpr 𝕜 σ → ℝ
  | const _ => 0
  | var _ => 0
  | add p q => majD2 a b p + majD2 a b q
  | sub p q => majD2 a b p + majD2 a b q
  | mul p q => majD2 a b p * maj a q + 2 * (majD a b p * majD a b q) + maj a p * majD2 a b q

variable {a a' b b' : σ → ℝ}

/-- `P̂(a) ≥ 0` for `a ≥ 0`. -/
theorem maj_nonneg (ha : ∀ i, 0 ≤ a i) (e : PolyExpr 𝕜 σ) : 0 ≤ maj a e := by
  induction e with
  | const c => exact norm_nonneg c
  | var i => exact ha i
  | add p q hp hq => exact add_nonneg hp hq
  | sub p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq => exact mul_nonneg hp hq

/-- `P̂'(a)·b ≥ 0` for `a, b ≥ 0`. -/
theorem majD_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (e : PolyExpr 𝕜 σ) :
    0 ≤ majD a b e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact hb i
  | add p q hp hq => exact add_nonneg hp hq
  | sub p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq =>
    exact add_nonneg (mul_nonneg hp (maj_nonneg ha q)) (mul_nonneg (maj_nonneg ha p) hq)

/-- `P̂''(a)[b, b] ≥ 0` for `a, b ≥ 0`. -/
theorem majD2_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (e : PolyExpr 𝕜 σ) :
    0 ≤ majD2 a b e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact le_rfl
  | add p q hp hq => exact add_nonneg hp hq
  | sub p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq =>
    have := majD_nonneg ha hb p
    have := majD_nonneg ha hb q
    have := maj_nonneg ha p
    have := maj_nonneg ha q
    exact add_nonneg (add_nonneg (mul_nonneg hp (maj_nonneg ha q)) (by positivity))
      (mul_nonneg (maj_nonneg ha p) hq)

/-- The majorant is monotone on nonnegative arguments. -/
theorem maj_mono (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ a' i) (e : PolyExpr 𝕜 σ) :
    maj a e ≤ maj a' e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact haa i
  | add p q hp hq => exact add_le_add hp hq
  | sub p q hp hq => exact add_le_add hp hq
  | mul p q hp hq => exact mul_le_mul hp hq (maj_nonneg ha q) ((maj_nonneg ha p).trans hp)

/-- `P̂'` is monotone in both arguments (nonnegative). -/
theorem majD_mono (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (haa : ∀ i, a i ≤ a' i)
    (hbb : ∀ i, b i ≤ b' i) (e : PolyExpr 𝕜 σ) : majD a b e ≤ majD a' b' e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact hbb i
  | add p q hp hq => exact add_le_add hp hq
  | sub p q hp hq => exact add_le_add hp hq
  | mul p q hp hq =>
    exact add_le_add
      (mul_le_mul hp (maj_mono ha haa q) (maj_nonneg ha q) ((majD_nonneg ha hb p).trans hp))
      (mul_le_mul (maj_mono ha haa p) hq (majD_nonneg ha hb q)
        ((maj_nonneg ha p).trans (maj_mono ha haa p)))

/-- `P̂''` is monotone in both arguments (nonnegative). -/
theorem majD2_mono (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (haa : ∀ i, a i ≤ a' i)
    (hbb : ∀ i, b i ≤ b' i) (e : PolyExpr 𝕜 σ) : majD2 a b e ≤ majD2 a' b' e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact le_rfl
  | add p q hp hq => exact add_le_add hp hq
  | sub p q hp hq => exact add_le_add hp hq
  | mul p q hp hq =>
    have m1 := maj_mono ha haa p
    have m2 := maj_mono ha haa q
    have d1 := majD_mono ha hb haa hbb p
    have d2 := majD_mono ha hb haa hbb q
    have n1 := maj_nonneg ha p
    have n2 := maj_nonneg ha q
    have e1 := majD_nonneg ha hb p
    have e2 := majD_nonneg ha hb q
    have f1 := majD2_nonneg ha hb p
    have f2 := majD2_nonneg ha hb q
    simp only [majD2]
    have k1 := mul_le_mul hp m2 n2 (f1.trans hp)
    have k2 := mul_le_mul d1 d2 e2 (e1.trans d1)
    have k3 := mul_le_mul m1 hq f2 (n1.trans m1)
    linarith

/-- Sanity: the majorant of a constant is its norm. -/
@[simp] theorem maj_const (c : 𝕜) : maj a (const c : PolyExpr 𝕜 σ) = ‖c‖ := rfl

/-- The majorant of a power is the power of the majorant. -/
@[simp] theorem maj_npow (p : PolyExpr 𝕜 σ) (k : ℕ) : maj a (npow p k) = maj a p ^ k := by
  induction k with
  | zero => simp [npow]
  | succ k ih => simp [npow, maj, ih, pow_succ]

end Majorants

section Eval

variable {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]

/-- Evaluation of a polynomial expression in a commutative `𝕜`-algebra. -/
def eval (x : σ → A) : PolyExpr 𝕜 σ → A
  | const c => algebraMap 𝕜 A c
  | var i => x i
  | add p q => eval x p + eval x q
  | sub p q => eval x p - eval x q
  | mul p q => eval x p * eval x q

/-- The directional derivative `DP(x)h` (product rule). -/
def deriv (x h : σ → A) : PolyExpr 𝕜 σ → A
  | const _ => 0
  | var i => h i
  | add p q => deriv x h p + deriv x h q
  | sub p q => deriv x h p - deriv x h q
  | mul p q => deriv x h p * eval x q + eval x p * deriv x h q

/-- Evaluation of a power. -/
@[simp] theorem eval_npow (x : σ → A) (p : PolyExpr 𝕜 σ) (k : ℕ) :
    eval x (npow p k) = eval x p ^ k := by
  induction k with
  | zero => simp [npow, eval]
  | succ k ih => simp [npow, eval, ih, pow_succ]

/-- `DP(x)` is additive in the direction. -/
theorem deriv_add (x h h' : σ → A) (e : PolyExpr 𝕜 σ) :
    deriv x (h + h') e = deriv x h e + deriv x h' e := by
  induction e with
  | const c => simp [deriv]
  | var i => simp [deriv]
  | add p q hp hq => simp only [deriv, hp, hq]; abel
  | sub p q hp hq => simp only [deriv, hp, hq]; abel
  | mul p q hp hq => simp only [deriv, hp, hq]; ring

/-- `DP(x)` is `𝕜`-homogeneous in the direction. -/
theorem deriv_smul (x h : σ → A) (c : 𝕜) (e : PolyExpr 𝕜 σ) :
    deriv x (c • h) e = c • deriv x h e := by
  induction e with
  | const c => simp [deriv]
  | var i => simp [deriv]
  | add p q hp hq => simp only [deriv, hp, hq, smul_add]
  | sub p q hp hq => simp only [deriv, hp, hq, smul_sub]
  | mul p q hp hq => simp only [deriv, hp, hq, smul_add, smul_mul_assoc, mul_smul_comm]

/-! ### Sanity checks for `deriv` -/

/-- Sanity: `D(x²)h = 2xh`. -/
theorem deriv_sq (x h : σ → A) (i : σ) :
    deriv x h (mul (var i) (var i) : PolyExpr 𝕜 σ) = 2 * (x i * h i) := by
  simp only [deriv, eval]; ring

/-- Sanity (exactness of the remainder bound): for `x²`, `½ P̂''(a + b)[b, b] = b²`, and the
remainder is exactly `h²`. -/
theorem majD2_sq (a b : σ → ℝ) (i : σ) :
    majD2 a b (mul (var i) (var i) : PolyExpr 𝕜 σ) / 2 = b i ^ 2 := by
  simp only [majD2, majD]; ring

/-- Sanity: the Taylor remainder of `x²` is `h²`. -/
theorem taylor_sq (x h : σ → A) (i : σ) :
    eval (x + h) (mul (var i) (var i) : PolyExpr 𝕜 σ) -
      eval x (mul (var i) (var i) : PolyExpr 𝕜 σ) -
      deriv x h (mul (var i) (var i) : PolyExpr 𝕜 σ) = h i ^ 2 := by
  simp only [deriv, eval, Pi.add_apply]; ring

/-! ### Norm estimates -/

variable [NormOneClass A] {a b : σ → ℝ} {x h : σ → A}

/-- **(a) Majorant bound** `‖P(x)‖ ≤ P̂(a)` when `‖x i‖ ≤ a i`. -/
theorem norm_eval_le (hx : ∀ i, ‖x i‖ ≤ a i) (e : PolyExpr 𝕜 σ) : ‖eval x e‖ ≤ maj a e := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  induction e with
  | const c => simp [eval, maj, norm_algebraMap']
  | var i => exact hx i
  | add p q hp hq => exact (norm_add_le _ _).trans (add_le_add hp hq)
  | sub p q hp hq => exact (norm_sub_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
    exact (norm_mul_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) (maj_nonneg ha p))

/-- **Derivative bound** `‖DP(x)h‖ ≤ P̂'(a)·b` when `‖x i‖ ≤ a i`, `‖h i‖ ≤ b i`. -/
theorem norm_deriv_le (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i) (e : PolyExpr 𝕜 σ) :
    ‖deriv x h e‖ ≤ majD a b e := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hh i)
  induction e with
  | const c => simp [deriv, majD]
  | var i => exact hh i
  | add p q hp hq => exact (norm_add_le _ _).trans (add_le_add hp hq)
  | sub p q hp hq => exact (norm_sub_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul hp (norm_eval_le hx q) (norm_nonneg _) (majD_nonneg ha hb p))
    · exact (norm_mul_le _ _).trans
        (mul_le_mul (norm_eval_le hx p) hq (norm_nonneg _) (maj_nonneg ha p))

omit [NormOneClass A] in
/-- Bound on the perturbed point: `‖x i + h i‖ ≤ a i + b i`. -/
theorem norm_add_le_add (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i) :
    ∀ i, ‖(x + h) i‖ ≤ (a + b) i := fun i =>
  (norm_add_le _ _).trans (add_le_add (hx i) (hh i))

/-- **Lipschitz bound** `‖P(x + h) − P(x)‖ ≤ P̂'(a + b)·b`. -/
theorem norm_eval_add_sub_le (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i)
    (e : PolyExpr 𝕜 σ) : ‖eval (x + h) e - eval x e‖ ≤ majD (a + b) b e := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hh i)
  have hab : ∀ i, 0 ≤ (a + b) i := fun i => add_nonneg (ha i) (hb i)
  have hle : ∀ i, a i ≤ (a + b) i := fun i => le_add_of_nonneg_right (hb i)
  have hxh := norm_add_le_add hx hh
  induction e with
  | const c => simp [eval, majD]
  | var i => simpa [eval, majD] using hh i
  | add p q hp hq =>
    simp only [eval, majD]
    rw [add_sub_add_comm]; exact (norm_add_le _ _).trans (add_le_add hp hq)
  | sub p q hp hq =>
    simp only [eval, majD]
    rw [sub_sub_sub_comm]; exact (norm_sub_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
    simp only [eval, majD]
    have hid : eval (x + h) p * eval (x + h) q - eval x p * eval x q =
        (eval (x + h) p - eval x p) * eval (x + h) q +
          eval x p * (eval (x + h) q - eval x q) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul hp (norm_eval_le hxh q) (norm_nonneg _) (majD_nonneg hab hb p))
    · exact (norm_mul_le _ _).trans (mul_le_mul ((norm_eval_le hx p).trans (maj_mono ha hle p))
        hq (norm_nonneg _) (maj_nonneg hab p))

/-- **(b) Taylor with remainder** in the Banach algebra:
`‖P(x + h) − P(x) − DP(x)h‖ ≤ ½ P̂''(a + b)[b, b]`. -/
theorem norm_taylor_le (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i) (e : PolyExpr 𝕜 σ) :
    ‖eval (x + h) e - eval x e - deriv x h e‖ ≤ majD2 (a + b) b e / 2 := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hh i)
  have hab : ∀ i, 0 ≤ (a + b) i := fun i => add_nonneg (ha i) (hb i)
  have hle : ∀ i, a i ≤ (a + b) i := fun i => le_add_of_nonneg_right (hb i)
  have hxh := norm_add_le_add hx hh
  induction e with
  | const c => simp [eval, deriv, majD2]
  | var i => simp [eval, deriv, majD2]
  | add p q hp hq =>
    simp only [eval, deriv, majD2]
    have hid : eval (x + h) p + eval (x + h) q - (eval x p + eval x q) -
        (deriv x h p + deriv x h q) = (eval (x + h) p - eval x p - deriv x h p) +
          (eval (x + h) q - eval x q - deriv x h q) := by abel
    rw [hid, add_div]; exact (norm_add_le _ _).trans (add_le_add hp hq)
  | sub p q hp hq =>
    simp only [eval, deriv, majD2]
    have hid : eval (x + h) p - eval (x + h) q - (eval x p - eval x q) -
        (deriv x h p - deriv x h q) = (eval (x + h) p - eval x p - deriv x h p) -
          (eval (x + h) q - eval x q - deriv x h q) := by abel
    rw [hid, add_div]; exact (norm_sub_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
    simp only [eval, deriv, majD2]
    have hid : eval (x + h) p * eval (x + h) q - eval x p * eval x q -
        (deriv x h p * eval x q + eval x p * deriv x h q) =
        deriv x h p * (eval (x + h) q - eval x q) +
          (eval (x + h) p - eval x p - deriv x h p) * eval (x + h) q +
          eval x p * (eval (x + h) q - eval x q - deriv x h q) := by ring
    rw [hid]
    have t1 : ‖deriv x h p * (eval (x + h) q - eval x q)‖ ≤
        majD (a + b) b p * majD (a + b) b q :=
      (norm_mul_le _ _).trans (mul_le_mul
        ((norm_deriv_le hx hh p).trans (majD_mono ha hb hle (fun i => le_rfl) p))
        (norm_eval_add_sub_le hx hh q) (norm_nonneg _) (majD_nonneg hab hb p))
    have t2 : ‖(eval (x + h) p - eval x p - deriv x h p) * eval (x + h) q‖ ≤
        majD2 (a + b) b p / 2 * maj (a + b) q :=
      (norm_mul_le _ _).trans (mul_le_mul hp (norm_eval_le hxh q) (norm_nonneg _)
        (div_nonneg (majD2_nonneg hab hb p) zero_le_two))
    have t3 : ‖eval x p * (eval (x + h) q - eval x q - deriv x h q)‖ ≤
        maj (a + b) p * (majD2 (a + b) b q / 2) :=
      (norm_mul_le _ _).trans (mul_le_mul ((norm_eval_le hx p).trans (maj_mono ha hle p)) hq
        (norm_nonneg _) (maj_nonneg hab p))
    calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ majD (a + b) b p * majD (a + b) b q + majD2 (a + b) b p / 2 * maj (a + b) q +
          maj (a + b) p * (majD2 (a + b) b q / 2) := add_le_add (add_le_add t1 t2) t3
      _ = _ := by ring

end Eval

/-- Rejected fixture: the majorant must use `|c|`. For `P = 1 + 2·x` at `x = 1 ∈ ℂ`, the
absolute value of the expression with a sign flipped, `|1 − 2·1| = 1`, is below `‖P(1)‖ = 3`,
while the majorant `1 + 2·1 = 3` is sharp. -/
theorem not_norm_eval_le_signed :
    ¬ ‖eval (𝕜 := ℂ) (fun _ : Unit => (1 : ℂ))
        (add (const 1) (mul (const 2) (var ())))‖ ≤ |(1 : ℝ) - 2 * 1| := by
  simp only [eval, Algebra.algebraMap_self, RingHom.id_apply]
  norm_num

end PolyExpr

/-! ## Inverses by the Neumann series -/

section Inverse

variable {𝕜 : Type*} [NormedField 𝕜] {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
  [NormOneClass A] [CompleteSpace A]

/-- **(c) Neumann bound for `1/D`.** If `‖d − d̄·1‖ < ‖d̄‖` for a scalar `d̄` then `d` is a unit
and `‖d⁻¹‖ ≤ 1/(‖d̄‖ − ‖d − d̄·1‖)`. -/
theorem inverse_bound (d : A) (dbar : 𝕜) (hd : ‖d - algebraMap 𝕜 A dbar‖ < ‖dbar‖) :
    IsUnit d ∧ ‖Ring.inverse d‖ ≤ 1 / (‖dbar‖ - ‖d - algebraMap 𝕜 A dbar‖) := by
  have h0 : 0 < ‖dbar‖ := (norm_nonneg _).trans_lt hd
  have hne : dbar ≠ 0 := norm_pos_iff.1 h0
  set b : A := dbar⁻¹ • d with hbdef
  have hb1 : b - 1 = dbar⁻¹ • (d - algebraMap 𝕜 A dbar) := by
    rw [smul_sub, Algebra.smul_def dbar⁻¹ (algebraMap 𝕜 A dbar), ← map_mul,
      inv_mul_cancel₀ hne, map_one]
  have hnb : ‖b - 1‖ = ‖d - algebraMap 𝕜 A dbar‖ / ‖dbar‖ := by
    rw [hb1, norm_smul, norm_inv, inv_mul_eq_div]
  have hlt : ‖-(b - 1)‖ < 1 := by
    rw [norm_neg, hnb, div_lt_one h0]; exact hd
  have hbu : IsUnit b := by
    have := isUnit_one_sub_of_norm_lt_one hlt
    rwa [sub_neg_eq_add, add_sub_cancel] at this
  have hbinv : ‖Ring.inverse b‖ ≤ 1 / (1 - ‖b - 1‖) := by
    have h1 : b = 1 - -(b - 1) := by abel
    rw [h1, ← geom_series_eq_inverse _ hlt]
    have := tsum_geometric_le_of_norm_lt_one _ hlt
    rw [norm_one, sub_self, zero_add, norm_neg] at this
    rw [one_div]; convert this using 3; abel_nf
  have hdu : d = dbar • b := by rw [hbdef, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hu : IsUnit d := by
    rw [hdu, Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.2 hne).map (algebraMap 𝕜 A)).mul hbu
  have hinv : Ring.inverse d = dbar⁻¹ • Ring.inverse b := by
    have h1 : d * (dbar⁻¹ • Ring.inverse b) = 1 := by
      rw [hdu, smul_mul_smul_comm, mul_inv_cancel₀ hne, one_smul, Ring.mul_inverse_cancel _ hbu]
    have := (Ring.inverse_mul_eq_iff_eq_mul d 1 _ hu).2 h1.symm
    rwa [mul_one] at this
  refine ⟨hu, ?_⟩
  have hpos : 0 < 1 - ‖b - 1‖ := by rw [norm_neg] at hlt; linarith
  rw [hinv, norm_smul, norm_inv]
  calc ‖dbar‖⁻¹ * ‖Ring.inverse b‖ ≤ ‖dbar‖⁻¹ * (1 / (1 - ‖b - 1‖)) :=
        mul_le_mul_of_nonneg_left hbinv (inv_nonneg.2 h0.le)
    _ = 1 / (‖dbar‖ - ‖d - algebraMap 𝕜 A dbar‖) := by
        rw [hnb]; field_simp

omit [NormOneClass A] [CompleteSpace A] in
/-- Difference of inverses: `‖d'⁻¹ − d⁻¹‖ ≤ ‖d⁻¹‖ ‖d'⁻¹‖ ‖d' − d‖` for units `d, d'`. -/
theorem norm_inverse_sub_inverse_le {d d' : A} (hd : IsUnit d) (hd' : IsUnit d') :
    ‖Ring.inverse d' - Ring.inverse d‖ ≤
      ‖Ring.inverse d‖ * ‖Ring.inverse d'‖ * ‖d' - d‖ := by
  have hid : Ring.inverse d' - Ring.inverse d =
      Ring.inverse d * (d - d') * Ring.inverse d' := by
    rw [mul_sub, sub_mul, Ring.inverse_mul_cancel _ hd, one_mul, mul_assoc,
      Ring.mul_inverse_cancel _ hd', mul_one]
  rw [hid, ← norm_neg (d' - d), neg_sub]
  calc _ ≤ ‖Ring.inverse d * (d - d')‖ * ‖Ring.inverse d'‖ := norm_mul_le _ _
    _ ≤ ‖Ring.inverse d‖ * ‖d - d'‖ * ‖Ring.inverse d'‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

omit [NormOneClass A] [CompleteSpace A] in
/-- Difference of quotients: `‖n'd'⁻¹ − nd⁻¹‖ ≤ ‖n' − n‖‖d'⁻¹‖ + ‖n‖‖d⁻¹‖‖d'⁻¹‖‖d' − d‖`. -/
theorem norm_quot_sub_quot_le {n n' d d' : A} (hd : IsUnit d) (hd' : IsUnit d') :
    ‖n' * Ring.inverse d' - n * Ring.inverse d‖ ≤
      ‖n' - n‖ * ‖Ring.inverse d'‖ +
        ‖n‖ * (‖Ring.inverse d‖ * ‖Ring.inverse d'‖ * ‖d' - d‖) := by
  have hid : n' * Ring.inverse d' - n * Ring.inverse d =
      (n' - n) * Ring.inverse d' + n * (Ring.inverse d' - Ring.inverse d) := by
    rw [sub_mul, mul_sub]; abel
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) ?_)
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_inverse_sub_inverse_le hd hd') (norm_nonneg _))

/-- Sanity (degenerate case): `d = d̄·1` gives `‖d⁻¹‖ ≤ 1/‖d̄‖`. -/
theorem inverse_bound_const (dbar : 𝕜) (h : dbar ≠ 0) :
    ‖Ring.inverse (algebraMap 𝕜 A dbar)‖ ≤ 1 / ‖dbar‖ := by
  have := (inverse_bound (algebraMap 𝕜 A dbar) dbar (by simpa using h)).2
  simpa using this

end Inverse

/-! ## Specialization to `ℓ¹_r(ℤ²)` -/

namespace WEll1Z2

variable {r : ℝ} [Fact (0 ≤ r)]

/-- `1/D` in `ℓ¹_r(ℤ²)`: if `‖D − D̄‖_r < |D̄|` then `D` is invertible with
`‖D⁻¹‖_r ≤ 1/(|D̄| − ‖D − D̄‖_r)`. -/
theorem inverse_bound (d : WEll1Z2 r) (dbar : ℂ) (hd : ‖d - algebraMap ℂ _ dbar‖ < ‖dbar‖) :
    IsUnit d ∧ ‖Ring.inverse d‖ ≤ 1 / (‖dbar‖ - ‖d - algebraMap ℂ _ dbar‖) :=
  LeanTheory.Theory.KAM.inverse_bound d dbar hd

end WEll1Z2

end LeanTheory.Theory.KAM
