/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Kronecker2D
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Weighted polynomial expression trees for Kronecker certificates

A small, reusable layer over `Certificates/Kronecker2D` for certificates that evaluate one large
polynomial expression in several trigonometric polynomials (for example a frame and torsion
certificate of a KAM torus).

An expression is a tree `Ex` (variables, integer constants, `+`, `-`, `*`). One tree is used in
three ways:

* **real evaluation** `Ex.eval` (the honest value), with **majorants** `majQ`/`dmajQ` bounding the
  value and the effect of perturbing the variables (`abs_eval_le`, `abs_eval_sub_le`), and a
  symbolic partial derivative `dEx` (`hasDerivAt_eval`);
* **phased evaluation** `Ex.evH` in any commutative ring (`P2 = ℤ[u][v]`, `ℤ` after Kronecker
  substitution, `ℂ`), commuting with ring homomorphisms (`evH_map`), with degree boxes
  (`inBox_evH`) and a priori `ℓ¹` bounds (`l1_evH`);
* the bridge `evH_phase`: if every variable `i` is represented by `x̂ᵢ = λ(Wᵢ) xᵢ` with a weight
  `Wᵢ = (dt, dv, ph)`, `λ(dt, dv, ph) = T^dt V^dv i^ph`, and the tree is homogeneous for these
  weights (`Ex.wt W e = some w`, checked by computation), then `evH W x̂ e = λ(w) · eval x e`.

The phases are needed because sine series are represented by integer polynomials only up to a
factor `i`. In `evH` a sum of two terms whose phases differ by
`2` is formed with a minus sign, so that the factors `i² = −1` cancel and `evH` represents the
honest real value `eval`.
-/

@[expose] public section

namespace LeanTheory.Certificates.KronExpr

open Polynomial LeanTheory.Certificates.Kron2

/-- Polynomial expression trees: variables, integer constants, sums, differences, products. -/
inductive Ex where
  /-- The variable with index `i`. -/
  | var (i : ℕ)
  /-- An integer constant. -/
  | cst (k : ℤ)
  /-- Sum. -/
  | add (e f : Ex)
  /-- Difference. -/
  | sub (e f : Ex)
  /-- Product. -/
  | mul (e f : Ex)

namespace Ex

/-! ## Real (honest) evaluation and majorants -/

/-- Evaluation in a commutative ring. -/
def eval {α : Type*} [CommRing α] (x : ℕ → α) : Ex → α
  | var i => x i
  | cst k => (k : α)
  | add e f => eval x e + eval x f
  | sub e f => eval x e - eval x f
  | mul e f => eval x e * eval x f

/-- Majorant: a bound on `|eval x e|` from bounds `B i` on `|x i|`. -/
def majQ (B : ℕ → ℚ) : Ex → ℚ
  | var i => B i
  | cst k => |(k : ℚ)|
  | add e f => majQ B e + majQ B f
  | sub e f => majQ B e + majQ B f
  | mul e f => majQ B e * majQ B f

/-- Perturbation majorant: a bound on `|eval x e − eval x' e|` from `|x' i| ≤ B i` and
`|x i − x' i| ≤ E i`. -/
def dmajQ (B E : ℕ → ℚ) : Ex → ℚ
  | var i => E i
  | cst _ => 0
  | add e f => dmajQ B E e + dmajQ B E f
  | sub e f => dmajQ B E e + dmajQ B E f
  | mul e f => dmajQ B E e * (majQ B f + dmajQ B E f) + majQ B e * dmajQ B E f

/-- **Majorant bound**: `|eval x e| ≤ majQ B e` when `|x i| ≤ B i`. -/
theorem abs_eval_le {B : ℕ → ℚ} {x : ℕ → ℝ} (hx : ∀ i, |x i| ≤ B i) :
    ∀ e : Ex, |eval x e| ≤ majQ B e
  | var i => hx i
  | cst k => by simp [eval, majQ]
  | add e f => by
    simp only [eval, majQ, Rat.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (abs_eval_le hx e) (abs_eval_le hx f))
  | sub e f => by
    simp only [eval, majQ, Rat.cast_add]
    exact (abs_sub _ _).trans (add_le_add (abs_eval_le hx e) (abs_eval_le hx f))
  | mul e f => by
    simp only [eval, majQ, Rat.cast_mul, abs_mul]
    exact mul_le_mul (abs_eval_le hx e) (abs_eval_le hx f) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_eval_le hx e))

/-- **Perturbation bound**: `|eval x e − eval x' e| ≤ dmajQ B E e` when `|x' i| ≤ B i` and
`|x i − x' i| ≤ E i`. -/
theorem abs_eval_sub_le {B E : ℕ → ℚ} {x x' : ℕ → ℝ} (hB : ∀ i, |x' i| ≤ B i)
    (hE : ∀ i, |x i - x' i| ≤ E i) : ∀ e : Ex, |eval x e - eval x' e| ≤ dmajQ B E e
  | var i => hE i
  | cst k => by simp [eval, dmajQ]
  | add e f => by
    simp only [eval, dmajQ, Rat.cast_add]
    have h := add_le_add (abs_eval_sub_le hB hE e) (abs_eval_sub_le hB hE f)
    refine le_trans ?_ h
    rw [show eval x e + eval x f - (eval x' e + eval x' f) =
      (eval x e - eval x' e) + (eval x f - eval x' f) by ring]
    exact abs_add_le _ _
  | sub e f => by
    simp only [eval, dmajQ, Rat.cast_add]
    have h := add_le_add (abs_eval_sub_le hB hE e) (abs_eval_sub_le hB hE f)
    refine le_trans ?_ h
    rw [show eval x e - eval x f - (eval x' e - eval x' f) =
      (eval x e - eval x' e) - (eval x f - eval x' f) by ring]
    exact abs_sub _ _
  | mul e f => by
    simp only [eval, dmajQ, Rat.cast_add, Rat.cast_mul]
    have he := abs_eval_sub_le hB hE e
    have hf := abs_eval_sub_le hB hE f
    have hbe := abs_eval_le hB e
    have hbf := abs_eval_le hB f
    have hxf : |eval x f| ≤ (majQ B f : ℝ) + dmajQ B E f := by
      have := abs_sub_abs_le_abs_sub (eval x f) (eval x' f)
      linarith
    rw [show eval x e * eval x f - eval x' e * eval x' f =
      (eval x e - eval x' e) * eval x f + eval x' e * (eval x f - eval x' f) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h0 : 0 ≤ (dmajQ B E e : ℝ) := (abs_nonneg _).trans he
    exact add_le_add (mul_le_mul he hxf (abs_nonneg _) h0)
      (mul_le_mul hbe hf (abs_nonneg _) ((abs_nonneg _).trans hbe))

/-- Symbolic partial derivative with respect to the variable `k`. -/
def dEx (k : ℕ) : Ex → Ex
  | var i => if i = k then cst 1 else cst 0
  | cst _ => cst 0
  | add e f => add (dEx k e) (dEx k f)
  | sub e f => sub (dEx k e) (dEx k f)
  | mul e f => add (mul (dEx k e) f) (mul e (dEx k f))

/-- `dEx k e` is the partial derivative of the real evaluation in the variable `k`. -/
theorem hasDerivAt_eval (x : ℕ → ℝ) (k : ℕ) (y : ℝ) : ∀ e : Ex,
    HasDerivAt (fun y => eval (Function.update x k y) e)
      (eval (Function.update x k y) (dEx k e)) y
  | var i => by
    by_cases h : i = k
    · subst h
      simp only [eval, dEx, ↓reduceIte, Function.update_self, Int.cast_one]
      exact hasDerivAt_id y
    · simp only [eval, dEx, h, ↓reduceIte, Int.cast_zero, Function.update_of_ne h]
      exact hasDerivAt_const y (x i)
  | cst c => by simpa [eval, dEx] using hasDerivAt_const y (c : ℝ)
  | add e f => by
    exact HasDerivAt.add (hasDerivAt_eval x k y e) (hasDerivAt_eval x k y f)
  | sub e f => by
    exact HasDerivAt.sub (hasDerivAt_eval x k y e) (hasDerivAt_eval x k y f)
  | mul e f => by
    exact HasDerivAt.mul (hasDerivAt_eval x k y e) (hasDerivAt_eval x k y f)

/-- The real evaluation is continuous in continuously varying variables. -/
theorem continuous_eval {X : Type*} [TopologicalSpace X] {x : X → ℕ → ℝ}
    (hx : ∀ i, Continuous fun p => x p i) : ∀ e : Ex, Continuous fun p => eval (x p) e
  | var i => hx i
  | cst _ => continuous_const
  | add e f => (continuous_eval hx e).add (continuous_eval hx f)
  | sub e f => (continuous_eval hx e).sub (continuous_eval hx f)
  | mul e f => (continuous_eval hx e).mul (continuous_eval hx f)

/-! ## Weights and phased evaluation -/

/-- Combine the weights of the two operands of a sum: equal degrees and phases of equal parity. -/
def comb : Option (ℕ × ℕ × ℕ) → Option (ℕ × ℕ × ℕ) → Option (ℕ × ℕ × ℕ)
  | some (d, e, p), some (d', e', p') =>
    if d = d' ∧ e = e' ∧ (p + p') % 2 = 0 then some (d, e, p) else none
  | _, _ => none

/-- Product of weights (phases mod 4). -/
def wmul : Option (ℕ × ℕ × ℕ) → Option (ℕ × ℕ × ℕ) → Option (ℕ × ℕ × ℕ)
  | some (d, e, p), some (d', e', p') => some (d + d', e + e', (p + p') % 4)
  | _, _ => none

/-- The weight `(t-degree, v-degree, phase mod 4)` of a homogeneous tree, `none` otherwise. -/
def wt (W : ℕ → ℕ × ℕ × ℕ) : Ex → Option (ℕ × ℕ × ℕ)
  | var i => some (W i)
  | cst _ => some (0, 0, 0)
  | add e f => comb (wt W e) (wt W f)
  | sub e f => comb (wt W e) (wt W f)
  | mul e f => wmul (wt W e) (wt W f)

/-- The sign attached to the second operand of a sum: `−1` if the phases differ. -/
def sgn (W : ℕ → ℕ × ℕ × ℕ) (e f : Ex) : ℤ :=
  match wt W e, wt W f with
  | some (_, _, p), some (_, _, p') => if p = p' then 1 else -1
  | _, _ => 1

/-- Phased evaluation in a commutative ring. -/
def evH {α : Type*} [CommRing α] (W : ℕ → ℕ × ℕ × ℕ) (x : ℕ → α) : Ex → α
  | var i => x i
  | cst k => (k : α)
  | add e f => evH W x e + (sgn W e f : α) * evH W x f
  | sub e f => evH W x e - (sgn W e f : α) * evH W x f
  | mul e f => evH W x e * evH W x f

/-- `evH` commutes with ring homomorphisms. -/
theorem evH_map {α β : Type*} [CommRing α] [CommRing β] (φ : α →+* β) (W : ℕ → ℕ × ℕ × ℕ)
    (x : ℕ → α) : ∀ e : Ex, φ (evH W x e) = evH W (fun i => φ (x i)) e
  | var i => rfl
  | cst k => by simp [evH]
  | add e f => by simp [evH, evH_map φ W x e, evH_map φ W x f]
  | sub e f => by simp [evH, evH_map φ W x e, evH_map φ W x f]
  | mul e f => by simp [evH, evH_map φ W x e, evH_map φ W x f]

/-- The complex value `T^dt V^dv i^ph` of a weight. -/
noncomputable def lam (T V : ℂ) (w : ℕ × ℕ × ℕ) : ℂ := T ^ w.1 * V ^ w.2.1 * Complex.I ^ w.2.2

/-- `i^(n mod 4) = i^n`. -/
theorem I_pow_mod4 (n : ℕ) : Complex.I ^ (n % 4) = Complex.I ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

/-- Two phases `< 4` of equal parity that differ give opposite powers of `i`. -/
theorem I_pow_flip {p p' : ℕ} (hp : p < 4) (hp' : p' < 4) (hne : p ≠ p') (h2 : (p + p') % 2 = 0) :
    Complex.I ^ p' = -Complex.I ^ p := by
  have h4 := Complex.I_pow_four
  interval_cases p <;> interval_cases p' <;> simp_all [pow_succ]

/-- Phases of homogeneous trees stay below `4`. -/
theorem wt_ph_lt {W : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (W i).2.2 < 4) :
    ∀ (e : Ex) (w : ℕ × ℕ × ℕ), wt W e = some w → w.2.2 < 4
  | var i, w, h => by simp only [wt, Option.some.injEq] at h; rw [← h]; exact hW i
  | cst k, w, h => by simp only [wt, Option.some.injEq] at h; rw [← h]; norm_num
  | add e f, w, h => by
    simp only [wt] at h
    rcases he : wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, comb, reduceCtorEq] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h; rw [← h]; exact wt_ph_lt hW e _ he
  | sub e f, w, h => by
    simp only [wt] at h
    rcases he : wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, comb, reduceCtorEq] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h; rw [← h]; exact wt_ph_lt hW e _ he
  | mul e f, w, h => by
    simp only [wt] at h
    rcases he : wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, wmul, reduceCtorEq, Option.some.injEq] at h
    rw [← h]; exact Nat.mod_lt _ (by norm_num)

/-- Sum step of `evH_phase`. -/
theorem phase_add {T V : ℂ} {d dv p p' : ℕ} (hp : p < 4) (hp' : p' < 4) (h2 : (p + p') % 2 = 0)
    (A B : ℂ) :
    lam T V (d, dv, p) * A + ((if p = p' then 1 else -1 : ℤ) : ℂ) * (lam T V (d, dv, p') * B) =
      lam T V (d, dv, p) * (A + B) := by
  split_ifs with h
  · subst h; push_cast; ring
  · simp only [lam, I_pow_flip hp hp' h h2]; push_cast; ring

/-- **The phase bridge.** If each variable is represented by `x̂ᵢ = λ(Wᵢ) xᵢ` (real `xᵢ`) and the
tree is homogeneous with weight `w`, then the phased evaluation is `λ(w)` times the real value. -/
theorem evH_phase {W : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (W i).2.2 < 4) (T V : ℂ) {xh : ℕ → ℂ}
    {x : ℕ → ℝ} (hx : ∀ i, xh i = lam T V (W i) * (x i : ℂ)) :
    ∀ (e : Ex) (w : ℕ × ℕ × ℕ), wt W e = some w → evH W xh e = lam T V w * ((eval x e : ℝ) : ℂ)
  | var i, w, h => by
    simp only [wt, Option.some.injEq] at h; rw [← h]; exact hx i
  | cst k, w, h => by
    simp only [wt, Option.some.injEq] at h; rw [← h]; simp [evH, eval, lam]
  | add e f, w, h => by
    simp only [wt] at h
    rcases he : wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, comb, reduceCtorEq] at h
    split_ifs at h with hc
    obtain ⟨rfl, rfl, h2⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have hp : p < 4 := wt_ph_lt hW e _ he
    have hp' : p' < 4 := wt_ph_lt hW f _ hf
    simp only [evH, eval, sgn, he, hf, evH_phase hW T V hx e _ he, evH_phase hW T V hx f _ hf]
    rw [phase_add hp hp' h2]; push_cast; ring
  | sub e f, w, h => by
    simp only [wt] at h
    rcases he : wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, comb, reduceCtorEq] at h
    split_ifs at h with hc
    obtain ⟨rfl, rfl, h2⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have hp : p < 4 := wt_ph_lt hW e _ he
    have hp' : p' < 4 := wt_ph_lt hW f _ hf
    simp only [evH, eval, sgn, he, hf, evH_phase hW T V hx e _ he, evH_phase hW T V hx f _ hf]
    have key := phase_add (T := T) (V := V) (d := d) (dv := dv) hp hp' h2
      ((eval x e : ℝ) : ℂ) (-((eval x f : ℝ) : ℂ))
    rw [Complex.ofReal_sub]; linear_combination key
  | mul e f, w, h => by
    simp only [wt] at h
    rcases he : wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, wmul, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [evH, eval, evH_phase hW T V hx e _ he, evH_phase hW T V hx f _ hf, lam,
      I_pow_mod4]
    push_cast; ring

/-! ## Degree boxes and a priori `ℓ¹` bounds of the phased evaluation in `P2` -/

/-- Degree box of a tree from degree boxes of the variables. -/
def box (Bx : ℕ → ℕ × ℕ) : Ex → ℕ × ℕ
  | var i => Bx i
  | cst _ => (0, 0)
  | add e f => (max (box Bx e).1 (box Bx f).1, max (box Bx e).2 (box Bx f).2)
  | sub e f => (max (box Bx e).1 (box Bx f).1, max (box Bx e).2 (box Bx f).2)
  | mul e f => ((box Bx e).1 + (box Bx f).1, (box Bx e).2 + (box Bx f).2)

/-- `ℓ¹` majorant of a tree from `ℓ¹` bounds of the variables. -/
def majN (L : ℕ → ℕ) : Ex → ℕ
  | var i => L i
  | cst k => k.natAbs
  | add e f => majN L e + majN L f
  | sub e f => majN L e + majN L f
  | mul e f => majN L e * majN L f

/-- Integer constants of `P2`. -/
theorem intCast_P2 (k : ℤ) : (k : P2) = C (C k) := by simp

/-- Integer constants lie in the box `(0, 0)`. -/
theorem inBox_intCast (k : ℤ) : InBox (k : P2) 0 0 := by
  rw [intCast_P2]; exact InBox.C k

/-- **Degree box** of the phased evaluation in `P2`. -/
theorem inBox_evH {Bx : ℕ → ℕ × ℕ} (W : ℕ → ℕ × ℕ × ℕ) {x : ℕ → P2}
    (hx : ∀ i, InBox (x i) (Bx i).1 (Bx i).2) :
    ∀ e : Ex, InBox (evH W x e) (box Bx e).1 (box Bx e).2
  | var i => hx i
  | cst k => inBox_intCast k
  | add e f => by
    have h1 := inBox_evH W hx e
    have h2 := (inBox_intCast (sgn W e f)).mul (inBox_evH W hx f)
    simp only [zero_add] at h2
    exact (h1.mono (le_max_left _ _) (le_max_left _ _)).add
      (h2.mono (le_max_right _ _) (le_max_right _ _))
  | sub e f => by
    have h1 := inBox_evH W hx e
    have h2 := (inBox_intCast (sgn W e f)).mul (inBox_evH W hx f)
    simp only [zero_add] at h2
    exact (h1.mono (le_max_left _ _) (le_max_left _ _)).sub
      (h2.mono (le_max_right _ _) (le_max_right _ _))
  | mul e f => (inBox_evH W hx e).mul (inBox_evH W hx f)

/-- The phase sign is `±1`. -/
theorem natAbs_sgn (W : ℕ → ℕ × ℕ × ℕ) (e f : Ex) : (sgn W e f).natAbs = 1 := by
  unfold sgn; split
  · split_ifs <;> rfl
  · rfl

/-- Multiplying by the phase sign does not increase `ℓ¹`. -/
theorem l1_sgn_mul (W : ℕ → ℕ × ℕ × ℕ) (e f : Ex) (P : P2) :
    l1 ((sgn W e f : P2) * P) ≤ l1 P := by
  rw [intCast_P2]
  exact (l1_C_mul_le _ _).trans (by rw [natAbs_sgn, one_mul])

/-- **A priori `ℓ¹` bound** of the phased evaluation in `P2`. -/
theorem l1_evH {L : ℕ → ℕ} (W : ℕ → ℕ × ℕ × ℕ) {x : ℕ → P2} (hx : ∀ i, l1 (x i) ≤ L i) :
    ∀ e : Ex, l1 (evH W x e) ≤ majN L e
  | var i => hx i
  | cst k => by rw [evH, intCast_P2, l1_C]; rfl
  | add e f => (l1_add_le _ _).trans (add_le_add (l1_evH W hx e)
      ((l1_sgn_mul W e f _).trans (l1_evH W hx f)))
  | sub e f => (l1_sub_le _ _).trans (add_le_add (l1_evH W hx e)
      ((l1_sgn_mul W e f _).trans (l1_evH W hx f)))
  | mul e f => (l1_mul_le _ _).trans (Nat.mul_le_mul (l1_evH W hx e) (l1_evH W hx f))

/-! ## Sanity checks -/

/-- Fixture weights: variable `0` has weight `(1, 0, 0)` (a cosine series), variable `1` weight
`(1, 0, 1)` (a sine series, represented with a factor `i`). -/
def fixW : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | _ => (1, 0, 1)

/-- Accepted fixture: `x₀² + x₁²` is homogeneous of weight `(2, 0, 0)`. -/
theorem wt_fixture_accept :
    wt fixW (add (mul (var 0) (var 0)) (mul (var 1) (var 1))) = some (2, 0, 0) := by
  rfl

/-- Rejected fixture: `x₀ + x₁` mixes the phases `0` and `1`, so it has no weight. -/
theorem wt_fixture_reject : wt fixW (add (var 0) (var 1)) = none := by rfl

/-- Degenerate case: a constant has weight `0`, so adding it to a variable is rejected. -/
theorem wt_fixture_const : wt fixW (add (var 0) (cst 1)) = none := by rfl

/-- Special case: the phased evaluation of `x₀² + x₁²` subtracts the second square (the factor
`i² = −1` of the representation `x̂₁ = i x₁` is compensated). -/
theorem evH_fixture (a b : ℤ) :
    evH fixW (fun i => if i = 0 then a else b)
      (add (mul (var 0) (var 0)) (mul (var 1) (var 1))) = a * a - b * b := by
  simp [evH, sgn, wt, wmul, fixW]; ring

/-- Majorant fixture: `|x₀ x₁ − x₀' x₁'| ≤ 0.21` when `|x₀'|, |x₁'| ≤ 1` and both variables move
by at most `0.1`. -/
theorem dmajQ_fixture :
    dmajQ (fun _ => 1) (fun _ => 1 / 10) (mul (var 0) (var 1)) = 21 / 100 := by
  simp [dmajQ, majQ]; norm_num

end Ex

end LeanTheory.Certificates.KronExpr
