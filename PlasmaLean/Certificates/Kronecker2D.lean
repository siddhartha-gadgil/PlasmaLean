/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact ℓ¹ norms of bivariate integer polynomials by Kronecker substitution

Infrastructure for certifying sup-norm bounds of **trigonometric polynomials** with exact
integer coefficients (KAM route, stage K2, `notes/theory/kam-route.md` §5).

A bivariate integer polynomial `P ∈ ℤ[u][v]` (`P2 = Polynomial (Polynomial ℤ)`, outer variable
`v`, inner variable `u`) evaluated at unimodular `u = e^{iθ}`, `v = e^{iψ}` is a trigonometric
polynomial, and `‖P(u, v)‖ ≤ ‖P‖₁` (`norm_evalC_le`), where `‖P‖₁ = l1 P` is the sum of the
absolute values of the coefficients. `l1` is subadditive and submultiplicative (`l1_add_le`,
`l1_mul_le`), so `l1` of a polynomial expression is bounded a priori by the same expression in the
`l1` of its inputs.

**Kronecker substitution.** `kron b W : P2 →+* ℤ` evaluates at `u = X = 2^b`, `v = X^W`. It is a
ring homomorphism, so the image of a large polynomial expression is computed with a few big-integer
multiplications (GMP-accelerated in the kernel). If `P` lies in the box
`deg_u ≤ a < W`, `deg_v ≤ J` and its coefficients satisfy `‖P‖₁ < 2^(b-1)`, then the
coefficients of `P` are the balanced base-`X` digits of `kron b W P`, and
`l1 P = l1Kron b d (kron b W P)` (`l1_eq_l1Kron`), where `l1Kron` sums the absolute values of
the digits by divide and conquer with shifts. Thus `‖P‖₁` of a product of polynomials with
thousands of terms is an exact kernel computation, with no truncation and no rounding.

`InBox` records the degree box, closed under `+`, `-`, `*` (`InBox.add`, `InBox.mul`, ...).
-/

@[expose] public section

namespace PlasmaLean.Certificates.Kron2

open Polynomial Finset

/-! ## ℓ¹-type functionals lifted to polynomials -/

section Lift
variable {R : Type*} [Semiring R]

/-- The functional `p ↦ ∑ₙ N(pₙ)` induced on polynomials by a functional `N` on coefficients. -/
noncomputable def liftN (N : R → ℕ) (p : R[X]) : ℕ := p.sum fun _ c => N c

/-- `liftN` as a sum over any range containing the support. -/
theorem liftN_eq_sum_range (N : R → ℕ) (h0 : N 0 = 0) (p : R[X]) {n : ℕ}
    (hn : p.natDegree < n) : liftN N p = ∑ i ∈ range n, N (p.coeff i) :=
  sum_over_range' p (fun _ => h0) n hn

/-- `liftN` of zero. -/
theorem liftN_zero (N : R → ℕ) : liftN N (0 : R[X]) = 0 := by simp [liftN]

/-- `liftN` of a monomial. -/
theorem liftN_monomial (N : R → ℕ) (h0 : N 0 = 0) (n : ℕ) (c : R) :
    liftN N (monomial n c) = N c :=
  sum_monomial_index c (fun _ c => N c) h0

/-- Subadditivity is inherited. -/
theorem liftN_add_le (N : R → ℕ) (h0 : N 0 = 0) (hadd : ∀ a b, N (a + b) ≤ N a + N b)
    (p q : R[X]) : liftN N (p + q) ≤ liftN N p + liftN N q := by
  set n := max (p + q).natDegree (max p.natDegree q.natDegree) + 1
  rw [liftN_eq_sum_range N h0 (p + q) (n := n) (by omega),
    liftN_eq_sum_range N h0 p (n := n) (by omega), liftN_eq_sum_range N h0 q (n := n) (by omega),
    ← sum_add_distrib]
  exact sum_le_sum fun i _ => by rw [coeff_add]; exact hadd _ _

/-- Subadditivity over finite sums. -/
theorem liftN_sum_le (N : R → ℕ) (h0 : N 0 = 0) (hadd : ∀ a b, N (a + b) ≤ N a + N b)
    {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    liftN N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, liftN N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [liftN_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (liftN_add_le N h0 hadd _ _).trans (by gcongr)

/-- Submultiplicativity is inherited. -/
theorem liftN_mul_le (N : R → ℕ) (h0 : N 0 = 0) (hadd : ∀ a b, N (a + b) ≤ N a + N b)
    (hmul : ∀ a b, N (a * b) ≤ N a * N b) (p q : R[X]) :
    liftN N (p * q) ≤ liftN N p * liftN N q := by
  rw [mul_eq_sum_sum]
  calc liftN N (∑ i ∈ p.support, q.sum fun j a => monomial (i + j) (p.coeff i * a))
      ≤ ∑ i ∈ p.support, liftN N (q.sum fun j a => monomial (i + j) (p.coeff i * a)) :=
        liftN_sum_le N h0 hadd _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, N (p.coeff i) * N (q.coeff j) := by
        gcongr with i hi
        rw [Polynomial.sum_def]
        refine (liftN_sum_le N h0 hadd _ _).trans (sum_le_sum fun j _ => ?_)
        rw [liftN_monomial N h0]
        exact hmul _ _
    _ = liftN N p * liftN N q := by
        rw [liftN, liftN, Polynomial.sum_def, Polynomial.sum_def, sum_mul_sum]

/-- A single coefficient is bounded by `liftN`. -/
theorem le_liftN (N : R → ℕ) (h0 : N 0 = 0) (p : R[X]) (n : ℕ) : N (p.coeff n) ≤ liftN N p := by
  by_cases hn : n ∈ p.support
  · rw [liftN, Polynomial.sum_def]
    exact single_le_sum (f := fun n => N (p.coeff n)) (fun _ _ => Nat.zero_le _) hn
  · rw [notMem_support_iff.mp hn, h0]; exact Nat.zero_le _

/-- Norm bound for evaluation at a point of the closed unit disc. -/
theorem norm_eval₂_le (N : R → ℕ) (f : R →+* ℂ) (hf : ∀ a, ‖f a‖ ≤ N a) {x : ℂ}
    (hx : ‖x‖ ≤ 1) (p : R[X]) : ‖p.eval₂ f x‖ ≤ liftN N p := by
  rw [eval₂_eq_sum, liftN, Polynomial.sum_def, Polynomial.sum_def]
  push_cast
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_pow]
  calc ‖f (p.coeff n)‖ * ‖x‖ ^ n ≤ N (p.coeff n) * 1 := by
        gcongr
        · exact hf _
        · exact pow_le_one₀ (norm_nonneg _) hx
    _ = _ := mul_one _

end Lift

section LiftRing
variable {R : Type*} [Ring R]

/-- `liftN` is invariant under negation when `N` is. -/
theorem liftN_neg (N : R → ℕ) (hneg : ∀ a, N (-a) = N a) (p : R[X]) :
    liftN N (-p) = liftN N p := by
  simp [liftN, Polynomial.sum_def, support_neg, coeff_neg, hneg]

end LiftRing

/-! ## The ℓ¹ norm on `ℤ[u]` and `ℤ[u][v]` -/

/-- Bivariate integer polynomials: outer variable `v`, inner variable `u`. -/
abbrev P2 : Type := Polynomial (Polynomial ℤ)

/-- `‖p‖₁ = ∑ |pₙ|` for `p ∈ ℤ[u]`. -/
noncomputable def l1Z (p : ℤ[X]) : ℕ := liftN Int.natAbs p

/-- `‖P‖₁ = ∑ |P_{ij}|` for `P ∈ ℤ[u][v]`. -/
noncomputable def l1 (P : P2) : ℕ := liftN l1Z P

theorem l1Z_zero : l1Z 0 = 0 := liftN_zero _

theorem l1Z_add_le (p q : ℤ[X]) : l1Z (p + q) ≤ l1Z p + l1Z q :=
  liftN_add_le _ rfl Int.natAbs_add_le p q

theorem l1Z_mul_le (p q : ℤ[X]) : l1Z (p * q) ≤ l1Z p * l1Z q :=
  liftN_mul_le _ rfl Int.natAbs_add_le (fun a b => (Int.natAbs_mul a b).le) p q

theorem l1Z_neg (p : ℤ[X]) : l1Z (-p) = l1Z p := liftN_neg _ Int.natAbs_neg p

/-- Subadditivity of `‖·‖₁`. -/
theorem l1_add_le (P Q : P2) : l1 (P + Q) ≤ l1 P + l1 Q :=
  liftN_add_le _ l1Z_zero l1Z_add_le P Q

/-- Submultiplicativity of `‖·‖₁` (the Banach-algebra property, constant `1`). -/
theorem l1_mul_le (P Q : P2) : l1 (P * Q) ≤ l1 P * l1 Q :=
  liftN_mul_le _ l1Z_zero l1Z_add_le l1Z_mul_le P Q

/-- `‖-P‖₁ = ‖P‖₁`. -/
theorem l1_neg (P : P2) : l1 (-P) = l1 P := liftN_neg _ l1Z_neg P

/-- `‖P - Q‖₁ ≤ ‖P‖₁ + ‖Q‖₁`. -/
theorem l1_sub_le (P Q : P2) : l1 (P - Q) ≤ l1 P + l1 Q := by
  rw [sub_eq_add_neg]; exact (l1_add_le _ _).trans (by rw [l1_neg])

/-- `‖∑ Pᵢ‖₁ ≤ ∑ ‖Pᵢ‖₁`. -/
theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → P2) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) :=
  liftN_sum_le _ l1Z_zero l1Z_add_le s f

/-- `‖c u^i v^j‖₁ = |c|`. -/
theorem l1_monomial (i j : ℕ) (c : ℤ) : l1 (monomial j (monomial i c)) = c.natAbs := by
  rw [l1, liftN_monomial _ l1Z_zero, l1Z, liftN_monomial _ rfl]

/-- A bivariate constant `c`. -/
theorem l1_C (c : ℤ) : l1 (C (C c)) = c.natAbs := by
  rw [show (C (C c) : P2) = monomial 0 (monomial 0 c) by simp [← C_mul_X_pow_eq_monomial]]
  exact l1_monomial 0 0 c

/-- `‖c • P‖₁ ≤ |c| ‖P‖₁` for an integer constant `c` (as `C (C c) * P`). -/
theorem l1_C_mul_le (c : ℤ) (P : P2) : l1 (C (C c) * P) ≤ c.natAbs * l1 P :=
  (l1_mul_le _ _).trans (by rw [l1_C])

/-- A coefficient is bounded by `‖·‖₁`. -/
theorem natAbs_coeff_le_l1 (P : P2) (i j : ℕ) : ((P.coeff j).coeff i).natAbs ≤ l1 P :=
  (le_liftN Int.natAbs rfl _ i).trans (le_liftN l1Z l1Z_zero P j)

/-! ## Evaluation on the unit torus -/

/-- Evaluation of `P ∈ ℤ[u][v]` at `(u, v) ∈ ℂ²`. -/
noncomputable def evalC (u v : ℂ) : P2 →+* ℂ :=
  eval₂RingHom (eval₂RingHom (Int.castRingHom ℂ) u) v

/-- Evaluation of a monomial. -/
theorem evalC_monomial (u v : ℂ) (i j : ℕ) (c : ℤ) :
    evalC u v (monomial j (monomial i c)) = c * u ^ i * v ^ j := by
  simp [evalC]

/-- **`|P(u, v)| ≤ ‖P‖₁` on the closed unit bidisc**, in particular on the torus
`u = e^{iθ}`, `v = e^{iψ}`. -/
theorem norm_evalC_le {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (P : P2) :
    ‖evalC u v P‖ ≤ l1 P := by
  refine norm_eval₂_le l1Z _ (fun p => ?_) hv P
  refine norm_eval₂_le Int.natAbs _ (fun c => ?_) hu p
  rw [eq_intCast, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

/-- Upper bound: if `P(u,v) = (κ f) m` with `κ > 0` and `|m| = 1`, then `|f| ≤ ‖P‖₁ / κ`. -/
theorem abs_le_of_evalC {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {P : P2} {κ f : ℝ}
    (hκ : 0 < κ) {m : ℂ} (hm : ‖m‖ = 1) (h : evalC u v P = ((κ * f : ℝ) : ℂ) * m) :
    |f| ≤ l1 P / κ := by
  have := norm_evalC_le hu.le hv.le P
  rw [h, norm_mul, hm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hκ] at this
  rw [le_div_iff₀ hκ]; linarith

/-- Lower bound: if `P(u,v) = (κ f) u^{i₀} v^{j₀}` with `κ > 0`, then for any integer `c₀`,
`f ≥ (c₀ - ‖P - c₀ u^{i₀} v^{j₀}‖₁) / κ` (`c₀` is the centre coefficient, supplied by an oracle;
any value is sound). -/
theorem le_of_evalC {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {P : P2} {κ f : ℝ} (hκ : 0 < κ)
    {i₀ j₀ : ℕ} (c₀ : ℤ) (h : evalC u v P = ((κ * f : ℝ) : ℂ) * (u ^ i₀ * v ^ j₀)) :
    ((c₀ : ℝ) - l1 (P - monomial j₀ (monomial i₀ c₀))) / κ ≤ f := by
  have hb := norm_evalC_le hu.le hv.le (P - monomial j₀ (monomial i₀ c₀))
  rw [map_sub, evalC_monomial, h] at hb
  have hm : ‖u ^ i₀ * v ^ j₀‖ = 1 := by simp [hu, hv]
  have e : ((κ * f : ℝ) : ℂ) * (u ^ i₀ * v ^ j₀) - (c₀ : ℂ) * u ^ i₀ * v ^ j₀ =
      (((κ * f - c₀ : ℝ)) : ℂ) * (u ^ i₀ * v ^ j₀) := by push_cast; ring
  rw [e, norm_mul, hm, mul_one, Complex.norm_real, Real.norm_eq_abs] at hb
  rw [div_le_iff₀ hκ]
  linarith [neg_abs_le (κ * f - c₀)]

/-! ## Degree boxes -/

/-- `P` has `v`-degree `≤ b` and every `v`-coefficient has `u`-degree `≤ a`. -/
def InBox (P : P2) (a b : ℕ) : Prop := P.natDegree ≤ b ∧ ∀ j, (P.coeff j).natDegree ≤ a

theorem InBox.mono {P : P2} {a b a' b' : ℕ} (h : InBox P a b) (ha : a ≤ a') (hb : b ≤ b') :
    InBox P a' b' := ⟨h.1.trans hb, fun j => (h.2 j).trans ha⟩

theorem InBox.add {P Q : P2} {a b : ℕ} (hP : InBox P a b) (hQ : InBox Q a b) :
    InBox (P + Q) a b :=
  ⟨(natDegree_add_le _ _).trans (max_le hP.1 hQ.1), fun j => by
    rw [coeff_add]; exact (natDegree_add_le _ _).trans (max_le (hP.2 j) (hQ.2 j))⟩

theorem InBox.neg {P : P2} {a b : ℕ} (hP : InBox P a b) : InBox (-P) a b :=
  ⟨by rw [natDegree_neg]; exact hP.1, fun j => by rw [coeff_neg, natDegree_neg]; exact hP.2 j⟩

theorem InBox.sub {P Q : P2} {a b : ℕ} (hP : InBox P a b) (hQ : InBox Q a b) :
    InBox (P - Q) a b := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

theorem InBox.mul {P Q : P2} {a b c d : ℕ} (hP : InBox P a b) (hQ : InBox Q c d) :
    InBox (P * Q) (a + c) (b + d) :=
  ⟨natDegree_mul_le.trans (add_le_add hP.1 hQ.1), fun j => by
    rw [coeff_mul]
    refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    exact natDegree_mul_le.trans (add_le_add (hP.2 _) (hQ.2 _))⟩

theorem InBox.sum {ι : Type*} (s : Finset ι) {f : ι → P2} {a b : ℕ}
    (h : ∀ i ∈ s, InBox (f i) a b) : InBox (∑ i ∈ s, f i) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, fun j => by simp⟩
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact (h x (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem InBox.monomial (i j : ℕ) (c : ℤ) : InBox (monomial j (monomial i c)) i j := by
  refine ⟨natDegree_monomial_le _, fun k => ?_⟩
  rw [coeff_monomial]
  split_ifs
  · exact natDegree_monomial_le _
  · simp

theorem InBox.C (c : ℤ) : InBox (Polynomial.C (Polynomial.C c)) 0 0 := by
  rw [show (Polynomial.C (Polynomial.C c) : P2) = Polynomial.monomial 0 (Polynomial.monomial 0 c) by
    simp [← C_mul_X_pow_eq_monomial]]
  exact InBox.monomial 0 0 c

/-! ## Kronecker substitution -/

/-- Kronecker substitution `u ↦ X = 2^b`, `v ↦ X^W`. -/
noncomputable def kron (b W : ℕ) : P2 →+* ℤ :=
  eval₂RingHom (eval₂RingHom (RingHom.id ℤ) ((2 : ℤ) ^ b)) (((2 : ℤ) ^ b) ^ W)

/-- Kronecker image of a monomial. -/
theorem kron_monomial (b W i j : ℕ) (c : ℤ) :
    kron b W (monomial j (monomial i c)) = c * (2 : ℤ) ^ (b * (i + W * j)) := by
  simp [kron, pow_add, pow_mul]
  ring

/-- The coefficient in slot `n = i + W j`. -/
noncomputable def slot (P : P2) (W n : ℕ) : ℤ := (P.coeff (n / W)).coeff (n % W)

/-- Splitting a range of length `W * J` into `J` blocks of length `W`. -/
theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) (W J : ℕ) :
    ∑ n ∈ range (W * J), g n = ∑ j ∈ range J, ∑ i ∈ range W, g (i + W * j) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    exact sum_congr rfl fun i _ => by rw [add_comm]

/-- `slot` at `i + W j` for `i < W`. -/
theorem slot_add_mul {P : P2} {W i j : ℕ} (hi : i < W) :
    slot P W (i + W * j) = (P.coeff j).coeff i := by
  have hW : 0 < W := by omega
  rw [slot, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hi, zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hi]

/-- Outside the box, slots vanish. -/
theorem slot_eq_zero {P : P2} {a J W n : ℕ} (hbox : InBox P a J) (hW : 0 < W)
    (hn : W * (J + 1) ≤ n) : slot P W n = 0 := by
  have : J + 1 ≤ n / W := (Nat.le_div_iff_mul_le hW).2 (by rw [mul_comm]; exact hn)
  have h1 := hbox.1
  rw [slot, coeff_eq_zero_of_natDegree_lt (p := P) (by omega)]
  simp

/-- **Kronecker image as a slot sum** (for `P` in the box). -/
theorem kron_eq_sum {P : P2} {a J W S : ℕ} (b : ℕ) (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) :
    kron b W P = ∑ n ∈ range S, slot P W n * ((2 : ℤ) ^ b) ^ n := by
  have h1 : kron b W P = ∑ j ∈ range (J + 1), ∑ i ∈ range W,
      slot P W (i + W * j) * ((2 : ℤ) ^ b) ^ (i + W * j) := by
    rw [kron, coe_eval₂RingHom, eval₂_eq_sum_range' _ (n := J + 1) (by have := hbox.1; omega)]
    refine sum_congr rfl fun j _ => ?_
    rw [coe_eval₂RingHom, eval₂_eq_sum_range' _ (n := W) (by have := hbox.2 j; omega),
      sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [slot_add_mul (mem_range.1 hi)]
    simp [pow_add, pow_mul]
    ring
  rw [h1, ← sum_range_mul_eq (fun n => slot P W n * ((2 : ℤ) ^ b) ^ n)]
  refine sum_subset (range_subset_range.2 hS) fun n _ hn => ?_
  rw [slot_eq_zero hbox (by omega) (by simpa using hn), zero_mul]

/-- **`‖P‖₁` as a slot sum** (for `P` in the box). -/
theorem l1_eq_sum {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) : l1 P = ∑ n ∈ range S, (slot P W n).natAbs := by
  have h1 : l1 P = ∑ j ∈ range (J + 1), ∑ i ∈ range W, (slot P W (i + W * j)).natAbs := by
    rw [l1, liftN_eq_sum_range _ l1Z_zero _ (n := J + 1) (by have := hbox.1; omega)]
    refine sum_congr rfl fun j _ => ?_
    rw [l1Z, liftN_eq_sum_range _ rfl _ (n := W) (by have := hbox.2 j; omega)]
    exact sum_congr rfl fun i hi => by rw [slot_add_mul (mem_range.1 hi)]
  rw [h1, ← sum_range_mul_eq (fun n => (slot P W n).natAbs)]
  refine sum_subset (range_subset_range.2 hS) fun n _ hn => ?_
  rw [slot_eq_zero hbox (by omega) (by simpa using hn), Int.natAbs_zero]

/-! ## Digit sums by divide and conquer (kernel-computable) -/

/-- Sum of `|e - H|` over the `2^d` base-`2^b` digits `e` of `T` (divide and conquer with shifts;
structural recursion through `Nat.rec` for cheap kernel reduction). -/
def digitSum (H b d : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun T => (T - H) + (H - T))
    (fun d ih T => ih (T % (1 <<< (b <<< d))) + ih (T >>> (b <<< d))) d

/-- The offset `∑_{n < 2^d} H X^n` (all digits equal to `H`), by doubling. -/
def offs (H b d : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) H (fun d o => o + (o <<< (b <<< d))) d

/-- **The kernel-computable ℓ¹ norm**: the sum of the absolute values of the balanced base-`2^b`
digits (in `2^d` slots) of an integer. -/
def l1Kron (b d : ℕ) (Nv : ℤ) : ℕ :=
  digitSum (2 ^ (b - 1)) b d (Nv + offs (2 ^ (b - 1)) b d).toNat

theorem digitSum_zero (H b T : ℕ) : digitSum H b 0 T = (T - H) + (H - T) := rfl

theorem digitSum_succ (H b d T : ℕ) :
    digitSum H b (d + 1) T = digitSum H b d (T % 2 ^ (b * 2 ^ d)) +
      digitSum H b d (T / 2 ^ (b * 2 ^ d)) := by
  change digitSum H b d (T % (1 <<< (b <<< d))) + digitSum H b d (T >>> (b <<< d)) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow]

theorem offs_zero (H b : ℕ) : offs H b 0 = H := rfl

theorem offs_succ (H b d : ℕ) : offs H b (d + 1) = offs H b d + offs H b d * 2 ^ (b * 2 ^ d) := by
  change offs H b d + (offs H b d <<< (b <<< d)) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]

/-- A number with `m` digits `< X` is `< X^m`. -/
theorem sum_digits_lt {X : ℕ} (e : ℕ → ℕ) (he : ∀ n, e n < X) (m : ℕ) :
    ∑ n ∈ range m, e n * X ^ n < X ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, pow_succ]
    have := he m
    have h1 : e m * X ^ m ≤ (X - 1) * X ^ m := Nat.mul_le_mul_right _ (by omega)
    have h2 : (X - 1) * X ^ m + X ^ m = X ^ m * X := by
      rw [mul_comm (X ^ m) X]
      have : 1 ≤ X := by omega
      calc (X - 1) * X ^ m + X ^ m = (X - 1 + 1) * X ^ m := by ring
        _ = X * X ^ m := by rw [Nat.sub_add_cancel this]
    omega

/-- Specification of `digitSum`. -/
theorem digitSum_spec (H b : ℕ) (e : ℕ → ℕ) (he : ∀ n, e n < 2 ^ b) (d : ℕ) (off : ℕ) :
    digitSum H b d (∑ n ∈ range (2 ^ d), e (off + n) * (2 ^ b) ^ n) =
      ∑ n ∈ range (2 ^ d), ((e (off + n) - H) + (H - e (off + n))) := by
  induction d generalizing off with
  | zero => simp [digitSum_zero]
  | succ d ih =>
    have hX : (2 : ℕ) ^ (b * 2 ^ d) = (2 ^ b) ^ 2 ^ d := pow_mul 2 b (2 ^ d)
    set A := ∑ n ∈ range (2 ^ d), e (off + n) * (2 ^ b) ^ n
    set B := ∑ n ∈ range (2 ^ d), e (off + 2 ^ d + n) * (2 ^ b) ^ n
    have hsplit : ∑ n ∈ range (2 ^ (d + 1)), e (off + n) * (2 ^ b) ^ n =
        A + (2 ^ b) ^ 2 ^ d * B := by
      rw [pow_succ, mul_two, sum_range_add, mul_sum]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [pow_add, ← add_assoc]; ring
    have hA : A < (2 ^ b) ^ 2 ^ d := sum_digits_lt (fun n => e (off + n)) (fun n => he _) _
    have hpos : 0 < (2 ^ b) ^ 2 ^ d := by positivity
    rw [digitSum_succ, hsplit, hX, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA,
      Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hA, zero_add, ih off, ih (off + 2 ^ d),
      pow_succ, mul_two, sum_range_add]
    congr 1
    exact sum_congr rfl fun n _ => by rw [← add_assoc]

/-- Specification of `offs`. -/
theorem offs_spec (H b d : ℕ) : offs H b d = ∑ n ∈ range (2 ^ d), H * (2 ^ b) ^ n := by
  induction d with
  | zero => simp [offs_zero]
  | succ d ih =>
    rw [offs_succ, ih, pow_succ, mul_two, sum_range_add, pow_mul, sum_mul]
    congr 1
    exact sum_congr rfl fun n _ => by rw [pow_add]; ring

/-- **Exact ℓ¹ norm by Kronecker substitution.** If `P` lies in the box `deg_u ≤ a < W`,
`deg_v ≤ J`, `W (J + 1) ≤ 2^d`, and `‖P‖₁ < 2^(b-1)` (an a priori bound), then `‖P‖₁` equals the
digit sum `l1Kron b d (kron b W P)` of its Kronecker image. -/
theorem l1_eq_l1Kron {P : P2} {a J W b d : ℕ} (hb : 1 ≤ b) (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ 2 ^ d) (hl1 : l1 P < 2 ^ (b - 1)) : l1 P = l1Kron b d (kron b W P) := by
  set H := 2 ^ (b - 1) with hH
  have hX : (2 : ℕ) ^ b = 2 * H := by
    rw [hH, ← pow_succ']; congr 1; omega
  -- slot coefficients are small
  have hc : ∀ n, (slot P W n).natAbs < H := fun n =>
    (natAbs_coeff_le_l1 P _ _).trans_lt hl1
  set e : ℕ → ℕ := fun n => (slot P W n + H).toNat with he_def
  have he_int : ∀ n, ((e n : ℕ) : ℤ) = slot P W n + H := fun n => by
    have := hc n
    rw [he_def]; simp only
    rw [Int.toNat_of_nonneg (by omega)]
  have he_lt : ∀ n, e n < 2 ^ b := fun n => by
    have h1 := he_int n; have h2 := hc n
    rw [hX]; omega
  have hsum : kron b W P + (offs H b d : ℤ) =
      ((∑ n ∈ range (2 ^ d), e n * (2 ^ b) ^ n : ℕ) : ℤ) := by
    rw [kron_eq_sum b hbox ha hS, offs_spec]
    push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [he_int]; ring
  rw [l1Kron, ← hH, hsum, Int.toNat_natCast]
  have := digitSum_spec H b e he_lt d 0
  simp only [zero_add] at this
  rw [this, l1_eq_sum hbox ha hS]
  refine sum_congr rfl fun n _ => ?_
  have h1 := he_int n
  omega

/-! ## Sanity checks -/

/-- Degenerate case: the zero polynomial has digit sum `0`. -/
theorem l1Kron_zero_fixture : l1Kron 8 3 0 = 0 := by decide +kernel

/-- The fixture `P = 3u − 2v + 5` (so `‖P‖₁ = 10`). -/
noncomputable def fixtureP : P2 :=
  monomial 0 (monomial 1 3) - monomial 1 (monomial 0 2) + monomial 0 (monomial 0 5)

/-- Accepted fixture: `‖3u − 2v + 5‖₁ = 10`, computed through the Kronecker image
`5 + 3·2⁸ − 2·2¹⁶` (`b = 8`, `W = 2`, 4 slots) and `l1_eq_l1Kron`. -/
theorem l1_fixtureP : l1 fixtureP = 10 := by
  have hbox : InBox fixtureP 1 1 :=
    ((InBox.monomial 1 0 3).mono le_rfl (by norm_num)).sub
      ((InBox.monomial 0 1 2).mono (by norm_num) le_rfl) |>.add
      ((InBox.monomial 0 0 5).mono (by norm_num) (by norm_num))
  have hl1 : l1 fixtureP ≤ 10 := by
    refine (l1_add_le _ _).trans ?_
    refine (add_le_add (l1_sub_le _ _) le_rfl).trans ?_
    rw [l1_monomial, l1_monomial, l1_monomial]; norm_num
  have hk : kron 8 2 fixtureP = 5 + 3 * 2 ^ 8 - 2 * 2 ^ 16 := by
    simp only [fixtureP, map_add, map_sub, kron_monomial]; norm_num
  rw [l1_eq_l1Kron (a := 1) (J := 1) (W := 2) (b := 8) (d := 2) (by norm_num) hbox (by norm_num)
    (by norm_num) (by omega), hk]
  decide +kernel

/-- Rejected fixture: the a priori bound is necessary. The constant `200 ≥ 2^(b-1) = 128` is read
as the balanced digits `(−56, 1)`, with digit sum `57 ≠ 200`. -/
theorem l1Kron_reject_fixture : l1Kron 8 1 200 = 57 := by decide +kernel

end PlasmaLean.Certificates.Kron2
