/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.Kronecker2DWeighted
public import PlasmaLean.Certificates.KronChebCompute

/-!
# Fast weighted digit sums of packed integers (kernel arithmetic)

Kernel-computable bounds of weighted `ℓ¹` norms of polynomials given by their Kronecker images, with
few kernel reduction steps: a packed integer `T = ∑_{k<n} e_k 2^{bk}` with offset digits
`e_k = g_k + 2^{b−1}` is processed by a constant number of big-integer operations
(`Nat.land`, shifts, products, which the kernel evaluates with GMP), and then cut into blocks.

* `dexp b e n = ∑_{k<n} e_k 2^{bk}` (digit expansions) and their algebra: splitting
  (`dexp_mod`, `dexp_shiftRight`), bitwise `and` of expansions (`land_dexp`), digitwise
  subtraction (`dexp_sub`) and **casting out** `2^b − 1` (`dexp_mod_pred`);
* `absDig b n T`: the expansion of the absolute digits `|e_k − 2^{b−1}|`, computed with masks
  (`absDig_dexp`), i.e. by `O(1)` big-integer operations;
* `rowBlk`: a weighted digit sum along a row by blocks of `L` digits, each block weighted by the
  larger weight at its two ends; for weights that are monotone in the distance to a centre this is
  an upper bound of the exact weighted sum (`sum_le_rowBlk`).

**Sanity.** `dexp_zero`, `absDig_fixture` (a two-digit example), `rowBlk_fixture`.
-/

@[expose] public section

namespace PlasmaLean.Certificates.KronDigits

open Finset

/-- The digit expansion `∑_{k<n} e_k 2^{bk}`. -/
def dexp (b : ℕ) (e : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ range n, e k * 2 ^ (b * k)

/-- **Sanity**: the empty expansion is `0`. -/
@[simp] theorem dexp_zero (b : ℕ) (e : ℕ → ℕ) : dexp b e 0 = 0 := by simp [dexp]

/-- One more digit. -/
theorem dexp_succ (b : ℕ) (e : ℕ → ℕ) (n : ℕ) :
    dexp b e (n + 1) = dexp b e n + e n * 2 ^ (b * n) := by
  simp [dexp, sum_range_succ]

/-- Expansions are bounded by their length. -/
theorem dexp_lt {b : ℕ} {e : ℕ → ℕ} {n : ℕ} (he : ∀ k, k < n → e k < 2 ^ b) :
    dexp b e n < 2 ^ (b * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [dexp_succ]
    have h1 := ih fun k hk => he k (by omega)
    have h2 : e n + 1 ≤ 2 ^ b := he n (by omega)
    calc dexp b e n + e n * 2 ^ (b * n) < 2 ^ (b * n) + e n * 2 ^ (b * n) := by omega
      _ = (e n + 1) * 2 ^ (b * n) := by ring
      _ ≤ 2 ^ b * 2 ^ (b * n) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (b * (n + 1)) := by rw [← pow_add]; ring_nf

/-- Splitting an expansion. -/
theorem dexp_add (b : ℕ) (e : ℕ → ℕ) (m n : ℕ) :
    dexp b e (m + n) = dexp b e m + 2 ^ (b * m) * dexp b (fun k => e (m + k)) n := by
  simp only [dexp, sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [mul_add, pow_add]; ring

/-- The low part of an expansion. -/
theorem dexp_mod {b : ℕ} {e : ℕ → ℕ} {m n : ℕ} (he : ∀ k, k < m + n → e k < 2 ^ b) :
    dexp b e (m + n) % 2 ^ (b * m) = dexp b e m := by
  rw [dexp_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (dexp_lt fun k hk => he k (by omega))]

/-- The high part of an expansion. -/
theorem dexp_shiftRight {b : ℕ} {e : ℕ → ℕ} {m n : ℕ} (he : ∀ k, k < m + n → e k < 2 ^ b) :
    dexp b e (m + n) >>> (b * m) = dexp b (fun k => e (m + k)) n := by
  rw [Nat.shiftRight_eq_div_pow, dexp_add, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (dexp_lt fun k hk => he k (by omega)), zero_add]

/-- Expansions are additive. -/
theorem dexp_add_fun (b : ℕ) (e f : ℕ → ℕ) (n : ℕ) :
    dexp b e n + dexp b f n = dexp b (fun k => e k + f k) n := by
  simp only [dexp, ← sum_add_distrib, add_mul]

/-- Expansions are homogeneous. -/
theorem mul_dexp (b c : ℕ) (e : ℕ → ℕ) (n : ℕ) : c * dexp b e n = dexp b (fun k => c * e k) n := by
  simp only [dexp, mul_sum, mul_assoc]

/-- **Digitwise subtraction**. -/
theorem dexp_sub (b : ℕ) {e f : ℕ → ℕ} (n : ℕ) (h : ∀ k, k < n → f k ≤ e k) :
    dexp b e n - dexp b f n = dexp b (fun k => e k - f k) n := by
  have : dexp b e n = dexp b f n + dexp b (fun k => e k - f k) n := by
    rw [dexp_add_fun]
    refine sum_congr rfl fun k hk => ?_
    simp only [Nat.add_sub_cancel' (h k (mem_range.1 hk))]
  omega

/-- Expansions depend only on the digits below the length. -/
theorem dexp_congr (b : ℕ) {e f : ℕ → ℕ} (n : ℕ) (h : ∀ k, k < n → e k = f k) :
    dexp b e n = dexp b f n :=
  sum_congr rfl fun k hk => by rw [h k (mem_range.1 hk)]

/-- Bitwise `and` of numbers split at the same bit position. -/
theorem land_two_pow_mul_add {m a c x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    (2 ^ m * a + x) &&& (2 ^ m * c + y) = 2 ^ m * (a &&& c) + (x &&& y) := by
  have hxy : x &&& y < 2 ^ m := Nat.lt_of_le_of_lt Nat.and_le_left hx
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ hxy]
  split_ifs <;> simp [Nat.testBit_and]

/-- **Bitwise `and` of expansions** is digitwise. -/
theorem land_dexp {b : ℕ} {e f : ℕ → ℕ} {n : ℕ} (he : ∀ k, k < n → e k < 2 ^ b)
    (hf : ∀ k, k < n → f k < 2 ^ b) :
    dexp b e n &&& dexp b f n = dexp b (fun k => e k &&& f k) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [dexp_succ, dexp_succ, dexp_succ, add_comm (dexp b e n), add_comm (dexp b f n),
      add_comm (dexp b (fun k => e k &&& f k) n), mul_comm (e n), mul_comm (f n),
      mul_comm (e n &&& f n)]
    rw [land_two_pow_mul_add (dexp_lt fun k hk => he k (by omega))
      (dexp_lt fun k hk => hf k (by omega)), ih (fun k hk => he k (by omega))
      (fun k hk => hf k (by omega))]

/-- **Casting out `2^b − 1`**: an expansion is congruent to its digit sum. -/
theorem dexp_mod_pred (b : ℕ) (e : ℕ → ℕ) (n : ℕ) :
    dexp b e n % (2 ^ b - 1) = (∑ k ∈ range n, e k) % (2 ^ b - 1) := by
  have h1 : ∀ k, 2 ^ (b * k) % (2 ^ b - 1) = 1 % (2 ^ b - 1) := fun k => by
    have : 2 ^ b % (2 ^ b - 1) = 1 % (2 ^ b - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ b = m + 1 :=
        ⟨2 ^ b - 1, by have := Nat.one_le_two_pow (n := b); omega⟩
      rw [hm, Nat.add_sub_cancel, Nat.add_mod_left]
    rw [pow_mul, Nat.pow_mod, this, ← Nat.pow_mod, one_pow]
  rw [dexp, Finset.sum_nat_mod, Finset.sum_nat_mod _ _ (fun k => e k)]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.mul_mod, h1, ← Nat.mul_mod, mul_one]

/-- A block sum by casting out, when the digit sum is small. -/
theorem dexp_mod_pred_eq {b : ℕ} {e : ℕ → ℕ} {n : ℕ} (hs : ∑ k ∈ range n, e k < 2 ^ b - 1) :
    dexp b e n % (2 ^ b - 1) = ∑ k ∈ range n, e k := by
  rw [dexp_mod_pred, Nat.mod_eq_of_lt hs]

/-! ## Absolute digits by masks -/

/-- `onesK` is the expansion with all digits `1`. -/
theorem onesK_eq (b n : ℕ) (hb : 1 ≤ b) : onesK b n = dexp b (fun _ => 1) n := by
  have h2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  rw [onesK, Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul, dexp]
  simp only [one_mul, pow_mul]
  rw [Nat.geomSum_eq h2]

/-- `e &&& 2^i` is `2^i` or `0` according to bit `i`. -/
theorem land_two_pow_eq (e i : ℕ) : e &&& 2 ^ i = (e / 2 ^ i % 2) * 2 ^ i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ i) with h | h
  · rw [h, zero_mul, Nat.zero_testBit]
    by_cases hj : i = j
    · subst hj; simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hj]
  · rw [h, one_mul, Nat.testBit_two_pow]
    by_cases hj : i = j
    · subst hj; simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hj]

/-- The sign bit of a digit `e < 2^b` (bit `b − 1`). -/
theorem land_top_eq {b e : ℕ} (hb : 1 ≤ b) (he : e < 2 ^ b) :
    e &&& 2 ^ (b - 1) = (if 2 ^ (b - 1) ≤ e then 1 else 0) * 2 ^ (b - 1) := by
  rw [land_two_pow_eq]
  have hbH : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ']; congr 1; omega
  congr 1
  split_ifs with h
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  · rw [Nat.div_eq_of_lt (by omega)]

/-- **The absolute digits by masks**: for `e_k < 2^b`,
`absDig b n (dexp b e n) = dexp b |e − 2^{b−1}| n`. -/
theorem absDig_dexp {b : ℕ} (hb : 1 ≤ b) {e : ℕ → ℕ} {n : ℕ} (he : ∀ k, k < n → e k < 2 ^ b) :
    absDig b n (dexp b e n) =
      dexp b (fun k => (e k - 2 ^ (b - 1)) + (2 ^ (b - 1) - e k)) n := by
  set H := 2 ^ (b - 1) with hH
  have hbH : 2 ^ b = 2 * H := by rw [hH, ← pow_succ']; congr 1; omega
  have hH1 : 1 ≤ H := Nat.one_le_two_pow
  set σ : ℕ → ℕ := fun k => if H ≤ e k then 1 else 0 with hσ
  have hσle : ∀ k, σ k ≤ 1 := fun k => by simp only [hσ]; split_ifs <;> omega
  have ho : onesK b n = dexp b (fun _ => 1) n := onesK_eq b n hb
  -- the top-bit mask
  have h1 : onesK b n <<< (b - 1) = dexp b (fun _ => H) n := by
    rw [Nat.shiftLeft_eq, ho, mul_comm, mul_dexp]; simp only [mul_one]; rfl
  have h2 : dexp b e n &&& dexp b (fun _ => H) n = H * dexp b σ n := by
    rw [land_dexp he (fun k _ => by rw [hbH]; omega), mul_dexp]
    refine dexp_congr b n fun k hk => ?_
    rw [land_top_eq hb (he k hk), mul_comm]
  have hP : (dexp b e n &&& (onesK b n <<< (b - 1))) >>> (b - 1) = dexp b σ n := by
    rw [h1, h2, Nat.shiftRight_eq_div_pow, ← hH, Nat.mul_div_cancel_left _ (by omega)]
  have h3 : (dexp b σ n <<< b) - dexp b σ n = dexp b (fun k => (2 ^ b - 1) * σ k) n := by
    rw [Nat.shiftLeft_eq, ← mul_dexp, Nat.sub_one_mul, mul_comm]
  have h4 : dexp b e n &&& dexp b (fun k => (2 ^ b - 1) * σ k) n =
      dexp b (fun k => σ k * e k) n := by
    rw [land_dexp he (fun k _ => by
      have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      calc (2 ^ b - 1) * σ k ≤ (2 ^ b - 1) * 1 := Nat.mul_le_mul_left _ (hσle k)
        _ < 2 ^ b := by omega)]
    refine dexp_congr b n fun k hk => ?_
    simp only [hσ]
    split_ifs
    · rw [mul_one, one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (he k hk)]
    · simp
  have h5 : dexp b σ n <<< (b - 1) = dexp b (fun k => σ k * H) n := by
    rw [Nat.shiftLeft_eq, ← hH, mul_comm, mul_dexp]
    exact dexp_congr b n fun k _ => mul_comm _ _
  have h6 : dexp b (fun k => σ k * e k) n - dexp b (fun k => σ k * H) n =
      dexp b (fun k => σ k * e k - σ k * H) n := by
    refine dexp_sub b n fun k hk => ?_
    simp only [hσ]; split_ifs <;> omega
  have h7 : (onesK b n - dexp b σ n) <<< (b - 1) =
      dexp b (fun k => (1 - σ k) * H) n := by
    rw [ho, dexp_sub b n fun k _ => hσle k, Nat.shiftLeft_eq, ← hH, mul_comm, mul_dexp]
    exact dexp_congr b n fun k _ => mul_comm _ _
  have h8 : dexp b e n - dexp b (fun k => σ k * e k) n = dexp b (fun k => e k - σ k * e k) n := by
    refine dexp_sub b n fun k hk => ?_
    have := hσle k; nlinarith
  have h9 : dexp b (fun k => (1 - σ k) * H) n - dexp b (fun k => e k - σ k * e k) n =
      dexp b (fun k => (1 - σ k) * H - (e k - σ k * e k)) n := by
    refine dexp_sub b n fun k hk => ?_
    simp only [hσ]; split_ifs with h <;> omega
  dsimp only [absDig]
  rw [hP, h3, h4, h5, h6, h7, h8, h9, dexp_add_fun]
  refine dexp_congr b n fun k hk => ?_
  simp only [hσ]
  split_ifs with h <;> omega

/-! ## Weighted block sums along a row -/

/-- No fuel: the empty sum. -/
theorem rowBlk_zero (b L : ℕ) (wA : ℕ → ℕ) (i len x : ℕ) : rowBlk b L wA 0 i len x = 0 := rfl

/-- One block of the weighted digit sum. -/
theorem rowBlk_succ (b L : ℕ) (wA : ℕ → ℕ) (f i len x : ℕ) :
    rowBlk b L wA (f + 1) i len x =
      if len ≤ L then (x % ((1 <<< b) - 1)) * max (wA i) (wA (i + len - 1))
      else ((x % (1 <<< (b * L))) % ((1 <<< b) - 1)) * max (wA i) (wA (i + L - 1)) +
        rowBlk b L wA f (i + L) (len - L) (x >>> (b * L)) := rfl

/-- Weights whose value inside any block is at most the larger value at its two ends (for
example, weights monotone in the distance to a centre). -/
def BlockMono (wA : ℕ → ℕ) : Prop := ∀ i m t, t < m → wA (i + t) ≤ max (wA i) (wA (i + m - 1))

/-- **Block sums bound the weighted digit sum of a row**: for digits `a_t < 2^b` with digit sum
below `2^b − 1` and enough fuel, `∑_{t<len} wA(i + t) a_t ≤ rowBlk b L wA f i len (dexp b a len)`.
-/
theorem sum_le_rowBlk {b L : ℕ} {wA : ℕ → ℕ} (hw : BlockMono wA) :
    ∀ (f i len : ℕ) (a : ℕ → ℕ), (∀ t, t < len → a t < 2 ^ b) →
      ∑ t ∈ range len, a t < 2 ^ b - 1 → len ≤ f * L →
      ∑ t ∈ range len, wA (i + t) * a t ≤ rowBlk b L wA f i len (dexp b a len) := by
  have hpred : (1 <<< b) - 1 = 2 ^ b - 1 := by rw [Nat.shiftLeft_eq, one_mul]
  intro f
  induction f with
  | zero =>
    intro i len a _ _ hlen
    have : len = 0 := by simpa using hlen
    subst this; simp [rowBlk_zero]
  | succ f ih =>
    intro i len a ha hs hlen
    rw [rowBlk_succ, hpred]
    split_ifs with hle
    · rw [dexp_mod_pred_eq hs, sum_mul]
      refine sum_le_sum fun t ht => ?_
      rw [mul_comm (wA _)]
      exact Nat.mul_le_mul_left _ (hw i len t (mem_range.1 ht))
    · obtain ⟨m, rfl⟩ : ∃ m, len = L + m := ⟨len - L, by omega⟩
      have h1 : dexp b a (L + m) % (1 <<< (b * L)) = dexp b a L := by
        rw [Nat.shiftLeft_eq, one_mul, dexp_mod ha]
      have h2 : dexp b a (L + m) >>> (b * L) = dexp b (fun t => a (L + t)) m :=
        dexp_shiftRight ha
      rw [sum_range_add] at hs
      have hs1 : ∑ t ∈ range L, a t < 2 ^ b - 1 := by omega
      have hs2 : ∑ t ∈ range m, a (L + t) < 2 ^ b - 1 := by omega
      rw [h1, h2, dexp_mod_pred_eq hs1, sum_range_add, show L + m - L = m by omega]
      refine add_le_add ?_ ?_
      · rw [sum_mul]
        refine sum_le_sum fun t ht => ?_
        rw [mul_comm (wA _)]
        exact Nat.mul_le_mul_left _ (hw i L t (mem_range.1 ht))
      · have := ih (i + L) m (fun t => a (L + t)) (fun t ht => ha _ (by omega)) hs2
          (by rw [Nat.succ_mul] at hlen; omega)
        refine le_trans (le_of_eq ?_) this
        exact sum_congr rfl fun t _ => by rw [add_assoc]

/-- **Sanity**: one block of two digits `3, 5` with unit weights sums to `8`. -/
theorem rowBlk_fixture : rowBlk 8 4 (fun _ => 1) 1 0 2 (3 + 5 * 2 ^ 8) = 8 := by decide +kernel

/-- **Sanity**: the absolute digits of the digits `130, 120` (offset `128`) are `2, 8`. -/
theorem absDig_fixture : absDig 8 2 (130 + 120 * 2 ^ 8) = 2 + 8 * 2 ^ 8 := by decide +kernel

end PlasmaLean.Certificates.KronDigits
