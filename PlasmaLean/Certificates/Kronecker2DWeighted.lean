/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.Kronecker2D
public import PlasmaLean.Theory.KAM.Cohomological

/-!
# Weighted ℓ¹ norms of trigonometric polynomials by Kronecker substitution

The weighted extension of `Certificates/Kronecker2D` needed by the KAM route, stage K3
(`notes/theory/kam-k3-plan.md` §4, lemma 3). `Kronecker2D` computes the plain `ℓ¹` norm of the
coefficients of `P ∈ ℤ[u][v]`. Here the coefficients are weighted by the analytic weight
`e^{r(|k| + |m|)}` of `Theory/KAM/Cohomological` (`weight`, `wnorm`), with the mode `(k, m)`
measured from a chosen centre `(i₀, j₀)`.

**The coefficient function.** `coefZ2 P i₀ j₀ : ℤ × ℤ → ℤ` sends `(k, m)` to the coefficient of
`u^{k+i₀} v^{m+j₀}` in `P`. On the unit torus `u = e^{iθ}`, `v = e^{iψ}`,
`P(u, v) = u^{i₀} v^{j₀} ∑_{k,m} coefZ2 P i₀ j₀ (k, m) e^{i(kθ + mψ)}` (`evalC_exp_eq_fourierSum`,
with `fourierSum` of `Cohomological`). So `coefZ2` gives the genuine Fourier coefficients of the
trigonometric polynomial `u^{−i₀} v^{−j₀} P(u, v)`, and they have finite support.

**Irrational weights.** `e^r` is irrational. Given a rational upper bound `e^r ≤ p / 2^e`, the
weight `e^{rs}` of a mode of size `s` is bounded by the integer `kwtS p e K s = p^s 2^{e(K − s)}`
divided by `2^{eK}` (`exp_mul_le_kwtS`). This holds for every `s`, also for `s > K`, because the
subtraction is truncated, and it is exact as `p / 2^e → e^r` when `s ≤ K`. The weight of mode
`(k, m)` is bounded by the separable product `sepWt` of a `k`-factor and an `m`-factor
(`exp_le_sepWt`).

**Weighted digit sums.** `wl1Kron b d wt Nv` sums `wt n · |e_n|` over the balanced base-`2^b` digits
`e_n` of `Nv` (`wdigitSum`, divide and conquer with an explicit slot offset). If `P` lies in the
degree box and `‖P‖₁ < 2^{b−1}`, then `∑ₙ wt n |slot n| = wl1Kron b d wt (kron b W P)`
(`wsum_eq_wl1Kron`). This is the weighted version of `l1_eq_l1Kron`, with the same hypotheses.
For the kernel, the separable version `wl1Kron2` (row width `2^dc`) computes the same number row
by row (`wl1Kron2_eq`). The column weights are then closed terms shared by all rows, which the
kernel evaluates once. A per-slot weight would cost several big-number operations at each of the
`2^d` slots.

**Main result.** `wnorm_coefZ2_le_wl1Kron2`: under those hypotheses and `e^r ≤ p/2^e`,
`‖coefZ2 P i₀ j₀‖_r · 2^{e(K_i + K_j)} ≤ wl1Kron2 b dc dr wA wB (kron b 2^dc P)`, together with
`InWeighted r`. The right side is one exact kernel computation. The general form for any integer
slot weight is `wnorm_coefZ2_le`.

Algebra of `wnorm` used downstream: `wnorm_smul`, `wnorm_add_le` (with `inWeighted_smul`,
`inWeighted_add`).

**Sanity.** `wl1Kron_zero_wt` (weight `0`), `wl1Kron_fixture` (an accepted fixture with
weights `1, 2, 3`), and `wl1Kron_reject_fixture` (without the a priori bound the digits are
misread).
-/

@[expose] public section

namespace PlasmaLean.Certificates.Kron2

open Polynomial Finset PlasmaLean.Theory.KAM

/-! ## Pruned digit recursions (kernel-computable) -/

/-- Pruned digit recursion: apply `leaf (off + n) e_n` to the first `c` of the `2^d` base-`2^b`
digits `e_n` of `T` (slot offset `off`) and sum. Divide and conquer with shifts. A block with no
kept digits is not visited (structural recursion through `Nat.rec`). -/
def pdig (b : ℕ) (leaf : ℕ → ℕ → ℕ) (d : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ)
    (fun off c T => cond (Nat.beq c 0) 0 (leaf off T))
    (fun d ih off c T => cond (Nat.beq c 0) 0
      (ih off (min c (1 <<< d)) (T % (1 <<< (b <<< d))) +
        ih (off + (1 <<< d)) (c - (1 <<< d)) (T >>> (b <<< d)))) d

/-- `pdig` on a single slot. -/
theorem pdig_zero (b : ℕ) (leaf : ℕ → ℕ → ℕ) (off c T : ℕ) :
    pdig b leaf 0 off c T = cond (Nat.beq c 0) 0 (leaf off T) := rfl

/-- One divide-and-conquer step of `pdig`. -/
theorem pdig_succ (b : ℕ) (leaf : ℕ → ℕ → ℕ) (d off c T : ℕ) :
    pdig b leaf (d + 1) off c T = cond (Nat.beq c 0) 0
      (pdig b leaf d off (min c (2 ^ d)) (T % 2 ^ (b * 2 ^ d)) +
        pdig b leaf d (off + 2 ^ d) (c - 2 ^ d) (T / 2 ^ (b * 2 ^ d))) := by
  change cond (Nat.beq c 0) 0 (pdig b leaf d off (min c (1 <<< d)) (T % (1 <<< (b <<< d))) +
    pdig b leaf d (off + (1 <<< d)) (c - (1 <<< d)) (T >>> (b <<< d))) = _
  simp only [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow]

/-- Specification of `pdig`: on a number with `2^d` digits `e_n < 2^b`, it sums `leaf` over the
first `min c 2^d` digits. -/
theorem pdig_spec (b : ℕ) (leaf : ℕ → ℕ → ℕ) (e : ℕ → ℕ) (he : ∀ n, e n < 2 ^ b) (d : ℕ)
    (off c : ℕ) :
    pdig b leaf d off c (∑ n ∈ range (2 ^ d), e (off + n) * (2 ^ b) ^ n) =
      ∑ n ∈ range (min c (2 ^ d)), leaf (off + n) (e (off + n)) := by
  induction d generalizing off c with
  | zero =>
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [pdig_zero]
    · have h1 : min c 1 = 1 := by omega
      have h2 : Nat.beq c 0 = false := by
        obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
        rfl
      simp [pdig_zero, h1, h2]
  | succ d ih =>
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [pdig_succ]
    have h2 : Nat.beq c 0 = false := by
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      rfl
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
    rw [pdig_succ, h2, Bool.cond_false, hsplit, hX, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hA, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hA, zero_add, ih off,
      ih (off + 2 ^ d)]
    rcases le_or_gt c (2 ^ d) with hcd | hcd
    · have e1 : min c (2 ^ (d + 1)) = min (min c (2 ^ d)) (2 ^ d) := by rw [pow_succ]; omega
      have e2 : min (c - 2 ^ d) (2 ^ d) = 0 := by omega
      rw [e1, e2]; simp
    · have e1 : min c (2 ^ (d + 1)) = 2 ^ d + min (c - 2 ^ d) (2 ^ d) := by rw [pow_succ]; omega
      have e2 : min (min c (2 ^ d)) (2 ^ d) = 2 ^ d := by omega
      rw [e1, e2, sum_range_add]
      congr 1
      exact sum_congr rfl fun n _ => by rw [← add_assoc]

/-- The offset `H (1 + X + ⋯ + X^{W−1})`, `X = 2^b`, of one row of `W` digits. -/
def rowOffs (H b W : ℕ) : ℕ := H * (((1 <<< (b * W)) - 1) / ((1 <<< b) - 1))

/-- `rowOffs` is the offset with all `W` digits equal to `H`. -/
theorem rowOffs_spec (H b W : ℕ) (hb : 1 ≤ b) :
    rowOffs H b W = ∑ i ∈ range W, H * (2 ^ b) ^ i := by
  have h2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  rw [rowOffs, ← mul_sum, Nat.geomSum_eq h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul,
    one_mul, pow_mul]

/-- **The kernel-computable separable weighted ℓ¹ norm**: the balanced base-`2^b` digits of `Nv`
are read as `R` rows of `W` digits (row `j`, column `i`, slot `i + W j`). The result is
`∑_{j < R} wB j ∑_{i < W} wA i |e_{i + W j}|`, computed row by row (rows by `pdig` in base
`2^{bW}`, columns by `pdig` in base `2^b`). The column weights `wA i` are the same closed terms in
every row, so the kernel evaluates each of them once. -/
def wl1KronP (b W dc dr R : ℕ) (wA wB : ℕ → ℕ) (Nv : ℤ) : ℕ :=
  pdig (b * W)
    (fun j T => wB j *
      pdig b (fun i x => wA i * ((x - 2 ^ (b - 1)) + (2 ^ (b - 1) - x))) dc 0 W T) dr 0 R
    (Nv + offs (rowOffs (2 ^ (b - 1)) b W) (b * W) dr).toNat

/-- **Exact separable weighted ℓ¹ norm by Kronecker substitution.** If `P` lies in the box
`deg_u ≤ a < W ≤ 2^dc`, `deg_v ≤ J < 2^dr`, and `‖P‖₁ < 2^(b-1)`, then
`∑_{j ≤ J} wB j ∑_{i < W} wA i |P_{ij}|` is the weighted digit sum `wl1KronP` of the Kronecker
image. -/
theorem wsum_eq_wl1KronP {P : P2} {a J W b dc dr : ℕ} (wA wB : ℕ → ℕ) (hb : 1 ≤ b)
    (hbox : InBox P a J) (ha : a < W) (hW : W ≤ 2 ^ dc) (hJ : J + 1 ≤ 2 ^ dr)
    (hl1 : l1 P < 2 ^ (b - 1)) :
    ∑ j ∈ range (J + 1), wB j * ∑ i ∈ range W, wA i * (slot P W (i + W * j)).natAbs =
      wl1KronP b W dc dr (J + 1) wA wB (kron b W P) := by
  set H := 2 ^ (b - 1) with hH
  have hX : (2 : ℕ) ^ b = 2 * H := by
    rw [hH, ← pow_succ']; congr 1; omega
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
  -- the rows of the offset Kronecker image
  set rowv : ℕ → ℕ := fun j => ∑ i ∈ range W, e (i + W * j) * (2 ^ b) ^ i with hrow
  have hrow_lt : ∀ j, rowv j < 2 ^ (b * W) := fun j => by
    rw [pow_mul]; exact sum_digits_lt (fun i => e (i + W * j)) (fun _ => he_lt _) W
  have hS : W * (J + 1) ≤ W * 2 ^ dr := Nat.mul_le_mul_left W hJ
  have hsum : kron b W P + (offs (rowOffs H b W) (b * W) dr : ℤ) =
      ((∑ j ∈ range (2 ^ dr), rowv (0 + j) * (2 ^ (b * W)) ^ j : ℕ) : ℤ) := by
    rw [kron_eq_sum b hbox ha hS, offs_spec, rowOffs_spec H b W hb,
      sum_range_mul_eq (fun n => slot P W n * ((2 : ℤ) ^ b) ^ n) W (2 ^ dr)]
    push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hrow, zero_add]
    push_cast
    rw [sum_mul, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [he_int, pow_add, pow_mul, ← pow_mul (2 : ℤ) b W]
    ring
  rw [wl1KronP, ← hH, hsum, Int.toNat_natCast,
    pdig_spec (b * W) _ rowv hrow_lt dr 0 (J + 1), min_eq_left hJ]
  refine sum_congr rfl fun j _ => ?_
  simp only [zero_add]
  congr 1
  -- one row: pad the `W` digits to `2^dc`
  set e' : ℕ → ℕ := fun i => if i < W then e (i + W * j) else 0 with he'
  have he'_lt : ∀ i, e' i < 2 ^ b := fun i => by
    simp only [he']; split_ifs
    · exact he_lt _
    · positivity
  have hpad : rowv j = ∑ i ∈ range (2 ^ dc), e' (0 + i) * (2 ^ b) ^ i := by
    simp only [hrow, he', zero_add]
    rw [← sum_subset (range_subset_range.2 hW) fun i _ hi => by
      simp only [mem_range] at hi; simp [hi]]
    exact sum_congr rfl fun i hi => by simp [mem_range.1 hi]
  rw [hpad, pdig_spec b _ e' he'_lt dc 0 W, min_eq_left hW]
  refine sum_congr rfl fun i hi => ?_
  simp only [zero_add, he', mem_range.1 hi, ↓reduceIte]
  congr 1
  have h1 := he_int (i + W * j)
  omega

/-! ## Integer weights dominating `e^{r(|k| + |m|)}` -/

/-- `|i − i₀|` on natural numbers. -/
def ndist (i i₀ : ℕ) : ℕ := (i - i₀) + (i₀ - i)

/-- The integer weight `p^s 2^{e(K − s)}` of a mode of size `s` (truncated subtraction). -/
def kwtS (p e K s : ℕ) : ℕ := p ^ s * 2 ^ (e * (K - s))


/-- `ndist` is the absolute value of the integer difference. -/
theorem ndist_cast (i i₀ : ℕ) : (ndist i i₀ : ℝ) = |(((i : ℤ) - i₀ : ℤ) : ℝ)| := by
  unfold ndist
  have hc : ∀ {x y : ℕ}, x ≤ y → (x : ℝ) ≤ y := fun h => Nat.cast_le.2 h
  rcases le_total i i₀ with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add]
    push_cast [Nat.cast_sub h]
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hc h])]
  · rw [Nat.sub_eq_zero_of_le h, add_zero]
    push_cast [Nat.cast_sub h]
    rw [abs_of_nonneg (by linarith [hc h])]

/-- `(p/2^e)^s · 2^{eK} ≤ p^s 2^{e(K − s)}` for every `s`. -/
theorem pow_div_mul_le (p e K s : ℕ) :
    ((p : ℝ) / 2 ^ e) ^ s * 2 ^ (e * K) ≤ (kwtS p e K s : ℝ) := by
  have h2 : (2 : ℝ) ^ (e * K) ≤ 2 ^ (e * (K - s)) * 2 ^ (e * s) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num)
      (by rw [← mul_add]; exact Nat.mul_le_mul_left e (by omega))
  rw [div_pow, ← pow_mul, div_mul_eq_mul_div, div_le_iff₀ (by positivity), kwtS]
  push_cast
  calc (p : ℝ) ^ s * 2 ^ (e * K) ≤ (p : ℝ) ^ s * (2 ^ (e * (K - s)) * 2 ^ (e * s)) := by gcongr
    _ = _ := by ring

/-- The analytic weight of a mode of size `s` is dominated by the integer weight. -/
theorem exp_mul_le_kwtS {r : ℝ} {p e : ℕ} (hq : Real.exp r ≤ p / 2 ^ e) (K s : ℕ) :
    Real.exp (r * s) * 2 ^ (e * K) ≤ (kwtS p e K s : ℝ) := by
  refine le_trans ?_ (pow_div_mul_le p e K s)
  rw [mul_comm r, Real.exp_nat_mul]
  gcongr

/-- The separable integer weight of Kronecker slot `n`, mode `(n % W − i₀, n / W − j₀)`:
`p^{s_j} 2^{e(K_j − s_j)} · p^{s_i} 2^{e(K_i − s_i)}`. -/
def sepWt (p e W i₀ j₀ Ki Kj n : ℕ) : ℕ :=
  kwtS p e Kj (ndist (n / W) j₀) * kwtS p e Ki (ndist (n % W) i₀)

/-- The analytic weight of slot `n` is dominated by the separable integer weight. -/
theorem exp_le_sepWt {r : ℝ} {p e : ℕ} (hq : Real.exp r ≤ p / 2 ^ e) (W i₀ j₀ Ki Kj n : ℕ) :
    Real.exp (r * ((ndist (n % W) i₀ + ndist (n / W) j₀ : ℕ) : ℝ)) * 2 ^ (e * (Ki + Kj)) ≤
      (sepWt p e W i₀ j₀ Ki Kj n : ℝ) := by
  have h1 := exp_mul_le_kwtS hq Ki (ndist (n % W) i₀)
  have h2 := exp_mul_le_kwtS hq Kj (ndist (n / W) j₀)
  rw [sepWt, Nat.cast_mul, Nat.cast_add, mul_add, Real.exp_add, mul_add, pow_add]
  calc _ = (Real.exp (r * (ndist (n / W) j₀ : ℕ)) * 2 ^ (e * Kj)) *
        (Real.exp (r * (ndist (n % W) i₀ : ℕ)) * 2 ^ (e * Ki)) := by ring
    _ ≤ _ := mul_le_mul h2 h1 (by positivity) (by positivity)

/-! ## Fourier coefficients of a bivariate polynomial -/

/-- The coefficient of `u^{k+i₀} v^{m+j₀}` in `P` (zero if an exponent is negative): the
Fourier coefficient of mode `(k, m)` of `u^{−i₀} v^{−j₀} P(u, v)` on the unit torus. -/
noncomputable def coefZ2 (P : P2) (i₀ j₀ : ℕ) (km : ℤ × ℤ) : ℤ :=
  if 0 ≤ km.1 + i₀ ∧ 0 ≤ km.2 + j₀ then (P.coeff (km.2 + j₀).toNat).coeff (km.1 + i₀).toNat
  else 0

/-- The mode `(n % W − i₀, n / W − j₀)` of Kronecker slot `n`. -/
def slotMode (W i₀ j₀ n : ℕ) : ℤ × ℤ := (((n % W : ℕ) : ℤ) - i₀, ((n / W : ℕ) : ℤ) - j₀)

/-- Distinct slots have distinct modes. -/
theorem slotMode_injective (W i₀ j₀ : ℕ) : Function.Injective (slotMode W i₀ j₀) := by
  intro n n' h
  simp only [slotMode, Prod.mk.injEq, sub_left_inj, Nat.cast_inj] at h
  rw [← Nat.mod_add_div n W, ← Nat.mod_add_div n' W, h.1, h.2]

/-- `coefZ2` at the mode of slot `n` is the slot coefficient. -/
theorem coefZ2_slotMode (P : P2) (W i₀ j₀ n : ℕ) :
    coefZ2 P i₀ j₀ (slotMode W i₀ j₀ n) = slot P W n := by
  unfold coefZ2 slotMode slot
  simp only [sub_add_cancel, Int.toNat_natCast, Int.natCast_nonneg, and_self, ↓reduceIte]

/-- `slotMode` of `i + W j` for `i < W`. -/
theorem slotMode_add_mul {W i j : ℕ} (hi : i < W) (i₀ j₀ : ℕ) :
    slotMode W i₀ j₀ (i + W * j) = ((i : ℤ) - i₀, (j : ℤ) - j₀) := by
  have hW : 0 < W := by omega
  rw [slotMode, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hi, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

/-- Outside the slot modes of the box, `coefZ2` vanishes. -/
theorem coefZ2_eq_zero {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {km : ℤ × ℤ}
    (hkm : km ∉ (range S).image (slotMode W i₀ j₀)) : coefZ2 P i₀ j₀ km = 0 := by
  unfold coefZ2
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    by_contra hne
    apply hkm
    set i := (km.1 + i₀).toNat with hi_def
    set j := (km.2 + j₀).toNat with hj_def
    have hj : j ≤ J := by
      by_contra hj
      exact hne (by
        rw [coeff_eq_zero_of_natDegree_lt (hbox.1.trans_lt (not_le.mp hj))]; simp)
    have hi : i ≤ a := by
      by_contra hi
      exact hne (coeff_eq_zero_of_natDegree_lt ((hbox.2 j).trans_lt (not_le.mp hi)))
    have hiW : i < W := by omega
    refine mem_image.2 ⟨i + W * j, mem_range.2 ?_, ?_⟩
    · calc i + W * j < W + W * J := by
            have := Nat.mul_le_mul_left W hj; omega
        _ = W * (J + 1) := by ring
        _ ≤ S := hS
    · rw [slotMode_add_mul hiW]
      have e1 : ((i : ℕ) : ℤ) = km.1 + i₀ := Int.toNat_of_nonneg h1
      have e2 : ((j : ℕ) : ℤ) = km.2 + j₀ := Int.toNat_of_nonneg h2
      ext <;> simp only <;> omega
  · rfl

/-- `P(u, v)` as a slot sum, for `P` in the box. -/
theorem evalC_eq_sum_slot {P : P2} {a J W S : ℕ} (u v : ℂ) (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) :
    evalC u v P = ∑ n ∈ range S, (slot P W n : ℂ) * (u ^ (n % W) * v ^ (n / W)) := by
  have h1 : evalC u v P = ∑ j ∈ range (J + 1), ∑ i ∈ range W,
      (slot P W (i + W * j) : ℂ) * (u ^ ((i + W * j) % W) * v ^ ((i + W * j) / W)) := by
    rw [evalC, coe_eval₂RingHom, eval₂_eq_sum_range' _ (n := J + 1) (by have := hbox.1; omega)]
    refine sum_congr rfl fun j _ => ?_
    rw [coe_eval₂RingHom, eval₂_eq_sum_range' _ (n := W) (by have := hbox.2 j; omega), sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [slot_add_mul hi', Nat.add_mul_div_left _ _ (by omega : 0 < W), Nat.div_eq_of_lt hi',
      zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']
    simp only [eq_intCast]
    ring
  rw [h1, ← sum_range_mul_eq (fun n => (slot P W n : ℂ) * (u ^ (n % W) * v ^ (n / W)))]
  refine sum_subset (range_subset_range.2 hS) fun n _ hn => ?_
  rw [slot_eq_zero hbox (by omega) (by simpa using hn)]
  simp

/-- `coefZ2` has finite support (contained in the slot modes of the box). -/
theorem summable_coefZ2 {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) (F : ℤ × ℤ → ℂ → ℝ) (hF : ∀ km, F km 0 = 0) :
    Summable fun km => F km (coefZ2 P i₀ j₀ km : ℂ) :=
  summable_of_ne_finset_zero (s := (range S).image (slotMode W i₀ j₀)) fun km hkm => by
    rw [coefZ2_eq_zero hbox ha hS i₀ j₀ hkm]; simp [hF]

/-- **Fourier expansion on the unit torus**: `P(e^{iθ}, e^{iψ}) = e^{i i₀ θ} e^{i j₀ ψ} ·
∑_{k,m} coefZ2 P i₀ j₀ (k, m) e^{i(kθ + mψ)}`. -/
theorem evalC_exp_eq_fourierSum {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) (θ ψ : ℝ) :
    evalC (Complex.exp (θ * Complex.I)) (Complex.exp (ψ * Complex.I)) P =
      Complex.exp (θ * Complex.I) ^ i₀ * Complex.exp (ψ * Complex.I) ^ j₀ *
        fourierSum (fun km => (coefZ2 P i₀ j₀ km : ℂ)) θ ψ := by
  have hfin : fourierSum (fun km => (coefZ2 P i₀ j₀ km : ℂ)) θ ψ =
      ∑ n ∈ range S, (slot P W n : ℂ) * fourierMode (slotMode W i₀ j₀ n) θ ψ := by
    rw [fourierSum, tsum_eq_sum (s := (range S).image (slotMode W i₀ j₀)) fun km hkm => by
      rw [coefZ2_eq_zero hbox ha hS i₀ j₀ hkm]; simp,
      sum_image fun x _ y _ h => slotMode_injective W i₀ j₀ h]
    exact sum_congr rfl fun n _ => by rw [coefZ2_slotMode]
  have key0 : ∀ A B : ℕ, Complex.exp (θ * Complex.I) ^ i₀ * Complex.exp (ψ * Complex.I) ^ j₀ *
      fourierMode ((A : ℤ) - i₀, (B : ℤ) - j₀) θ ψ =
        Complex.exp (θ * Complex.I) ^ A * Complex.exp (ψ * Complex.I) ^ B := by
    intro A B
    simp only [fourierMode, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : ∀ n, Complex.exp (θ * Complex.I) ^ i₀ * Complex.exp (ψ * Complex.I) ^ j₀ *
      fourierMode (slotMode W i₀ j₀ n) θ ψ =
        Complex.exp (θ * Complex.I) ^ (n % W) * Complex.exp (ψ * Complex.I) ^ (n / W) :=
    fun n => key0 _ _
  rw [hfin, evalC_eq_sum_slot _ _ hbox ha hS, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [← key]; ring

/-- Products of `coefZ2` with any function are summable (finite support). -/
theorem summable_coefZ2_mul {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) (g : ℤ × ℤ → ℂ) :
    Summable fun km => (coefZ2 P i₀ j₀ km : ℂ) * g km :=
  summable_of_ne_finset_zero (s := (range S).image (slotMode W i₀ j₀)) fun km hkm => by
    rw [coefZ2_eq_zero hbox ha hS i₀ j₀ hkm]; simp

/-- **Reading off Fourier coefficients**: if `P(e^{iθ}, e^{iψ}) = c f e^{i i₀ θ} e^{i j₀ ψ}` with
`c ≠ 0`, then `f` is the Fourier series of `c⁻¹ coefZ2 P i₀ j₀` at `(θ, ψ)`. -/
theorem eq_fourierSum_of_evalC {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {θ ψ : ℝ} {c f : ℂ} (hc : c ≠ 0)
    (h : evalC (Complex.exp (θ * Complex.I)) (Complex.exp (ψ * Complex.I)) P =
      c * f * (Complex.exp (θ * Complex.I) ^ i₀ * Complex.exp (ψ * Complex.I) ^ j₀)) :
    f = fourierSum (fun km => c⁻¹ * coefZ2 P i₀ j₀ km) θ ψ := by
  rw [evalC_exp_eq_fourierSum hbox ha hS i₀ j₀ θ ψ] at h
  have hU : Complex.exp (θ * Complex.I) ^ i₀ * Complex.exp (ψ * Complex.I) ^ j₀ ≠ 0 := by
    simp [Complex.exp_ne_zero]
  have h' : fourierSum (fun km => (coefZ2 P i₀ j₀ km : ℂ)) θ ψ = c * f := by
    apply mul_left_cancel₀ hU; rw [h]; ring
  simp only [fourierSum, mul_assoc] at h' ⊢
  rw [tsum_mul_left, h', inv_mul_cancel_left₀ hc]

/-- Linearity of `fourierSum` for summable data. -/
theorem fourierSum_add {f g : ℤ × ℤ → ℂ} {θ ψ : ℝ}
    (hf : Summable fun km => f km * fourierMode km θ ψ)
    (hg : Summable fun km => g km * fourierMode km θ ψ) :
    fourierSum (fun km => f km + g km) θ ψ = fourierSum f θ ψ + fourierSum g θ ψ := by
  simp only [fourierSum, add_mul]; exact hf.tsum_add hg

/-- The Fourier data `c · coefZ2 P i₀ j₀` are summable against the modes. -/
theorem summable_smul_coefZ2_mode {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) (c : ℂ) (θ ψ : ℝ) :
    Summable fun km => c * coefZ2 P i₀ j₀ km * fourierMode km θ ψ := by
  simpa [mul_assoc] using
    (summable_coefZ2_mul hbox ha hS i₀ j₀ (fun km => fourierMode km θ ψ)).mul_left c

/-! ## The weighted norm of `coefZ2` -/

/-- The mode size of slot `n` is the natural `ndist` sum. -/
theorem modeSize_slotMode (W i₀ j₀ n : ℕ) :
    modeSize (slotMode W i₀ j₀ n) = ((ndist (n % W) i₀ + ndist (n / W) j₀ : ℕ) : ℝ) := by
  rw [modeSize, slotMode, Nat.cast_add, ndist_cast, ndist_cast]

/-- **Weighted norm of the Fourier coefficients of `P`**, bounded by an integer slot sum for any
integer slot weight `wt` dominating `C e^{r(|k| + |m|)}`. -/
theorem wnorm_coefZ2_le {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {r C : ℝ} (wt : ℕ → ℕ)
    (hwt : ∀ n, Real.exp (r * ((ndist (n % W) i₀ + ndist (n / W) j₀ : ℕ) : ℝ)) * C ≤ wt n) :
    InWeighted r (fun km => (coefZ2 P i₀ j₀ km : ℂ)) ∧
      wnorm r (fun km => (coefZ2 P i₀ j₀ km : ℂ)) * C ≤
        ((∑ n ∈ range S, wt n * (slot P W n).natAbs : ℕ) : ℝ) := by
  refine ⟨summable_coefZ2 hbox ha hS i₀ j₀ (fun km c => ‖c‖ * weight r km) (by simp), ?_⟩
  have hfin : wnorm r (fun km => (coefZ2 P i₀ j₀ km : ℂ)) =
      ∑ n ∈ range S, ‖(slot P W n : ℂ)‖ * weight r (slotMode W i₀ j₀ n) := by
    rw [wnorm, tsum_eq_sum (s := (range S).image (slotMode W i₀ j₀)) fun km hkm => by
      rw [coefZ2_eq_zero hbox ha hS i₀ j₀ hkm]; simp,
      sum_image fun x _ y _ h => slotMode_injective W i₀ j₀ h]
    exact sum_congr rfl fun n _ => by rw [coefZ2_slotMode]
  rw [hfin, sum_mul, Nat.cast_sum]
  refine sum_le_sum fun n _ => ?_
  rw [Complex.norm_intCast, mul_assoc, Nat.cast_mul, mul_comm (wt n : ℝ), Nat.cast_natAbs,
    Int.cast_abs]
  gcongr
  rw [weight, modeSize_slotMode]
  exact hwt n

/-- **Weighted norm by one kernel computation.** Under the hypotheses of `wsum_eq_wl1KronP` and
`e^r ≤ p / 2^e`, the coefficients of `P` centred at `(i₀, j₀)` lie in `ℓ¹_r` and
`‖coefZ2 P i₀ j₀‖_r · 2^{e(K_i + K_j)}` is at most the separable weighted digit sum of the
Kronecker image, with column weights `p^{s} 2^{e(K_i − s)}`, `s = |i − i₀|`, and row weights
`p^{s} 2^{e(K_j − s)}`, `s = |j − j₀|`. -/
theorem wnorm_coefZ2_le_wl1KronP {P : P2} {a J W b dc dr : ℕ} (hb : 1 ≤ b) (hbox : InBox P a J)
    (ha : a < W) (hW : W ≤ 2 ^ dc) (hJ : J + 1 ≤ 2 ^ dr) (hl1 : l1 P < 2 ^ (b - 1)) (i₀ j₀ : ℕ)
    {r : ℝ} {p e : ℕ} (hq : Real.exp r ≤ p / 2 ^ e) (Ki Kj : ℕ) :
    InWeighted r (fun km => (coefZ2 P i₀ j₀ km : ℂ)) ∧
      wnorm r (fun km => (coefZ2 P i₀ j₀ km : ℂ)) * 2 ^ (e * (Ki + Kj)) ≤
        wl1KronP b W dc dr (J + 1) (fun i => kwtS p e Ki (ndist i i₀))
          (fun j => kwtS p e Kj (ndist j j₀)) (kron b W P) := by
  obtain ⟨h1, h2⟩ := wnorm_coefZ2_le hbox ha le_rfl i₀ j₀ (sepWt p e W i₀ j₀ Ki Kj)
    (fun n => exp_le_sepWt hq _ i₀ j₀ Ki Kj n)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [← wsum_eq_wl1KronP _ _ hb hbox ha hW hJ hl1,
    sum_range_mul_eq (fun n => sepWt p e W i₀ j₀ Ki Kj n * (slot P W n).natAbs) W (J + 1)]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have hW0 : 0 < W := by omega
  rw [sepWt, Nat.add_mul_div_left _ _ hW0, Nat.div_eq_of_lt hi', zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']
  ring

/-! ## Algebra of the weighted norm -/

/-- `ℓ¹_r` is closed under scalar multiplication. -/
theorem inWeighted_smul {r : ℝ} {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) (c : ℂ) :
    InWeighted r (fun km => c * f km) := by
  unfold InWeighted at *
  simpa [norm_mul, mul_assoc] using hf.mul_left ‖c‖

/-- `‖c f‖_r = |c| ‖f‖_r`. -/
theorem wnorm_smul (r : ℝ) (c : ℂ) (f : ℤ × ℤ → ℂ) :
    wnorm r (fun km => c * f km) = ‖c‖ * wnorm r f := by
  simp only [wnorm, norm_mul, mul_assoc]
  exact tsum_mul_left

/-- `ℓ¹_r` is closed under addition. -/
theorem inWeighted_add {r : ℝ} {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f) (hg : InWeighted r g) :
    InWeighted r (fun km => f km + g km) :=
  (hf.add hg).of_nonneg_of_le (fun km => by have := weight_pos r km; positivity)
    (fun km => by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (weight_pos r km).le)

/-- Triangle inequality `‖f + g‖_r ≤ ‖f‖_r + ‖g‖_r`. -/
theorem wnorm_add_le {r : ℝ} {f g : ℤ × ℤ → ℂ} (hf : InWeighted r f) (hg : InWeighted r g) :
    wnorm r (fun km => f km + g km) ≤ wnorm r f + wnorm r g := by
  unfold wnorm
  rw [← hf.tsum_add hg]
  exact (inWeighted_add hf hg).tsum_le_tsum
    (fun km => by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (weight_pos r km).le)
    (hf.add hg)

/-! ## Sanity checks -/

/-- Degenerate case: zero column weights give weighted digit sum `0`. -/
theorem wl1KronP_zero_wt :
    wl1KronP 8 2 1 1 2 (fun _ => 0) (fun _ => 1) (5 + 3 * 2 ^ 8 - 2 * 2 ^ 16) = 0 := by
  decide +kernel

/-- Accepted fixture: the Kronecker image of `3u − 2v + 5` (`b = 8`, `W = 2`, two rows) has
balanced digits `(5, 3)` in row `0` and `(−2, 0)` in row `1`. With column weights `1, 2` and row
weights `1, 10` the weighted digit sum is `(5·1 + 3·2) + 10·(2·1) = 31`. -/
theorem wl1KronP_fixture :
    wl1KronP 8 2 1 1 2 (fun i => i + 1) (fun j => 9 * j + 1) (5 + 3 * 2 ^ 8 - 2 * 2 ^ 16) =
      31 := by
  decide +kernel

/-- Pruning: reading only the first row of the same image gives `5·1 + 3·2 = 11`. -/
theorem wl1KronP_prune_fixture :
    wl1KronP 8 2 1 1 1 (fun i => i + 1) (fun j => 9 * j + 1) (5 + 3 * 2 ^ 8 - 2 * 2 ^ 16) =
      11 := by
  decide +kernel

/-- Rejected fixture: without the a priori bound, the constant `200 ≥ 2^(b-1) = 128` is read as
the balanced digits `(−56, 1)`; with unit weights the digit sum is `57 ≠ 200`. -/
theorem wl1KronP_reject_fixture : wl1KronP 8 2 1 0 1 (fun _ => 1) (fun _ => 1) 200 = 57 := by
  decide +kernel

end PlasmaLean.Certificates.Kron2
