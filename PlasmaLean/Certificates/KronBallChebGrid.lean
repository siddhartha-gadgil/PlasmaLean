/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallChebNorm

/-!
# Grid families: compact storage and fast Kronecker images

Family centres (`Certificates/KronBallCheb`) given by integer grids stored compactly, and their
Kronecker images computed by the kernel with few reduction steps.

**Storage of one Chebyshev coefficient** (`SliceData`): a stellarator-symmetric grid
`g = symGrid N M s h` (`g(2N − i, 2M − j) = s g(i, j)`) in a smaller box `|i − N| ≤ N_j`,
`|j − M| ≤ M_j`, given by the right halves `i > N` of its rows (one literal for all rows, fields of
`F_j` bits) and the centre column `i = N, j ≥ M` (one literal); an affine symbol
`a (i − N) + b (j − M)` may multiply the grid (derivatives, transport operators).

**Fast images.** `rpack`, `rpackR`: `∑_t (α + β t) f_t 2^{bt}` of the fields of a literal (and of
the reversed fields) by divide and conquer; `rowV`: the image of one grid row from two literals
(the row and its mirror) and the centre column; `slicePack`: the image of the coefficient
(`slicePack_eq`: `= kron b W (gridPolyNM N M g)`); `famPack`: the image of a `w`-symmetric family
`∑_{|k| ≤ D'} w^{D + k} g_{|k|}` (`famPack_eq`: `= kron b W (flat R (gridPoly3 …))`).

**Sanity.** `rpack_fixture`, `bsplit_zero`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.KronBallCheb

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronDigits PlasmaLean.Theory.KAM
  Complex

/-! ## Packing the fields of a literal -/

/-- `fieldZ` is `fieldW`. -/
theorem fieldZ_eq (F x t : ℕ) : fieldZ F x t = fieldW F x t := by
  simp only [fieldZ, fieldW, Nat.shiftLeft_eq, one_mul]
  push_cast
  rfl

/-- Fields of the low part of a literal. -/
theorem fieldW_mod {F x h t : ℕ} (ht : t < h) :
    fieldW F (x % (1 <<< (F * h))) t = fieldW F x t := by
  unfold fieldW
  have h1 : F * h = F * t + F * (h - t) := by rw [← mul_add]; congr 1; omega
  have h2 : (x % (1 <<< (F * h))) >>> (F * t) % 2 ^ F = x >>> (F * t) % 2 ^ F := by
    rw [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, h1,
      pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
    exact pow_dvd_pow 2 (by nlinarith [show 1 ≤ h - t by omega])
  rw [h2]

/-- Fields of the high part of a literal. -/
theorem fieldW_shiftRight {F x h t : ℕ} :
    fieldW F (x >>> (F * h)) t = fieldW F x (h + t) := by
  unfold fieldW
  rw [mul_add, Nat.shiftRight_add]

/-- **`rpack` computes the weighted field sum.** -/
theorem rpack_eq (b F : ℕ) : ∀ (d : ℕ) (α β : ℤ) (n x : ℕ), n ≤ 2 ^ d →
    rpack b F α β d n x = ∑ t ∈ range n, (α + β * t) * fieldW F x t * (2 : ℤ) ^ (b * t)
  | 0, α, β, n, x, hn => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hn) with rfl | rfl <;>
      simp [rpack, fieldZ_eq]
  | d + 1, α, β, n, x, hn => by
    rw [rpack]
    split_ifs with h1 h0
    · subst h0; simp
    · have : n = 1 := by omega
      subst this; simp [fieldZ_eq]
    · rw [rpack_eq b F d α β (n / 2) _ (by rw [pow_succ] at hn; omega),
        rpack_eq b F d _ β (n - n / 2) _ (by rw [pow_succ] at hn; omega)]
      conv_rhs => rw [show n = n / 2 + (n - n / 2) by omega, sum_range_add]
      congr 1
      · exact sum_congr rfl fun t ht => by rw [fieldW_mod (mem_range.1 ht)]
      · rw [sum_mul]
        refine sum_congr rfl fun t _ => ?_
        rw [fieldW_shiftRight, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
          Nat.cast_add, mul_add b, pow_add]
        ring

/-- **`rpackR` computes the weighted sum of the reversed fields.** -/
theorem rpackR_eq (b F : ℕ) : ∀ (d : ℕ) (α β : ℤ) (n x : ℕ), n ≤ 2 ^ d →
    rpackR b F α β d n x =
      ∑ t ∈ range n, (α + β * t) * fieldW F x (n - 1 - t) * (2 : ℤ) ^ (b * t)
  | 0, α, β, n, x, hn => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hn) with rfl | rfl <;>
      simp [rpackR, fieldZ_eq]
  | d + 1, α, β, n, x, hn => by
    rw [rpackR]
    split_ifs with h1 h0
    · subst h0; simp
    · have : n = 1 := by omega
      subst this; simp [fieldZ_eq]
    · rw [rpackR_eq b F d α β (n - n / 2) _ (by rw [pow_succ] at hn; omega),
        rpackR_eq b F d _ β (n / 2) _ (by rw [pow_succ] at hn; omega)]
      conv_rhs => rw [show n = (n - n / 2) + n / 2 by omega, sum_range_add]
      congr 1
      · refine sum_congr rfl fun t ht => ?_
        have ht' := mem_range.1 ht
        rw [fieldW_shiftRight]
        congr 3
        omega
      · rw [sum_mul]
        refine sum_congr rfl fun t ht => ?_
        have ht' := mem_range.1 ht
        rw [fieldW_mod (by omega), Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
          Nat.cast_add, mul_add b, pow_add,
          show n - n / 2 + n / 2 - 1 - (n - n / 2 + t) = n / 2 - 1 - t by omega]
        ring

/-- **Sanity**: two fields `3, 5` of width `4` (offset `8`) are `−5, −3`. -/
theorem rpack_fixture : rpack 8 4 1 0 1 2 (3 + 5 * 16) = -5 + (-3) * 2 ^ 8 := by decide +kernel

/-! ## Packing with natural numbers only (offset digits) -/

/-- The offset digit of a raw field `f` (`0 ≤ f < 2^F`): `m f + c`, or `c − m f` (`neg`). -/
def digN (m c : ℕ) (neg : Bool) (f : ℕ) : ℕ := if neg then c - m * f else m * f + c

/-- `∑_{t<n} digN(raw_t) 2^{bt}` for the raw fields `raw_t = ⌊x / 2^{Ft}⌋ mod 2^F` of `x`, with
natural numbers only (fast in the kernel). -/
def rpN (b F m c : ℕ) (neg : Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, n, x => if n = 0 then 0 else digN m c neg (x % (1 <<< F))
  | d + 1, n, x => if n ≤ 1 then (if n = 0 then 0 else digN m c neg (x % (1 <<< F))) else
      rpN b F m c neg d (n / 2) (x % (1 <<< (F * (n / 2)))) +
        (rpN b F m c neg d (n - n / 2) (x >>> (F * (n / 2))) <<< (b * (n / 2)))

/-- The reversed version of `rpN`. -/
def rpNR (b F m c : ℕ) (neg : Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, n, x => if n = 0 then 0 else digN m c neg (x % (1 <<< F))
  | d + 1, n, x => if n ≤ 1 then (if n = 0 then 0 else digN m c neg (x % (1 <<< F))) else
      rpNR b F m c neg d (n - n / 2) (x >>> (F * (n / 2))) +
        (rpNR b F m c neg d (n / 2) (x % (1 <<< (F * (n / 2)))) <<< (b * (n - n / 2)))

/-- The lowest raw field. -/
theorem rawF_zero (F x : ℕ) : x % (1 <<< F) = rawF F x 0 := by
  simp [rawF, Nat.shiftLeft_eq]

/-- Raw fields of the low part of a literal. -/
theorem rawF_mod {F x h t : ℕ} (ht : t < h) : rawF F (x % (1 <<< (F * h))) t = rawF F x t := by
  have h1 : F * h = F * t + F * (h - t) := by rw [← mul_add]; congr 1; omega
  simp only [rawF]
  rw [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, h1,
    pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 2 (by nlinarith [show 1 ≤ h - t by omega])

/-- Raw fields of the high part of a literal. -/
theorem rawF_shiftRight {F x h t : ℕ} : rawF F (x >>> (F * h)) t = rawF F x (h + t) := by
  simp only [rawF]
  rw [mul_add, Nat.shiftRight_add]

/-- **`rpN` computes the digit sum.** -/
theorem rpN_eq (b F m c : ℕ) (neg : Bool) : ∀ (d n x : ℕ), n ≤ 2 ^ d →
    rpN b F m c neg d n x = ∑ t ∈ range n, digN m c neg (rawF F x t) * 2 ^ (b * t)
  | 0, n, x, hn => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hn) with rfl | rfl <;>
      simp [rpN, rawF_zero]
  | d + 1, n, x, hn => by
    rw [rpN]
    split_ifs with h1 h0
    · subst h0; simp
    · have : n = 1 := by omega
      subst this; simp [rawF_zero]
    · rw [rpN_eq b F m c neg d (n / 2) _ (by rw [pow_succ] at hn; omega),
        rpN_eq b F m c neg d (n - n / 2) _ (by rw [pow_succ] at hn; omega)]
      conv_rhs => rw [show n = n / 2 + (n - n / 2) by omega, sum_range_add]
      congr 1
      · exact sum_congr rfl fun t ht => by rw [rawF_mod (mem_range.1 ht)]
      · rw [Nat.shiftLeft_eq, sum_mul]
        refine sum_congr rfl fun t _ => ?_
        rw [rawF_shiftRight, mul_add b, pow_add]; ring

/-- **`rpNR` computes the reversed digit sum.** -/
theorem rpNR_eq (b F m c : ℕ) (neg : Bool) : ∀ (d n x : ℕ), n ≤ 2 ^ d →
    rpNR b F m c neg d n x = ∑ t ∈ range n, digN m c neg (rawF F x (n - 1 - t)) * 2 ^ (b * t)
  | 0, n, x, hn => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hn) with rfl | rfl <;>
      simp [rpNR, rawF_zero]
  | d + 1, n, x, hn => by
    rw [rpNR]
    split_ifs with h1 h0
    · subst h0; simp
    · have : n = 1 := by omega
      subst this; simp [rawF_zero]
    · rw [rpNR_eq b F m c neg d (n - n / 2) _ (by rw [pow_succ] at hn; omega),
        rpNR_eq b F m c neg d (n / 2) _ (by rw [pow_succ] at hn; omega)]
      conv_rhs => rw [show n = (n - n / 2) + n / 2 by omega, sum_range_add]
      congr 1
      · refine sum_congr rfl fun t ht => ?_
        have ht' := mem_range.1 ht
        rw [rawF_shiftRight]
        congr 3
        omega
      · rw [Nat.shiftLeft_eq, sum_mul]
        refine sum_congr rfl fun t ht => ?_
        have ht' := mem_range.1 ht
        rw [rawF_mod (by omega), mul_add b, pow_add,
          show n - n / 2 + n / 2 - 1 - (n - n / 2 + t) = n / 2 - 1 - t by omega]
        ring

/-- `fieldW` through the raw field. -/
theorem fieldW_eq_rawF (F x t : ℕ) : fieldW F x t = (rawF F x t : ℤ) - 2 ^ (F - 1) := by
  simp [fieldW, rawF]

/-! ## Divide-and-conquer sums -/

/-- No levels: at most one term. -/
theorem bsplitN_zero (f : ℕ → ℕ) (B s n : ℕ) :
    bsplitN f B 0 s n = if n = 0 then 0 else f s := rfl

/-- One level of the divide and conquer. -/
theorem bsplitN_succ (f : ℕ → ℕ) (B d s n : ℕ) :
    bsplitN f B (d + 1) s n = if n ≤ 1 then (if n = 0 then 0 else f s) else
      bsplitN f B d s (n / 2) + (bsplitN f B d (s + n / 2) (n - n / 2) <<< (B * (n / 2))) := rfl

/-- `bsplitN` computes the sum. -/
theorem bsplitN_eq (f : ℕ → ℕ) (B : ℕ) : ∀ (d s n : ℕ), n ≤ 2 ^ d →
    bsplitN f B d s n = ∑ t ∈ range n, f (s + t) * 2 ^ (B * t)
  | 0, s, n, hn => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hn) with rfl | rfl <;>
      simp [bsplitN_zero]
  | d + 1, s, n, hn => by
    rw [bsplitN_succ]
    split_ifs with h1 h0
    · subst h0; simp
    · have : n = 1 := by omega
      subst this; simp
    · rw [bsplitN_eq f B d s (n / 2) (by rw [pow_succ] at hn; omega),
        bsplitN_eq f B d _ (n - n / 2) (by rw [pow_succ] at hn; omega)]
      conv_rhs => rw [show n = n / 2 + (n - n / 2) by omega, sum_range_add]
      congr 1
      rw [Nat.shiftLeft_eq, sum_mul]
      refine sum_congr rfl fun t _ => ?_
      rw [add_assoc, mul_add B, pow_add]; ring

/-- No levels: at most one term. -/
theorem bsplit_zero' (f : ℕ → ℤ) (B s n : ℕ) :
    bsplit f B 0 s n = if n = 0 then 0 else f s := rfl

/-- One level of the divide and conquer. -/
theorem bsplit_succ (f : ℕ → ℤ) (B d s n : ℕ) :
    bsplit f B (d + 1) s n = if n ≤ 1 then (if n = 0 then 0 else f s) else
      bsplit f B d s (n / 2) + bsplit f B d (s + n / 2) (n - n / 2) *
        ((1 <<< (B * (n / 2)) : ℕ) : ℤ) := rfl

/-- **Sanity**: the empty sum. -/
theorem bsplit_zero (f : ℕ → ℤ) (B d s : ℕ) : bsplit f B d s 0 = 0 := by
  cases d <;> simp [bsplit_zero', bsplit_succ]

/-- `bsplit` computes the sum. -/
theorem bsplit_eq (f : ℕ → ℤ) (B : ℕ) : ∀ (d s n : ℕ), n ≤ 2 ^ d →
    bsplit f B d s n = ∑ t ∈ range n, f (s + t) * (2 : ℤ) ^ (B * t)
  | 0, s, n, hn => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hn) with rfl | rfl <;>
      simp [bsplit_zero']
  | d + 1, s, n, hn => by
    rw [bsplit_succ]
    split_ifs with h1 h0
    · subst h0; simp
    · have : n = 1 := by omega
      subst this; simp
    · rw [bsplit_eq f B d s (n / 2) (by rw [pow_succ] at hn; omega),
        bsplit_eq f B d _ (n - n / 2) (by rw [pow_succ] at hn; omega)]
      conv_rhs => rw [show n = n / 2 + (n - n / 2) by omega, sum_range_add]
      congr 1
      rw [sum_mul]
      refine sum_congr rfl fun t _ => ?_
      rw [Nat.shiftLeft_eq, one_mul, add_assoc, Nat.cast_pow, Nat.cast_ofNat, mul_add B, pow_add]
      ring

/-! ## One Chebyshev coefficient -/

/-- The stored half grid (right halves of the rows and the upper centre column). -/
def sliceH (N M : ℕ) (sd : SliceData) (i j : ℕ) : ℤ :=
  if N < i ∧ i ≤ N + sd.Nj ∧ M ≤ j + sd.Mj ∧ j ≤ M + sd.Mj then
    fieldW sd.Fj (sd.row (j + sd.Mj - M)) (i - N - 1)
  else if i = N ∧ M ≤ j ∧ j ≤ M + sd.Mj then fieldW sd.Fj sd.col (j - M) else 0

/-- The grid of a stored coefficient: the symmetric completion (sign `s`) times the symbol
`c₀ + a (i − N) + b (j − M)`. -/
def sliceG (N M : ℕ) (s c0 a b' : ℤ) (sd : SliceData) (i j : ℕ) : ℤ :=
  (c0 + a * ((i : ℤ) - N) + b' * ((j : ℤ) - M)) * symGrid N M s (sliceH N M sd) i j

section rowV

variable {N M : ℕ} {s c0 a b' : ℤ} {sd : SliceData}

/-- The band of stored rows. -/
def InBand (M Mj j : ℕ) : Prop := M ≤ j + Mj ∧ j ≤ M + Mj

/-- The grid of a stored coefficient, unfolded. -/
theorem sliceG_eq (i j : ℕ) : sliceG N M s c0 a b' sd i j =
    (c0 + a * ((i : ℤ) - N) + b' * ((j : ℤ) - M)) *
      (sliceH N M sd i j + s * sliceH N M sd (2 * N - i) (2 * M - j)) := rfl

/-- The stored half grid vanishes outside the band. -/
theorem sliceH_eq_zero_of_band {i j : ℕ} (h : ¬ InBand M sd.Mj j) : sliceH N M sd i j = 0 := by
  unfold InBand at h
  unfold sliceH
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The stored half grid vanishes left of the centre column. -/
theorem sliceH_eq_zero_of_lt {i j : ℕ} (h : i < N) : sliceH N M sd i j = 0 := by
  unfold sliceH
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The stored half grid vanishes beyond the stored columns. -/
theorem sliceH_eq_zero_of_gt {i j : ℕ} (h : N + sd.Nj < i) : sliceH N M sd i j = 0 := by
  unfold sliceH
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The stored half grid right of the centre column. -/
theorem sliceH_right {i j : ℕ} (h1 : N < i) (h2 : i ≤ N + sd.Nj) (hj : InBand M sd.Mj j) :
    sliceH N M sd i j = fieldW sd.Fj (sd.row (j + sd.Mj - M)) (i - N - 1) := by
  unfold InBand at hj
  unfold sliceH
  rw [ite_eq_left (by omega)]

/-- The stored half grid on the centre column. -/
theorem sliceH_centre {j : ℕ} (hj : InBand M sd.Mj j) :
    sliceH N M sd N j = if M ≤ j then fieldW sd.Fj sd.col (j - M) else 0 := by
  unfold InBand at hj
  unfold sliceH
  rw [ite_eq_right (by omega)]
  by_cases h : M ≤ j
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- **The image of a row.** -/
theorem rowV_eq (b dd : ℕ) (hN : sd.Nj ≤ N) (hdd : sd.Nj ≤ 2 ^ dd) {j : ℕ}
    (hj : j ≤ 2 * M) :
    rowV b N M s c0 a b' dd sd j =
      ∑ i ∈ range (2 * N + 1), sliceG N M s c0 a b' sd i j * (2 : ℤ) ^ (b * i) := by
  by_cases hb : InBand M sd.Mj j
  · have hb2 : InBand M sd.Mj (2 * M - j) := by unfold InBand at hb ⊢; omega
    rw [rowV, ite_eq_left (c := M ≤ j + sd.Mj ∧ j ≤ M + sd.Mj) hb, fieldZ_eq, fieldZ_eq,
      rpack_eq b sd.Fj dd _ _ _ _ hdd, rpackR_eq b sd.Fj dd _ _ _ _ hdd]
    have hsplit : 2 * N + 1 = (N - sd.Nj) + (sd.Nj + (1 + (sd.Nj + (N - sd.Nj)))) := by omega
    rw [hsplit, sum_range_add, sum_range_add, sum_range_add, sum_range_add, sum_range_one]
    -- the zero blocks
    have z1 : ∑ t ∈ range (N - sd.Nj), sliceG N M s c0 a b' sd t j * (2 : ℤ) ^ (b * t) = 0 := by
      refine sum_eq_zero fun t ht => ?_
      have ht' := mem_range.1 ht
      rw [sliceG_eq, sliceH_eq_zero_of_lt (by omega), sliceH_eq_zero_of_gt (by omega)]
      ring
    have z2 : ∑ t ∈ range (N - sd.Nj), sliceG N M s c0 a b' sd
        (N - sd.Nj + (sd.Nj + (1 + (sd.Nj + t)))) j *
          (2 : ℤ) ^ (b * (N - sd.Nj + (sd.Nj + (1 + (sd.Nj + t))))) = 0 := by
      refine sum_eq_zero fun t ht => ?_
      have ht' := mem_range.1 ht
      rw [sliceG_eq, sliceH_eq_zero_of_gt (by omega), sliceH_eq_zero_of_lt (by omega)]
      ring
    rw [z1, z2]
    -- the mirror block
    have hmir : ∑ t ∈ range sd.Nj, sliceG N M s c0 a b' sd (N - sd.Nj + t) j *
          (2 : ℤ) ^ (b * (N - sd.Nj + t)) =
        s * (∑ t ∈ range sd.Nj, (c0 - a * sd.Nj + b' * ((j : ℤ) - M) + a * t) *
          fieldW sd.Fj (sd.row (M + sd.Mj - j)) (sd.Nj - 1 - t) * (2 : ℤ) ^ (b * t)) *
          ((1 <<< (b * (N - sd.Nj)) : ℕ) : ℤ) := by
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun t ht => ?_
      have ht' := mem_range.1 ht
      rw [sliceG_eq, sliceH_eq_zero_of_lt (by omega), sliceH_right (by omega) (by omega) hb2,
        show 2 * M - j + sd.Mj - M = M + sd.Mj - j by omega,
        show 2 * N - (N - sd.Nj + t) - N - 1 = sd.Nj - 1 - t by omega,
        Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat, mul_add b, pow_add]
      push_cast [Nat.cast_sub hN]
      ring
    -- the right block
    have hright : ∑ t ∈ range sd.Nj, sliceG N M s c0 a b' sd
          (N - sd.Nj + (sd.Nj + (1 + t))) j *
          (2 : ℤ) ^ (b * (N - sd.Nj + (sd.Nj + (1 + t)))) =
        (∑ t ∈ range sd.Nj, (c0 + a + b' * ((j : ℤ) - M) + a * t) *
          fieldW sd.Fj (sd.row (j + sd.Mj - M)) t * (2 : ℤ) ^ (b * t)) *
          ((1 <<< (b * (N + 1)) : ℕ) : ℤ) := by
      rw [sum_mul]
      refine sum_congr rfl fun t ht => ?_
      have ht' := mem_range.1 ht
      rw [sliceG_eq, sliceH_right (by omega) (by omega) hb, sliceH_eq_zero_of_lt (by omega),
        show N - sd.Nj + (sd.Nj + (1 + t)) - N - 1 = t by omega,
        show N - sd.Nj + (sd.Nj + (1 + t)) = N + 1 + t by omega,
        Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat, mul_add b (N + 1), pow_add]
      push_cast
      ring
    -- the centre
    have hcen : sliceG N M s c0 a b' sd (N - sd.Nj + (sd.Nj + 0)) j *
          (2 : ℤ) ^ (b * (N - sd.Nj + (sd.Nj + 0))) =
        (c0 + b' * ((j : ℤ) - M)) * ((if M ≤ j then fieldW sd.Fj sd.col (j - M) else 0) +
          s * (if j ≤ M then fieldW sd.Fj sd.col (M - j) else 0)) *
          ((1 <<< (b * N) : ℕ) : ℤ) := by
      rw [show N - sd.Nj + (sd.Nj + 0) = N by omega, sliceG_eq, sliceH_centre hb,
        show 2 * N - N = N by omega, sliceH_centre hb2, Nat.shiftLeft_eq, one_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      have e1 : (M ≤ 2 * M - j) ↔ j ≤ M := by omega
      by_cases h1 : M ≤ j <;> by_cases h2 : j ≤ M <;>
        simp only [h1, h2, e1, ↓reduceIte, show 2 * M - j - M = M - j by omega] <;> ring
    rw [hmir, hright, hcen]
    ring
  · rw [rowV, ite_eq_right (c := M ≤ j + sd.Mj ∧ j ≤ M + sd.Mj) hb]
    symm
    refine sum_eq_zero fun i _ => ?_
    have hb2 : ¬ InBand M sd.Mj (2 * M - j) := by unfold InBand at hb ⊢; omega
    rw [sliceG_eq, sliceH_eq_zero_of_band hb, sliceH_eq_zero_of_band hb2]
    ring

end rowV

/-! ## The image of a coefficient and of a family -/

/-- The stored coefficient fits its parameters. -/
def SliceOK (N M dd dr : ℕ) (sd : SliceData) : Prop :=
  sd.Nj ≤ N ∧ sd.Mj ≤ M ∧ sd.Nj ≤ 2 ^ dd ∧ 2 * sd.Mj + 1 ≤ 2 ^ dr ∧ 1 ≤ sd.Fj

/-- The fit of a stored coefficient is decidable. -/
instance (N M dd dr : ℕ) (sd : SliceData) : Decidable (SliceOK N M dd dr sd) := by
  unfold SliceOK; infer_instance

/-- **`slicePack` is the Kronecker image of the coefficient.** -/
theorem slicePack_eq (b W N M : ℕ) (s c0 a b' : ℤ) {dd dr : ℕ} {sd : SliceData}
    (h : SliceOK N M dd dr sd) :
    slicePack b W N M s c0 a b' dd dr sd = kron b W (gridPolyNM N M (sliceG N M s c0 a b' sd)) := by
  obtain ⟨hN, hM, hdd, hdr, -⟩ := h
  rw [kron_gridPolyNM, packGridNM_eq, slicePack, bsplit_eq _ _ dr 0 _ hdr]
  have hrow : ∀ j, j < 2 * M + 1 → ∑ i ∈ range (2 * N + 1),
      sliceG N M s c0 a b' sd i j * (2 : ℤ) ^ (b * (i + W * j)) =
      rowV b N M s c0 a b' dd sd j * (2 : ℤ) ^ (b * W * j) := fun j hj => by
    rw [rowV_eq b dd hN hdd (by omega), sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_add b, pow_add, mul_assoc b]; ring
  rw [sum_congr rfl fun j hj => hrow j (mem_range.1 hj)]
  have hz : ∀ j, ¬ InBand M sd.Mj j → rowV b N M s c0 a b' dd sd j = 0 := fun j hj => by
    rw [rowV, ite_eq_right (c := M ≤ j + sd.Mj ∧ j ≤ M + sd.Mj) hj]
  have hband : ∑ j ∈ range (2 * M + 1), rowV b N M s c0 a b' dd sd j * (2 : ℤ) ^ (b * W * j) =
      ∑ r ∈ range (2 * sd.Mj + 1), rowV b N M s c0 a b' dd sd (M - sd.Mj + r) *
        (2 : ℤ) ^ (b * W * (M - sd.Mj + r)) := by
    have hsplit : 2 * M + 1 = (M - sd.Mj) + ((2 * sd.Mj + 1) + (M - sd.Mj)) := by omega
    rw [hsplit, sum_range_add, sum_range_add]
    rw [sum_eq_zero (s := range (M - sd.Mj)) fun j hj => by
      rw [hz j (by unfold InBand; simp at hj; omega), zero_mul]]
    rw [sum_eq_zero (s := range (M - sd.Mj)) fun j hj => by
      rw [hz _ (by unfold InBand; simp at hj; omega), zero_mul]]
    simp
  rw [hband, sum_mul, Nat.shiftLeft_eq, one_mul]
  refine sum_congr rfl fun r _ => ?_
  rw [zero_add, Nat.cast_pow, Nat.cast_ofNat, mul_add (b * W), pow_add]; ring

/-- The `w`-symmetric family polynomial `∑_k (w^{D + k} + w^{D − k}) g_k` (the `k = 0` term
once), coefficients from position `k` of the list on. -/
def famPoly (N M D : ℕ) (s c0 a b' : ℤ) : ℕ → List SliceData → P3
  | _, [] => 0
  | k, sd :: rest => ((X : P3) ^ (D + k) + (if k = 0 then 0 else X ^ (D - k))) *
      Polynomial.C (gridPolyNM N M (sliceG N M s c0 a b' sd)) + famPoly N M D s c0 a b' (k + 1) rest

/-- `kron (flat wⁿ) = 2^{b W R n}`. -/
theorem kron_flat_X_pow (b W R n : ℕ) :
    kron b W (flat R ((X : P3) ^ n)) = (((1 <<< (b * W * R * n)) : ℕ) : ℤ) := by
  have h1 : flat R ((X : P3) ^ n) = monomial (R * n) (monomial 0 1) := by
    simp [flat, pow_mul, ← C_mul_X_pow_eq_monomial]
  rw [h1, kron_monomial]
  simp only [Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat, zero_add]
  ring_nf

/-- **`famPack` is the Kronecker image of the flattened family.** -/
theorem famPack_eq (b W R N M D : ℕ) (s c0 a b' : ℤ) {dd dr : ℕ} :
    ∀ (k : ℕ) (l : List SliceData), (∀ sd ∈ l, SliceOK N M dd dr sd) →
      famPack b W R N M D s c0 a b' dd dr k l = kron b W (flat R (famPoly N M D s c0 a b' k l))
  | _, [], _ => by simp [famPack, famPoly]
  | k, sd :: rest, h => by
    rw [famPack, famPoly, famPack_eq b W R N M D s c0 a b' (k + 1) rest
      fun sd' h' => h sd' (List.mem_cons_of_mem _ h'), map_add, map_add, map_mul, map_mul,
      flat_C, slicePack_eq b W N M s c0 a b' (h sd List.mem_cons_self), map_add, map_add,
      kron_flat_X_pow]
    split_ifs
    · simp; ring
    · rw [kron_flat_X_pow]; ring

/-! ## The image of a coefficient with natural numbers only -/

/-- The offset image of one row of a stored coefficient (offsets `2^{b−1}` on the `2N_j + 1` data
columns), natural numbers only. -/
def rowN (b N M c0 : ℕ) (odd : Bool) (dd : ℕ) (sd : SliceData) (j : ℕ) : ℕ :=
  (rpN b sd.Fj c0 (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) false dd sd.Nj
      (sd.row (j + sd.Mj - M)) <<< (b * (N + 1))) +
    (rpNR b sd.Fj c0 (if odd then 2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)
      else 2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) odd dd sd.Nj
      (sd.row (M + sd.Mj - j)) <<< (b * (N - sd.Nj))) +
    (centreN b M c0 odd sd j <<< (b * N))

/-- **The Kronecker image of a stored coefficient, natural numbers only**: the offset images of
the band rows (divide and conquer) minus the offsets. -/
def slicePackN (b W N M c0 : ℕ) (odd : Bool) (dd dr : ℕ) (sd : SliceData) : ℤ :=
  (((bsplitN (fun r => rowN b N M c0 odd dd sd (M - sd.Mj + r)) (b * W) dr 0 (2 * sd.Mj + 1)) <<<
    (b * W * (M - sd.Mj)) : ℕ) : ℤ) -
    (((rowO b N sd * onesK (b * W) (2 * sd.Mj + 1)) <<< (b * W * (M - sd.Mj)) : ℕ) : ℤ)

section natPack

variable {b F c0 d n x : ℕ}

/-- Raw fields are below `2^F`. -/
theorem rawF_lt (F x t : ℕ) : rawF F x t < 2 ^ F := Nat.mod_lt _ (by positivity)

/-- `2^F = 2 · 2^{F−1}` for `F ≥ 1`. -/
theorem two_pow_F (hF : 1 ≤ F) : (2 : ℕ) ^ F = 2 * 2 ^ (F - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- The right half: `rpN` is `rpack` plus offsets. -/
theorem rpN_cast (hn : n ≤ 2 ^ d) (hH : c0 * 2 ^ (F - 1) ≤ 2 ^ (b - 1)) :
    ((rpN b F c0 (2 ^ (b - 1) - c0 * 2 ^ (F - 1)) false d n x : ℕ) : ℤ) =
      rpack b F c0 0 d n x + 2 ^ (b - 1) * ∑ t ∈ range n, (2 : ℤ) ^ (b * t) := by
  rw [rpN_eq _ _ _ _ _ d n x hn, rpack_eq b F d _ _ n x hn, mul_sum, ← sum_add_distrib]
  push_cast
  refine sum_congr rfl fun t _ => ?_
  rw [digN, ite_eq_right (by simp), fieldW_eq_rawF]
  push_cast [hH]
  ring

/-- The mirror half: `rpNR` is `± rpackR` plus offsets. -/
theorem rpNR_cast (hn : n ≤ 2 ^ d) (hF : 1 ≤ F) (hH : c0 * 2 ^ (F - 1) ≤ 2 ^ (b - 1))
    (odd : Bool) :
    ((rpNR b F c0 (if odd then 2 ^ (b - 1) + c0 * 2 ^ (F - 1) else 2 ^ (b - 1) - c0 * 2 ^ (F - 1))
      odd d n x : ℕ) : ℤ) =
      (if odd then -1 else 1) * rpackR b F c0 0 d n x +
        2 ^ (b - 1) * ∑ t ∈ range n, (2 : ℤ) ^ (b * t) := by
  rw [rpNR_eq _ _ _ _ _ d n x hn, rpackR_eq b F d _ _ n x hn, mul_sum, mul_sum, ← sum_add_distrib]
  push_cast
  refine sum_congr rfl fun t _ => ?_
  have hr := rawF_lt F x (n - 1 - t)
  rw [two_pow_F hF] at hr
  cases odd
  · simp only [digN, Bool.false_eq_true, ↓reduceIte, fieldW_eq_rawF]
    push_cast [hH]
    ring
  · simp only [digN, ↓reduceIte, fieldW_eq_rawF]
    have h3 : c0 * rawF F x (n - 1 - t) ≤ 2 ^ (b - 1) + c0 * 2 ^ (F - 1) := by
      calc c0 * rawF F x (n - 1 - t) ≤ c0 * (2 * 2 ^ (F - 1)) := Nat.mul_le_mul_left _ hr.le
        _ = c0 * 2 ^ (F - 1) + c0 * 2 ^ (F - 1) := by ring
        _ ≤ _ := by omega
    push_cast [h3]
    ring

/-- The centre column digit is the centre of `rowV` plus the offset. -/
theorem centreN_cast {M c0 : ℕ} {sd : SliceData} (hF : 1 ≤ sd.Fj)
    (hH : 2 * c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) (odd : Bool) (j : ℕ) :
    ((centreN b M c0 odd sd j : ℕ) : ℤ) =
      ((c0 : ℤ) + 0 * ((j : ℤ) - M)) * ((if M ≤ j then fieldZ sd.Fj sd.col (j - M) else 0) +
        (if odd then -1 else 1) * (if j ≤ M then fieldZ sd.Fj sd.col (M - j) else 0)) +
        2 ^ (b - 1) := by
  have hr : ∀ t, rawF sd.Fj sd.col t < 2 * 2 ^ (sd.Fj - 1) := fun t => by
    have := rawF_lt sd.Fj sd.col t; rwa [two_pow_F hF] at this
  have hH1 : c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1) := by
    have : 2 * c0 * 2 ^ (sd.Fj - 1) = 2 * (c0 * 2 ^ (sd.Fj - 1)) := by ring
    omega
  simp only [fieldZ_eq, fieldW_eq_rawF, centreN]
  rcases lt_trichotomy j M with h | h | h
  · simp only [show ¬ M < j by omega, h, ↓reduceIte, show ¬ M ≤ j by omega, show j ≤ M by omega]
    cases odd
    · simp only [Bool.false_eq_true, ↓reduceIte]; push_cast [hH1]; ring
    · simp only [↓reduceIte]
      have h3 : c0 * rawF sd.Fj sd.col (M - j) ≤ 2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1) := by
        have := hr (M - j); nlinarith
      push_cast [h3]; ring
  · subst h
    simp only [lt_irrefl, ↓reduceIte, le_refl, Nat.sub_self]
    cases odd
    · simp only [Bool.false_eq_true, ↓reduceIte]; push_cast [hH]; ring
    · simp only [↓reduceIte]; push_cast; ring
  · simp only [h, ↓reduceIte, show M ≤ j by omega, show ¬ j ≤ M by omega]
    push_cast [hH1]; ring

/-- The offsets of a row, block by block. -/
theorem rowO_cast {N : ℕ} {sd : SliceData} (hb : 1 ≤ b) (hN : sd.Nj ≤ N) :
    ((rowO b N sd : ℕ) : ℤ) =
      2 ^ (b - 1) * (∑ t ∈ range sd.Nj, (2 : ℤ) ^ (b * t)) * ((1 <<< (b * (N + 1)) : ℕ) : ℤ) +
      2 ^ (b - 1) * (∑ t ∈ range sd.Nj, (2 : ℤ) ^ (b * t)) * ((1 <<< (b * (N - sd.Nj)) : ℕ) : ℤ) +
      2 ^ (b - 1) * ((1 <<< (b * N) : ℕ) : ℤ) := by
  rw [rowO, onesK_eq b _ hb, dexp, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]
  push_cast
  simp only [one_mul]
  have hs : ∑ t ∈ range (2 * sd.Nj + 1), (2 : ℤ) ^ (b * t) =
      ∑ t ∈ range sd.Nj, (2 : ℤ) ^ (b * t) + 2 ^ (b * sd.Nj) +
        2 ^ (b * (sd.Nj + 1)) * ∑ t ∈ range sd.Nj, (2 : ℤ) ^ (b * t) := by
    rw [show 2 * sd.Nj + 1 = (sd.Nj + 1) + sd.Nj by ring, sum_range_add, sum_range_succ, mul_sum]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [← pow_add, mul_add]
  rw [hs]
  have e1 : (2 : ℤ) ^ (b * sd.Nj) * 2 ^ (b * (N - sd.Nj)) = 2 ^ (b * N) := by
    rw [← pow_add, ← mul_add]; congr 2; omega
  have e2 : (2 : ℤ) ^ (b * (sd.Nj + 1)) * 2 ^ (b * (N - sd.Nj)) = 2 ^ (b * (N + 1)) := by
    rw [← pow_add, ← mul_add]; congr 2; omega
  linear_combination (2 ^ (b - 1) : ℤ) * e1 +
    (2 ^ (b - 1) * ∑ t ∈ range sd.Nj, (2 : ℤ) ^ (b * t)) * e2

/-- **The offset image of a band row is the row image plus offsets.** -/
theorem rowN_eq_rowV {N M dd : ℕ} {sd : SliceData} (hb : 1 ≤ b) (hN : sd.Nj ≤ N)
    (hdd : sd.Nj ≤ 2 ^ dd) (hF : 1 ≤ sd.Fj) (hH : 2 * c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1))
    (odd : Bool) {j : ℕ} (hj : InBand M sd.Mj j) :
    ((rowN b N M c0 odd dd sd j : ℕ) : ℤ) - rowO b N sd =
      rowV b N M (if odd then -1 else 1) c0 0 0 dd sd j := by
  have hH1 : c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1) := by
    have : 2 * c0 * 2 ^ (sd.Fj - 1) = 2 * (c0 * 2 ^ (sd.Fj - 1)) := by ring
    omega
  rw [rowV, ite_eq_left (c := M ≤ j + sd.Mj ∧ j ≤ M + sd.Mj) hj, rowO_cast hb hN, rowN]
  simp only [Nat.shiftLeft_eq, one_mul]
  push_cast
  rw [rpN_cast hdd hH1, rpNR_cast hdd hF hH1 odd, centreN_cast hF hH odd j]
  simp only [add_zero, zero_mul, sub_zero]
  ring

/-- **The natural-number image of a coefficient equals `slicePack`.** -/
theorem slicePackN_eq {W N M dd dr : ℕ} {sd : SliceData} (hb : 1 ≤ b) (hW : 1 ≤ W)
    (h : SliceOK N M dd dr sd) (hH : 2 * c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) (odd : Bool) :
    slicePackN b W N M c0 odd dd dr sd =
      slicePack b W N M (if odd then -1 else 1) c0 0 0 dd dr sd := by
  obtain ⟨hN, hM, hdd, hdr, hF⟩ := h
  rw [slicePackN, slicePack, bsplitN_eq _ _ dr 0 _ hdr, bsplit_eq _ _ dr 0 _ hdr,
    onesK_eq _ _ (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))), dexp]
  simp only [Nat.shiftLeft_eq, one_mul]
  push_cast
  rw [mul_sum, sum_mul, sum_mul, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun r hr => ?_
  rw [zero_add, ← rowN_eq_rowV hb hN hdd hF hH odd (by unfold InBand; simp at hr; omega)]
  ring

end natPack

/-! ## Facts about family polynomials -/


/-- The degree box of a family polynomial. -/
theorem inBox3_famPoly (N M D : ℕ) (s c0 a b' : ℤ) :
    ∀ (k : ℕ) (l : List SliceData), k + l.length ≤ D + 1 →
      InBox3 (famPoly N M D s c0 a b' k l) (2 * N) (2 * M) (2 * D)
  | _, [], _ => ⟨by simp [famPoly], fun j => by
    simp only [famPoly, Polynomial.coeff_zero]; exact ⟨by simp, fun _ => by simp⟩⟩
  | k, sd :: rest, h => by
    simp only [List.length_cons] at h
    rw [famPoly]
    refine InBox3.add ?_ (inBox3_famPoly N M D s c0 a b' (k + 1) rest (by omega))
    have h1 : InBox3 ((X : P3) ^ (D + k) + (if k = 0 then 0 else X ^ (D - k))) 0 0 (D + k) := by
      refine (InBox3.X_pow (D + k)).add ?_
      split_ifs
      · exact ⟨by simp, fun j => by
          simp only [Polynomial.coeff_zero]; exact ⟨by simp, fun _ => by simp⟩⟩
      · exact (InBox3.X_pow (D - k)).mono le_rfl le_rfl (by omega)
    have h2 := h1.mul (InBox3.C (box_gridPolyNM N M (sliceG N M s c0 a b' sd)))
    simp only [zero_add, add_zero] at h2
    exact h2.mono le_rfl le_rfl (by omega)

/-- The static `ℓ¹` bound of a stored coefficient. -/
def sliceL1 (N M : ℕ) (c0 a b' : ℤ) (sd : SliceData) : ℕ :=
  (2 * N + 1) * (2 * M + 1) * ((c0.natAbs + a.natAbs * N + b'.natAbs * M) * 2 ^ sd.Fj)

/-- The static `ℓ¹` bound of a family. -/
def famL1 (N M : ℕ) (c0 a b' : ℤ) : ℕ → List SliceData → ℕ
  | _, [] => 0
  | k, sd :: rest =>
    (if k = 0 then 1 else 2) * sliceL1 N M c0 a b' sd + famL1 N M c0 a b' (k + 1) rest

/-- The entries of a stored coefficient are bounded. -/
theorem abs_sliceG_le (N M : ℕ) {s : ℤ} (hs : |s| = 1) (c0 a b' : ℤ) (sd : SliceData)
    (hF : 1 ≤ sd.Fj) {i j : ℕ} (hi : i ≤ 2 * N) (hj : j ≤ 2 * M) :
    |sliceG N M s c0 a b' sd i j| ≤
      (((c0.natAbs + a.natAbs * N + b'.natAbs * M) * 2 ^ sd.Fj : ℕ) : ℤ) := by
  have hh : ∀ i j, |sliceH N M sd i j| ≤ 2 ^ (sd.Fj - 1) := fun i j => by
    unfold sliceH
    split_ifs
    · exact abs_fieldW_le _ _ _ hF
    · exact abs_fieldW_le _ _ _ hF
    · simp
  have h1 := abs_symGrid_le N M hs hh i j
  have h2 : |c0 + a * ((i : ℤ) - N) + b' * ((j : ℤ) - M)| ≤ |c0| + |a| * N + |b'| * M := by
    have e1 : |((i : ℤ) - N)| ≤ N := by rw [abs_le]; constructor <;> omega
    have e2 : |((j : ℤ) - M)| ≤ M := by rw [abs_le]; constructor <;> omega
    calc |c0 + a * ((i : ℤ) - N) + b' * ((j : ℤ) - M)|
        ≤ |c0| + |a| * |((i : ℤ) - N)| + |b'| * |((j : ℤ) - M)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]
          gcongr
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]
      _ ≤ |c0| + |a| * N + |b'| * M := by gcongr
  unfold sliceG
  rw [abs_mul]
  have e3 : (2 : ℤ) * 2 ^ (sd.Fj - 1) = 2 ^ sd.Fj := by rw [← pow_succ']; congr 1; omega
  push_cast
  rw [← e3]
  exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)

/-- **Static `ℓ¹` bound of a flattened family.** -/
theorem l1_flat_famPoly_le (R N M D : ℕ) {s : ℤ} (hs : |s| = 1) (c0 a b' : ℤ) :
    ∀ (k : ℕ) (l : List SliceData), (∀ sd ∈ l, 1 ≤ sd.Fj) →
      l1 (flat R (famPoly N M D s c0 a b' k l)) ≤ famL1 N M c0 a b' k l
  | _, [], _ => by simp [famPoly, famL1, l1, liftN]
  | k, sd :: rest, h => by
    rw [famPoly, famL1, map_add]
    refine (l1_add_le _ _).trans (add_le_add ?_
      (l1_flat_famPoly_le R N M D hs c0 a b' (k + 1) rest
        fun sd' h' => h sd' (List.mem_cons_of_mem _ h')))
    rw [map_mul, flat_C]
    refine (l1_mul_le _ _).trans ?_
    have hg : l1 (gridPolyNM N M (sliceG N M s c0 a b' sd)) ≤ sliceL1 N M c0 a b' sd :=
      l1_gridPolyNM_le_const N M fun i j hi hj =>
        abs_sliceG_le N M hs c0 a b' sd (h sd List.mem_cons_self) hi hj
    have hX : ∀ n, l1 (flat R ((X : P3) ^ n)) = 1 := fun n => by
      have h1 : flat R ((X : P3) ^ n) = monomial (R * n) (monomial 0 1) := by
        simp [flat, pow_mul, ← C_mul_X_pow_eq_monomial]
      rw [h1, l1_monomial]; rfl
    have hm : l1 (flat R ((X : P3) ^ (D + k) + (if k = 0 then 0 else X ^ (D - k)))) ≤
        (if k = 0 then 1 else 2) := by
      split_ifs
      · rw [add_zero, hX]
      · rw [map_add]; refine (l1_add_le _ _).trans ?_; rw [hX, hX]
    exact Nat.mul_le_mul hm hg

/-! ## The centre of a family -/

/-- The value at `w = c` of a family centre (weight `(1, 0, p)`):
`∑_k (c^k + c^{−k}) ctr g_k` (the `k = 0` term once). -/
def famCtr (S N M p : ℕ) (s c0 a b' : ℤ) (c : ℂ) : ℕ → List SliceData → FA
  | _, [] => 0
  | k, sd :: rest => algebraMap ℂ FA (c ^ k + if k = 0 then 0 else (c ^ k)⁻¹) *
      ctr S N M (1, 0, p) (gridPolyNM N M (sliceG N M s c0 a b' sd)) +
      famCtr S N M p s c0 a b' c (k + 1) rest

/-- `ctr3` is additive. -/
theorem ctr3_add (S N M D : ℕ) (c : ℂ) (w : ℕ × ℕ × ℕ) (P Q : P3) :
    ctr3 S N M D c w (P + Q) = ctr3 S N M D c w P + ctr3 S N M D c w Q := by
  simp only [ctr3, map_add, add_mul, smul_add, mul_add]

/-- `ctr3` of `wⁿ g`. -/
theorem ctr3_X_pow_C (S N M D : ℕ) (c : ℂ) (w : ℕ × ℕ × ℕ) (n : ℕ) (P : P2) :
    ctr3 S N M D c w ((X : P3) ^ n * Polynomial.C P) =
      algebraMap ℂ FA (c ^ n * (c ^ (D * w.1))⁻¹) * ctr S N M w P := by
  simp only [ctr3, ctr, map_mul, map_pow, phiW_X, phiW_C, mul_smul_comm]
  ring_nf

/-- **The centre of a family polynomial** is `famCtr`. -/
theorem ctr3_famPoly (S N M D p : ℕ) (s c0 a b' : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ∀ (k : ℕ) (l : List SliceData), k + l.length ≤ D + 1 →
      ctr3 S N M D c (1, 0, p) (famPoly N M D s c0 a b' k l) = famCtr S N M p s c0 a b' c k l
  | _, [], _ => by simp [famPoly, famCtr, ctr3]
  | k, sd :: rest, h => by
    simp only [List.length_cons] at h
    rw [famPoly, famCtr, ctr3_add, add_mul, ctr3_add,
      ctr3_famPoly S N M D p s c0 a b' hc (k + 1) rest (by omega)]
    congr 1
    split_ifs with hk
    · subst hk
      rw [ctr3_X_pow_C, add_zero, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hc)]
      simp [ctr3]
    · rw [ctr3_X_pow_C, ctr3_X_pow_C, ← add_mul, ← map_add, mul_one]
      congr 2
      have e1 : c ^ (D + k) * (c ^ D)⁻¹ = c ^ k := by
        rw [pow_add]; field_simp
      have e2 : c ^ (D - k) * (c ^ D)⁻¹ = (c ^ k)⁻¹ := by
        have : c ^ D = c ^ (D - k) * c ^ k := by rw [← pow_add]; congr 1; omega
        rw [this]; field_simp
      rw [e1, e2]

/-- **Families of real coefficients are real** at real parameter values (`|c| = 1`). -/
theorem isReal_famCtr (S N M p : ℕ) (c0 : ℤ) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ (k : ℕ) (l : List SliceData),
      IsReal (famCtr S N M p ((-1) ^ p) c0 0 0 c k l)
  | _, [] => by simpa [famCtr] using IsReal.algebraMap 0
  | k, sd :: rest => by
    rw [famCtr]
    refine IsReal.add (IsReal.mul ?_ ?_) (isReal_famCtr S N M p c0 hc (k + 1) rest)
    · have hck : ‖c ^ k‖ = 1 := by rw [norm_pow, hc, one_pow]
      have hinv : (c ^ k)⁻¹ = (starRingEnd ℂ) (c ^ k) := by
        rw [Complex.inv_def, ← Complex.sq_norm, hck]; simp
      split_ifs
      · simp only [add_zero]
        subst_vars
        simpa using IsReal.algebraMap 1
      · rw [hinv, Complex.add_conj]
        exact IsReal.algebraMap _
    · have : sliceG N M ((-1) ^ p) c0 0 0 sd = symGrid N M ((-1) ^ p)
          (fun i j => c0 * sliceH N M sd i j) := by
        funext i j; simp only [sliceG, symGrid]; ring
      rw [this]
      exact isReal_ctr_sym S N M p _

/-- Family centres are analytic. -/
theorem ana_famCtr (S N M p : ℕ) (s c0 a b' : ℤ) (c : ℂ) :
    ∀ (k : ℕ) (l : List SliceData), Ana (famCtr S N M p s c0 a b' c k l)
  | _, [] => by simpa [famCtr] using Ana.zero
  | k, sd :: rest => by
    rw [famCtr]
    exact ((Ana.algebraMap _).mul (ana_ctr_grid S N M _ _)).add (ana_famCtr S N M p s c0 a b' c _ _)

/-- **Derivatives of family centres**: `dS α β` with integer symbols multiplies every coefficient
grid by the symbol and lowers the phase by one. -/
theorem dS_famCtr (S N M p : ℕ) (s c0 : ℤ) (α β : ℤ) (c : ℂ) :
    ∀ (k : ℕ) (l : List SliceData),
      dS α β (famCtr S N M p s c0 0 0 c k l) =
        famCtr S N M ((p + 3) % 4) s 0 (c0 * α) (c0 * β) c k l
  | _, [] => by simpa [famCtr] using dS_algebraMap (α : ℂ) β 0
  | k, sd :: rest => by
    rw [famCtr, famCtr, dS_add _ _ ((Ana.algebraMap _).mul (ana_ctr_grid S N M _ _))
      (ana_famCtr S N M p s c0 0 0 c _ _), dS_famCtr S N M p s c0 α β c (k + 1) rest,
      ← Algebra.smul_def, dS_smul _ _ _ (ana_ctr_grid S N M _ _), Algebra.smul_def, dS_ctr_grid]
    congr 3
    refine congrArg _ (funext fun i => funext fun j => ?_)
    simp only [sliceG]
    ring

end PlasmaLean.Certificates.KronBallCheb
