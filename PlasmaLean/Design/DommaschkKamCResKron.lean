/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCKronW
public import PlasmaLean.Design.DommaschkKamIdentCheck

/-!
# Fast Kronecker images of salted packed rows (residual chain of torus C, N-33 plan item 7)

Infrastructure of the high-resolution residual chain of Dommaschk torus C
(`Design/DommaschkKamCRes*`). The centres of that chain are `193 × 161` grids; building their
Kronecker images entry by entry (`packGridNM` of `Certificates/KronBallGrid`) costs the kernel about
`1` ms per entry, and the kernel's caches degrade when many big literals share their low `64` bits
(`Nat` literals hash by their low word: grids whose corner coefficients vanish produce many such
literals). Here a grid is stored as **salted packed rows**:

* a row `r = (lo, cnt, F, x)` (`RowR`) holds the entries `i = lo, …, lo + cnt − 1` of one row `j`
  (fixed `ψ`-mode) as `cnt` fields of width `F` with offset `2^{F−1}` (`fldZ`), shifted above a
  random `64`-bit salt (`x = fields · 2^64 + salt`): distinct rows have distinct low words;
* the image of a row at slot width `b` is the divide-and-conquer **spread** `sprK` of the fields
  (shifts and masks only, `O(cnt log cnt)` bit operations, no per-entry list walk), minus the
  offset `rowOffs` (`rowImgR`); the image of the grid is the divide-and-conquer sum `dcZ` of the
  row images at stride `b W` (`imgR`).

**Main results.** `sprK_spec` (the spread places the fields), `rowImgR_spec`, `dcZ_spec`,
`kron_gridR` (the Kronecker image of `gridPolyNM N M (gridR rows)` is `imgR b W rows (2M + 1)`,
for rows inside the box), `l1_gridR_le` (the static `ℓ¹` bound `rowsL1`), the equality checks
`chkGrid`/`chkGrid_sound` (grids agree on blocks of rows), `Bd_ctr_of_node` (the norm of a node
centre from the tree majorants), and the `R`-form substitution `ev_substR_H` in the strip algebra.

**Sanity.** `sprK_fixture`, `gridR_nil` (degenerate: no rows, zero grid), `imgR_fixture` (an
accepted two-row image), `fldZ_reject` (rejected fixture: the field without the salt shift is a
different number, so the salt must be stripped).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open Polynomial Finset PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton
  PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall
  PlasmaLean.Design.DommaschkKam WEll1Z2 Complex

/-! ## Fields and the spread -/

/-- Field `k` (width `F`) of the natural number `y`. -/
def fldN (F y k : ℕ) : ℕ := (y >>> (F * k)) % 2 ^ F

/-- Field `k` of a masked number is the field of the number. -/
theorem fldN_mod (F y h k : ℕ) (hk : k < h) : fldN F (y % 2 ^ (F * h)) k = fldN F y k := by
  simp only [fldN, Nat.shiftRight_eq_div_pow]
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self y, ← pow_add,
    Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 (by nlinarith)

/-- Field `k` of a shifted number is a later field. -/
theorem fldN_div (F y h k : ℕ) : fldN F (y / 2 ^ (F * h)) k = fldN F y (h + k) := by
  simp only [fldN, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add, mul_add]

/-- **The spread**: the first `c` fields (width `F`) of `y` placed in slots of width `b`, by divide
and conquer over `d` levels (`c ≤ 2^d`). -/
def sprK (F b d : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ y => y)
    (fun d ih c y => cond (Nat.ble c (1 <<< d)) (ih c y)
      (ih (1 <<< d) (y % (1 <<< (F <<< d))) + (ih (c - (1 <<< d)) (y >>> (F <<< d)) <<< (b <<< d))))
    d

/-- One level of the spread. -/
theorem sprK_succ (F b d c y : ℕ) : sprK F b (d + 1) c y = cond (Nat.ble c (2 ^ d)) (sprK F b d c y)
    (sprK F b d (2 ^ d) (y % 2 ^ (F * 2 ^ d)) +
      sprK F b d (c - 2 ^ d) (y / 2 ^ (F * 2 ^ d)) * 2 ^ (b * 2 ^ d)) := by
  change cond (Nat.ble c (1 <<< d)) (sprK F b d c y) (sprK F b d (1 <<< d) (y % (1 <<< (F <<< d)))
    + (sprK F b d (c - (1 <<< d)) (y >>> (F <<< d)) <<< (b <<< d))) = _
  simp only [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow]

/-- **Specification of the spread**: for `c ≤ 2^d` and `y < 2^{F c}`,
`sprK F b d c y = ∑_{k < c} fldN F y k · 2^{b k}`. -/
theorem sprK_spec (F b : ℕ) : ∀ (d c y : ℕ), c ≤ 2 ^ d → y < 2 ^ (F * c) →
    sprK F b d c y = ∑ k ∈ range c, fldN F y k * 2 ^ (b * k)
  | 0, c, y, hc, hy => by
    change y = _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hc) with rfl | rfl
    · simp at hy; simp [hy]
    · simp only [mul_one] at hy
      simp [fldN, Nat.mod_eq_of_lt hy]
  | d + 1, c, y, hc, hy => by
    rw [sprK_succ]
    rcases Nat.lt_or_ge (2 ^ d) c with hlt | hle
    · have hb : Nat.ble c (2 ^ d) = false :=
        Bool.eq_false_iff.2 fun h => by have := Nat.le_of_ble_eq_true h; omega
      rw [hb, Bool.cond_false]
      have hc2 : c - 2 ^ d ≤ 2 ^ d := by rw [pow_succ] at hc; omega
      have h1 := sprK_spec F b d (2 ^ d) (y % 2 ^ (F * 2 ^ d)) le_rfl
        (Nat.mod_lt _ (by positivity))
      have hy2 : y / 2 ^ (F * 2 ^ d) < 2 ^ (F * (c - 2 ^ d)) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← mul_add,
          Nat.sub_add_cancel hlt.le]
        exact hy
      have h2 := sprK_spec F b d (c - 2 ^ d) (y / 2 ^ (F * 2 ^ d)) hc2 hy2
      rw [h1, h2]
      have hsplit : c = 2 ^ d + (c - 2 ^ d) := by omega
      conv_rhs => rw [hsplit, sum_range_add]
      congr 1
      · exact sum_congr rfl fun k hk => by rw [fldN_mod F y _ k (mem_range.1 hk)]
      · rw [sum_mul]
        exact sum_congr rfl fun k _ => by
          rw [fldN_div, mul_assoc, ← pow_add, mul_add, Nat.add_comm (b * k)]
    · have hb : Nat.ble c (2 ^ d) = true := Nat.ble_eq_true_of_le hle
      rw [hb, Bool.cond_true]
      exact sprK_spec F b d c y hle hy

/-- **Sanity (concrete)**: two fields `3, 5` of width `4` spread to slots of width `8`. -/
theorem sprK_fixture : sprK 4 8 1 2 (3 + 5 * 16) = 3 + 5 * 256 := by
  rw [sprK_spec 4 8 1 2 _ (by norm_num) (by norm_num)]
  simp [fldN, Finset.sum_range_succ]

/-! ## Salted rows -/

/-- A salted packed row `(lo, cnt, F, x)`: fields `i = lo, …, lo + cnt − 1` of width `F` (offset
`2^{F−1}`) above a `64`-bit salt. -/
abbrev RowR := ℕ × ℕ × ℕ × ℕ

/-- The default (empty) row. -/
def rowD : RowR := (0, 0, 1, 0)

/-- The signed field `k` of a salted row. -/
def fldZ (r : RowR) (k : ℕ) : ℤ := (fldN r.2.2.1 (r.2.2.2 >>> 64) k : ℤ) - 2 ^ (r.2.2.1 - 1)

/-- **Rejected fixture**: forgetting the salt shift reads a different field. -/
theorem fldZ_reject :
    fldZ (0, 1, 4, 3 * 2 ^ 64 + 5) 0 ≠ ((fldN 4 (3 * 2 ^ 64 + 5) 0 : ℕ) : ℤ) - 8 := by
  simp only [fldZ, fldN, Nat.shiftRight_eq_div_pow]
  norm_num

/-- The image of a row at slot width `b` (spread, minus the offsets, shifted to `lo`). -/
def rowImgR (b : ℕ) (r : RowR) : ℤ :=
  (((sprK r.2.2.1 b 8 r.2.1 ((r.2.2.2 >>> 64) % (1 <<< (r.2.2.1 * r.2.1))) : ℕ) : ℤ) -
    ((rowOffs (2 ^ (r.2.2.1 - 1)) b r.2.1 : ℕ) : ℤ)) * ((1 <<< (b * r.1) : ℕ) : ℤ)

/-- **Specification of the row image**. -/
theorem rowImgR_spec (b : ℕ) (hb : 1 ≤ b) (r : RowR) (hc : r.2.1 ≤ 256) :
    rowImgR b r = ∑ k ∈ range r.2.1, fldZ r k * 2 ^ (b * (r.1 + k)) := by
  obtain ⟨lo, c, F, x⟩ := r
  simp only at hc ⊢
  have hm : (x >>> 64) % (1 <<< (F * c)) < 2 ^ (F * c) := by
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.mod_lt _ (by positivity)
  rw [rowImgR, sprK_spec F b 8 c _ (by simpa using hc) hm, rowOffs_spec _ _ _ hb]
  simp only [Nat.shiftLeft_eq, one_mul]
  push_cast
  rw [← sum_sub_distrib, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  rw [fldN_mod F _ c k (mem_range.1 hk), fldZ]
  simp only
  rw [mul_add, pow_add, ← pow_mul]
  ring

/-- **The grid of a list of salted rows** (row `j` is `rows.getD j rowD`). -/
def gridR (rows : List RowR) (i j : ℕ) : ℤ :=
  if (rows.getD j rowD).1 ≤ i ∧ i < (rows.getD j rowD).1 + (rows.getD j rowD).2.1 then
    fldZ (rows.getD j rowD) (i - (rows.getD j rowD).1) else 0

/-- **Sanity (degenerate)**: no rows, zero grid. -/
theorem gridR_nil (i j : ℕ) : gridR [] i j = 0 := by
  simp [gridR, rowD]

/-- The rows lie in the box `[0, 2N]` and have at most `256` fields. -/
def rowsOK (N : ℕ) (rows : List RowR) : Bool :=
  rows.all fun r => Nat.ble (r.1 + r.2.1) (2 * N + 1) && Nat.ble r.2.1 256

/-- Every row of a checked list (and the default row) lies in the box. -/
theorem rowsOK_getD {N : ℕ} {rows : List RowR} (h : rowsOK N rows = true) (j : ℕ) :
    (rows.getD j rowD).1 + (rows.getD j rowD).2.1 ≤ 2 * N + 1 ∧ (rows.getD j rowD).2.1 ≤ 256 := by
  have key : ∀ r ∈ rows, r.1 + r.2.1 ≤ 2 * N + 1 ∧ r.2.1 ≤ 256 := by
    intro r hr
    have := List.all_eq_true.1 h r hr
    simp only [Bool.and_eq_true] at this
    exact ⟨Nat.le_of_ble_eq_true this.1, Nat.le_of_ble_eq_true this.2⟩
  refine getD_prop (Pr := fun r : RowR => r.1 + r.2.1 ≤ 2 * N + 1 ∧ r.2.1 ≤ 256) key ?_ j
  simp [rowD]

/-- The sum of one grid row against `2^{b i}` is the row image. -/
theorem row_sum_gridR (b : ℕ) (hb : 1 ≤ b) (N : ℕ) (rows : List RowR) (j : ℕ)
    (h1 : (rows.getD j rowD).1 + (rows.getD j rowD).2.1 ≤ 2 * N + 1)
    (h2 : (rows.getD j rowD).2.1 ≤ 256) :
    ∑ i ∈ range (2 * N + 1), gridR rows i j * 2 ^ (b * i) = rowImgR b (rows.getD j rowD) := by
  rw [rowImgR_spec b hb _ h2]
  set r := rows.getD j rowD with hr
  have hsplit : 2 * N + 1 = r.1 + (r.2.1 + (2 * N + 1 - (r.1 + r.2.1))) := by omega
  rw [hsplit, sum_range_add, sum_range_add]
  have e1 : ∑ i ∈ range r.1, gridR rows i j * 2 ^ (b * i) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have : ¬ (r.1 ≤ i ∧ i < r.1 + r.2.1) := by simp at hi; omega
    simp only [gridR, ← hr, this, ↓reduceIte, zero_mul]
  have e3 : ∑ i ∈ range (2 * N + 1 - (r.1 + r.2.1)),
      gridR rows (r.1 + (r.2.1 + i)) j * 2 ^ (b * (r.1 + (r.2.1 + i))) = 0 := by
    refine sum_eq_zero fun i _ => ?_
    have : ¬ (r.1 ≤ r.1 + (r.2.1 + i) ∧ r.1 + (r.2.1 + i) < r.1 + r.2.1) := by omega
    simp only [gridR, ← hr, this, ↓reduceIte, zero_mul]
  rw [e1, e3, zero_add, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < r.2.1 := mem_range.1 hk
  have : r.1 ≤ r.1 + k ∧ r.1 + k < r.1 + r.2.1 := by omega
  simp only [gridR, ← hr, this, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

/-! ## Divide-and-conquer sums -/

/-- `∑_{k < c} f (off + k) 2^{B k}` by divide and conquer over `d` levels (`c ≤ 2^d`). -/
def dcZ (B : ℕ) (f : ℕ → ℤ) (d : ℕ) : ℕ → ℕ → ℤ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℤ) (fun off c => cond (Nat.beq c 0) 0 (f off))
    (fun d ih off c => cond (Nat.ble c (1 <<< d)) (ih off c)
      (ih off (1 <<< d) + ih (off + (1 <<< d)) (c - (1 <<< d)) * ((1 <<< (B <<< d) : ℕ) : ℤ))) d

/-- **Specification of `dcZ`**. -/
theorem dcZ_spec (B : ℕ) (f : ℕ → ℤ) : ∀ (d off c : ℕ), c ≤ 2 ^ d →
    dcZ B f d off c = ∑ k ∈ range c, f (off + k) * 2 ^ (B * k)
  | 0, off, c, hc => by
    change cond (Nat.beq c 0) 0 (f off) = _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hc) with rfl | rfl
    · rfl
    · simp
  | d + 1, off, c, hc => by
    change cond (Nat.ble c (1 <<< d)) (dcZ B f d off c)
      (dcZ B f d off (1 <<< d) + dcZ B f d (off + (1 <<< d)) (c - (1 <<< d)) *
        ((1 <<< (B <<< d) : ℕ) : ℤ)) = _
    simp only [Nat.shiftLeft_eq, one_mul]
    rcases Nat.lt_or_ge (2 ^ d) c with hlt | hle
    · have hb : Nat.ble c (2 ^ d) = false :=
        Bool.eq_false_iff.2 fun h => by have := Nat.le_of_ble_eq_true h; omega
      rw [hb, Bool.cond_false, dcZ_spec B f d off (2 ^ d) le_rfl,
        dcZ_spec B f d _ (c - 2 ^ d) (by rw [pow_succ] at hc; omega)]
      have hsplit : c = 2 ^ d + (c - 2 ^ d) := by omega
      conv_rhs => rw [hsplit, sum_range_add]
      congr 1
      rw [sum_mul]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      rw [mul_assoc, ← pow_add, mul_add, add_assoc, Nat.add_comm (B * k)]
    · have hb : Nat.ble c (2 ^ d) = true := Nat.ble_eq_true_of_le hle
      rw [hb, Bool.cond_true]
      exact dcZ_spec B f d off c hle

/-- **The Kronecker image of a grid of salted rows** at slot width `b`, row stride `W`, `R` rows. -/
def imgR (b W : ℕ) (rows : List RowR) (R : ℕ) : ℤ :=
  dcZ (b * W) (fun j => rowImgR b (rows.getD j rowD)) 9 0 R

/-- **The Kronecker image of `gridR`**: for rows inside the box, `kron b W` of the grid
polynomial is `imgR b W rows (2M + 1)`. -/
theorem kron_gridR (b W N M : ℕ) (hb : 1 ≤ b) (hM : 2 * M + 1 ≤ 512) (rows : List RowR)
    (hok : rowsOK N rows = true) :
    kron b W (gridPolyNM N M (gridR rows)) = imgR b W rows (2 * M + 1) := by
  rw [kron_gridPolyNM, packGridNM_eq, imgR, dcZ_spec _ _ 9 0 _ (by simpa using hM)]
  refine sum_congr rfl fun j _ => ?_
  obtain ⟨h1, h2⟩ := rowsOK_getD hok j
  rw [zero_add, ← row_sum_gridR b hb N rows j h1 h2, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← pow_add, mul_add, mul_assoc]

/-- **Sanity (accepted)**: the image of two one-field rows. -/
theorem imgR_fixture : imgR 8 1 [(0, 1, 4, 11 * 2 ^ 64 + 7), (0, 1, 4, 5 * 2 ^ 64 + 9)] 2 =
    3 + (-3) * 2 ^ 8 := by
  rw [imgR, dcZ_spec _ _ 9 0 2 (by norm_num)]
  simp [Finset.sum_range_succ, rowImgR, rowOffs, sprK_spec, fldN, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]

/-! ## The static `ℓ¹` bound -/

/-- The static `ℓ¹` bound `∑ cnt · 2^{F − 1}` of a list of rows. -/
def rowsL1 (rows : List RowR) : ℕ := (rows.map fun r => r.2.1 * 2 ^ (r.2.2.1 - 1)).sum

/-- A signed field is bounded by the offset. -/
theorem natAbs_fldZ_le (r : RowR) (k : ℕ) : (fldZ r k).natAbs ≤ 2 ^ (r.2.2.1 - 1) := by
  have h := Nat.mod_lt ((r.2.2.2 >>> 64) >>> (r.2.2.1 * k)) (Nat.two_pow_pos r.2.2.1)
  have hF : 2 ^ r.2.2.1 ≤ 2 * 2 ^ (r.2.2.1 - 1) := by
    rcases Nat.eq_zero_or_pos r.2.2.1 with h0 | h0
    · rw [h0]; norm_num
    · rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set a := (r.2.2.2 >>> 64) >>> (r.2.2.1 * k) % 2 ^ r.2.2.1 with ha
  set A := 2 ^ r.2.2.1
  set B := 2 ^ (r.2.2.1 - 1)
  have hx : |(a : ℤ) - (B : ℤ)| ≤ (B : ℤ) := abs_le.2 ⟨by omega, by omega⟩
  have e : fldZ r k = (a : ℤ) - (B : ℤ) := by simp only [fldZ, fldN, ha, B, A]; push_cast; rfl
  rw [e]
  exact_mod_cast (Int.natCast_natAbs ((a : ℤ) - (B : ℤ))).symm ▸ hx

/-- The row sum of the absolute values is at most `cnt · 2^{F−1}`. -/
theorem row_l1_gridR (N : ℕ) (rows : List RowR) (j : ℕ) :
    ∑ i ∈ range (2 * N + 1), (gridR rows i j).natAbs ≤
      (rows.getD j rowD).2.1 * 2 ^ ((rows.getD j rowD).2.2.1 - 1) := by
  set r := rows.getD j rowD with hr
  calc ∑ i ∈ range (2 * N + 1), (gridR rows i j).natAbs
      ≤ ∑ i ∈ range (r.1 + r.2.1), (gridR rows i j).natAbs := by
        rcases le_total (2 * N + 1) (r.1 + r.2.1) with h | h
        · exact sum_le_sum_of_subset (range_subset_range.2 h)
        · have hs : 2 * N + 1 = (r.1 + r.2.1) + (2 * N + 1 - (r.1 + r.2.1)) := by omega
          rw [hs, sum_range_add]
          have : ∑ i ∈ range (2 * N + 1 - (r.1 + r.2.1)),
              (gridR rows (r.1 + r.2.1 + i) j).natAbs = 0 := by
            refine sum_eq_zero fun i _ => ?_
            have : ¬ (r.1 ≤ r.1 + r.2.1 + i ∧ r.1 + r.2.1 + i < r.1 + r.2.1) := by omega
            simp only [gridR, ← hr, this, ↓reduceIte, Int.natAbs_zero]
          rw [this, add_zero]
    _ = ∑ k ∈ range r.2.1, (gridR rows (r.1 + k) j).natAbs := by
        rw [sum_range_add]
        have : ∑ i ∈ range r.1, (gridR rows i j).natAbs = 0 := by
          refine sum_eq_zero fun i hi => ?_
          have : ¬ (r.1 ≤ i ∧ i < r.1 + r.2.1) := by simp at hi; omega
          simp only [gridR, ← hr, this, ↓reduceIte, Int.natAbs_zero]
        rw [this, zero_add]
    _ ≤ ∑ k ∈ range r.2.1, 2 ^ (r.2.2.1 - 1) := by
        refine sum_le_sum fun k hk => ?_
        have : r.1 ≤ r.1 + k ∧ r.1 + k < r.1 + r.2.1 := by simp at hk; omega
        simp only [gridR, ← hr, this, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
        exact natAbs_fldZ_le r k
    _ = r.2.1 * 2 ^ (r.2.2.1 - 1) := by simp

/-- Sums over the first `n` cells of a list are at most the sum over the list (default `0`). -/
theorem sum_getD_le (f : RowR → ℕ) (hd : f rowD = 0) :
    ∀ (rows : List RowR) (n : ℕ), ∑ j ∈ range n, f (rows.getD j rowD) ≤ (rows.map f).sum
  | [], n => by simp [hd]
  | r :: rows, 0 => by simp
  | r :: rows, n + 1 => by
    rw [sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    have := sum_getD_le f hd rows n
    omega

/-- **The static `ℓ¹` bound** of a grid of salted rows. -/
theorem l1_gridR_le (N M : ℕ) (rows : List RowR) :
    l1 (gridPolyNM N M (gridR rows)) ≤ rowsL1 rows := by
  refine (l1_gridPolyNM_le N M _).trans ?_
  simp only [gridL1NM, rsumN_eq]
  refine (sum_le_sum fun j _ => row_l1_gridR N rows j).trans ?_
  exact sum_getD_le (fun r => r.2.1 * 2 ^ (r.2.2.1 - 1)) (by simp [rowD]) rows _

/-! ## Equality checks of grids -/

/-- `p 0 && ⋯ && p (n − 1)` (kernel-friendly). -/
def allBelowB (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allBelowB p n && p n

/-- Soundness of `allBelowB`. -/
theorem allBelowB_sound {p : ℕ → Bool} : ∀ {n : ℕ}, allBelowB p n = true → ∀ k < n, p k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    simp only [allBelowB, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allBelowB_sound h.1 k hk
    · exact h.2

/-- **Equality check of two grids** on the rows `j0, …, j0 + nj − 1`, columns `0, …, 2N`. -/
def chkGrid (N : ℕ) (f g : ℕ → ℕ → ℤ) (j0 nj : ℕ) : Bool :=
  allBelowB (fun dj => allBelowB (fun i => f i (j0 + dj) == g i (j0 + dj)) (2 * N + 1)) nj

/-- **Soundness of the equality check.** -/
theorem chkGrid_sound {N : ℕ} {f g : ℕ → ℕ → ℤ} {j0 nj : ℕ} (h : chkGrid N f g j0 nj = true) :
    ∀ dj < nj, ∀ i < 2 * N + 1, f i (j0 + dj) = g i (j0 + dj) := fun dj hdj i hi => by
  have := allBelowB_sound (allBelowB_sound h dj hdj) i hi
  simpa using this

/-- Grids that agree on the box have the same grid polynomial. -/
theorem gridPolyNM_congr {N M : ℕ} {f g : ℕ → ℕ → ℤ}
    (h : ∀ j < 2 * M + 1, ∀ i < 2 * N + 1, f i j = g i j) :
    gridPolyNM N M f = gridPolyNM N M g := by
  unfold gridPolyNM
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [h j (mem_range.1 hj) i (mem_range.1 hi)]

/-! ## Norms of node centres from the tree majorants -/

/-- **The norm of a node centre** from the majorants of its tree: if `c · X n = eval X e`, then
`‖x n‖ ≤ (majQ B e + dmajQ B E e)/|c| + E n`. -/
theorem Bd_ctr_of_node {r : ℝ} (hr : 0 ≤ r) {B E : ℕ → ℚ} {x X : ℕ → FA} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : Ex) (hv : below n e = true) (c : ℤ) (hc : c ≠ 0)
    (hrel : (c : ℂ) • X n = Ex.eval X e) (hEn : Bd r (X n - x n) (E n)) (Bn : ℚ)
    (hfin : (Ex.majQ B e + Ex.dmajQ B E e) / |(c : ℚ)| + E n ≤ Bn) : Bd r (x n) Bn := by
  obtain ⟨h1, h2⟩ := Bd_eval_sub_below hr hB hE e hv
  have h3 : Bd r (Ex.eval X e) ((Ex.majQ B e : ℝ) + Ex.dmajQ B E e) := by
    have := h1.add h2; rwa [add_sub_cancel] at this
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hX : X n = (c : ℂ)⁻¹ • Ex.eval X e := by
    rw [← hrel, smul_smul, inv_mul_cancel₀ hc', one_smul]
  have h4 := h3.smul ((c : ℂ)⁻¹)
  rw [← hX, norm_inv, Complex.norm_intCast] at h4
  have h5 : Bd r (x n) (|(c : ℝ)|⁻¹ * ((Ex.majQ B e : ℝ) + Ex.dmajQ B E e) + E n) := by
    have := h4.sub hEn
    rwa [sub_sub_cancel] at this
  refine h5.le ?_
  have := (Rat.cast_le (K := ℝ)).2 hfin
  push_cast at this
  rw [div_eq_inv_mul] at this
  linarith

/-! ## The `R`-form substitution in the strip algebra -/

/-- `Rl` is `R₀ + u` (strip algebra). -/
theorem ev_Rl_H (x : Fin 6 → FA) : DkPoly.ev x Rl = algebraMap ℂ FA ((R0q : ℚ) : ℂ) + x 0 := by
  simp only [Rl, DkPoly.ev_cons, DkPoly.ev_nil, DkPoly.Tm.ev]
  simp

/-- `RpowL n` is `(R₀ + u)ⁿ` (strip algebra). -/
theorem ev_RpowL_H (x : Fin 6 → FA) :
    ∀ n, DkPoly.ev x (RpowL n) = (algebraMap ℂ FA ((R0q : ℚ) : ℂ) + x 0) ^ n
  | 0 => by simp [RpowL, DkPoly.Tm.ev]
  | n + 1 => by rw [RpowL, DkPoly.ev_mul, ev_RpowL_H x n, ev_Rl_H, pow_succ, mul_comm]

/-- **The substitution** `R = R₀ + u` in the strip algebra. -/
theorem ev_substR_H (x : Fin 6 → FA) (p : DkPoly.SP) :
    DkPoly.ev x (substR p) =
      DkPoly.ev ![algebraMap ℂ FA ((R0q : ℚ) : ℂ) + x 0, x 1, x 2, x 3, 0, 0] p := by
  induction p with
  | nil => simp [substR]
  | cons t p ih =>
    simp only [substR, List.foldr_cons] at ih ⊢
    rw [DkPoly.ev_merge, ih, DkPoly.ev_mulMono, ev_RpowL_H, DkPoly.ev_cons]
    simp only [DkPoly.Tm.ev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, pow_zero, one_mul]
    ring

end PlasmaLean.Design.DommaschkKamC
