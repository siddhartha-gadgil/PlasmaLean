/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallChebChain
public import PlasmaLean.Certificates.KronBallChebSpread

/-!
# Family environments: fast images, constants, embeddings

Supporting facts for the family ball chains (`Design/RationalStellaratorGCFam*`):

* `famPackN`: the Kronecker image of a grid family without a symbol, computed with natural
  numbers only (`slicePackN`), equal to `famPack` (`famPackN_eq`);
* the family centres of the constant variables: `ctr3_T3` (`t = 1`), `ctr3_V3` (`V = 1`),
  `ctr3_C` (constants in `w`);
* **embedding**: a family stored in a smaller layout `(N, M)` and scale `2^S`, read in the layout
  `(N + dN, M + dM)` with scale `2^{S + s}` and symbol `2^s`, has the same centre
  (`famCtr_embed`);
* the parameter family `famCtr` of the slices `(64 · 2^S, 2^{S−1})`: `64 + (c + c⁻¹)/2`
  (`famCtr_param`), which is `64 + cos ϑ` at `c = e^{iϑ}`.

**Sanity.** `famPackN_nil`: the empty family has image `0`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.KronBallCheb

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronDigits PlasmaLean.Theory.KAM
  Complex

/-- **The Kronecker image of a grid family without symbol** (symbol `c₀`, sign `−1` if `odd`),
natural numbers only per field. -/
def famPackN (b W R N M D c0 : ℕ) (odd : Bool) (dd dr : ℕ) : ℕ → List SliceData → ℤ
  | _, [] => 0
  | k, sd :: rest => slicePackN b W N M c0 odd dd dr sd *
      ((((1 <<< (b * W * R * (D + k))) : ℕ) : ℤ) +
        (if k = 0 then (0 : ℤ) else (((1 <<< (b * W * R * (D - k))) : ℕ) : ℤ))) +
      famPackN b W R N M D c0 odd dd dr (k + 1) rest

/-- **Sanity**: the empty family. -/
theorem famPackN_nil (b W R N M D c0 : ℕ) (odd : Bool) (dd dr k : ℕ) :
    famPackN b W R N M D c0 odd dd dr k [] = 0 := rfl

/-- **`famPackN` equals `famPack`.** -/
theorem famPackN_eq (b W R N M D c0 : ℕ) (odd : Bool) {dd dr : ℕ} (hb : 1 ≤ b) (hW : 1 ≤ W) :
    ∀ (k : ℕ) (l : List SliceData), (∀ sd ∈ l, SliceOK N M dd dr sd ∧
      2 * c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) →
      famPackN b W R N M D c0 odd dd dr k l =
        famPack b W R N M D (if odd then -1 else 1) c0 0 0 dd dr k l
  | _, [], _ => rfl
  | k, sd :: rest, h => by
    rw [famPackN, famPack, famPackN_eq b W R N M D c0 odd hb hW (k + 1) rest
      fun sd' h' => h sd' (List.mem_cons_of_mem _ h'),
      slicePackN_eq hb hW (h sd List.mem_cons_self).1 (h sd List.mem_cons_self).2 odd]

/-- `famPackN` as a sum over the list. -/
theorem famPackN_sum (b W R N M D c0 : ℕ) (odd : Bool) (dd dr : ℕ) :
    ∀ (k : ℕ) (l : List SliceData), famPackN b W R N M D c0 odd dd dr k l =
      ∑ i ∈ range l.length, slicePackN b W N M c0 odd dd dr (l.getD i SliceData.zero) *
        ((((1 <<< (b * W * R * (D + (k + i)))) : ℕ) : ℤ) +
          (if k + i = 0 then (0 : ℤ) else (((1 <<< (b * W * R * (D - (k + i)))) : ℕ) : ℤ)))
  | _, [] => by simp [famPackN]
  | k, sd :: rest => by
    rw [famPackN, famPackN_sum b W R N M D c0 odd dd dr (k + 1) rest, List.length_cons,
      sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [show k + 1 + i = k + (i + 1) by ring]

/-- **The Kronecker image of a grid family by divide and conquer over the Laurent positions**
(`D' + 1` coefficients, positions `D − D' … D + D'`): every intermediate integer is built once, by
`bsplit`. -/
def famPackB (b W R N M D c0 : ℕ) (odd : Bool) (dd dr dw : ℕ) (l : List SliceData) : ℤ :=
  bsplit (fun p => slicePackN b W N M c0 odd dd dr
      (l.getD (if p ≤ l.length - 1 then l.length - 1 - p else p - (l.length - 1)) SliceData.zero))
    (b * W * R) dw 0 (2 * (l.length - 1) + 1) *
    (((1 <<< (b * W * R * (D - (l.length - 1)))) : ℕ) : ℤ)

/-- Reindexing the Laurent positions: `∑_{p ≤ 2D'} F(|p − D'|) X^{p + D − D'} =
∑_{i ≤ D'} F(i) (X^{D + i} + [i > 0] X^{D − i})`. -/
theorem laurent_sum (F : ℕ → ℤ) (B D D' : ℕ) (hD : D' ≤ D) :
    (∑ p ∈ range (2 * D' + 1), F (if p ≤ D' then D' - p else p - D') * (2 : ℤ) ^ (B * p)) *
      2 ^ (B * (D - D')) =
    ∑ i ∈ range (D' + 1), F i * ((2 : ℤ) ^ (B * (D + i)) +
      (if i = 0 then (0 : ℤ) else 2 ^ (B * (D - i)))) := by
  rw [show 2 * D' + 1 = D' + (D' + 1) by ring, sum_range_add, add_mul, sum_mul, sum_mul]
  have hlow : ∑ x ∈ range D', F (if x ≤ D' then D' - x else x - D') * (2 : ℤ) ^ (B * x) *
      2 ^ (B * (D - D')) =
      ∑ i ∈ range (D' + 1), F i * (if i = 0 then (0 : ℤ) else 2 ^ (B * (D - i))) := by
    rw [sum_range_succ']
    simp only [↓reduceIte, mul_zero, add_zero, Nat.add_one_ne_zero]
    rw [← sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    rw [ite_eq_left (show D' - 1 - x ≤ D' by omega), show D' - (D' - 1 - x) = x + 1 by omega,
      mul_assoc, ← pow_add]
    congr 2
    rw [← mul_add]; congr 1; omega
  have hhigh : ∑ x ∈ range (D' + 1), F (if D' + x ≤ D' then D' - (D' + x) else D' + x - D') *
      (2 : ℤ) ^ (B * (D' + x)) * 2 ^ (B * (D - D')) =
      ∑ i ∈ range (D' + 1), F i * 2 ^ (B * (D + i)) := by
    refine sum_congr rfl fun x _ => ?_
    have : F (if D' + x ≤ D' then D' - (D' + x) else D' + x - D') = F x := by
      split_ifs with h
      · rw [show x = 0 by omega, add_zero, Nat.sub_self]
      · rw [show D' + x - D' = x by omega]
    rw [this, mul_assoc, ← pow_add]
    congr 2
    rw [← mul_add]; congr 1; omega
  rw [hlow, hhigh, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **`famPackB` equals `famPackN`** (for `D' ≤ D`). -/
theorem famPackB_eq (b W R N M D c0 : ℕ) (odd : Bool) (dd dr dw : ℕ) (l : List SliceData)
    (hl : 1 ≤ l.length) (hD : l.length - 1 ≤ D) (hdw : 2 * (l.length - 1) + 1 ≤ 2 ^ dw) :
    famPackB b W R N M D c0 odd dd dr dw l = famPackN b W R N M D c0 odd dd dr 0 l := by
  rw [famPackB, bsplit_eq _ _ dw 0 _ hdw, famPackN_sum]
  simp only [zero_add, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [laurent_sum (fun i => slicePackN b W N M c0 odd dd dr (l.getD i SliceData.zero)) _ D _ hD,
    show l.length - 1 + 1 = l.length by omega]

/-- The offset image of a stored coefficient (natural number). -/
def sliceT (b W N M c0 : ℕ) (odd : Bool) (dd dr : ℕ) (sd : SliceData) : ℕ :=
  (bsplitN (fun r => rowN b N M c0 odd dd sd (M - sd.Mj + r)) (b * W) dr 0 (2 * sd.Mj + 1)) <<<
    (b * W * (M - sd.Mj))

/-- The image of a stored coefficient is its offset image minus the offsets. -/
theorem slicePackN_eq_sub (b W N M c0 : ℕ) (odd : Bool) (dd dr : ℕ) (sd : SliceData) :
    slicePackN b W N M c0 odd dd dr sd = (sliceT b W N M c0 odd dd dr sd : ℤ) - sliceO b W N M sd :=
  rfl

/-- **The offset image of a grid family** (natural numbers only, divide and conquer over the
Laurent positions). -/
def famT (b W R N M D c0 : ℕ) (odd : Bool) (dd dr dw : ℕ) (l : List SliceData) : ℕ :=
  bsplitN (fun p => sliceT b W N M c0 odd dd dr (l.getD (lpos (l.length - 1) p) SliceData.zero))
    (b * W * R) dw 0 (2 * (l.length - 1) + 1) <<< (b * W * R * (D - (l.length - 1)))

/-- **The image of a grid family is `famT − famO`.** -/
theorem famT_sub_famO (b W R N M D c0 : ℕ) (odd : Bool) (dd dr dw : ℕ) (l : List SliceData)
    (hl : 1 ≤ l.length) (hD : l.length - 1 ≤ D) (hdw : 2 * (l.length - 1) + 1 ≤ 2 ^ dw) :
    (famT b W R N M D c0 odd dd dr dw l : ℤ) - famO b W R N M D dw l =
      famPackN b W R N M D c0 odd dd dr 0 l := by
  rw [famPackN_sum, famT, famO, bsplitN_eq _ _ dw 0 _ hdw, bsplitN_eq _ _ dw 0 _ hdw]
  simp only [zero_add, Nat.shiftLeft_eq, one_mul]
  push_cast
  rw [← sub_mul, ← sum_sub_distrib]
  have := laurent_sum (fun i => slicePackN b W N M c0 odd dd dr (l.getD i SliceData.zero))
    (b * W * R) D (l.length - 1) hD
  rw [show l.length - 1 + 1 = l.length by omega] at this
  rw [← this]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [slicePackN_eq_sub, sub_mul]
  rfl

/-! ## Fast rows: spreading with masks -/

/-- `rawF` is the field `fld`. -/
theorem rawF_eq_fld (F x t : ℕ) : rawF F x t = fld F x t := rfl

/-- **The offset image of a row by masks** (`2^{kr} ≥ N_j` fields per half row). -/
def rowNF (b N M c0 : ℕ) (odd : Bool) (kr : ℕ) (sd : SliceData) (j : ℕ) : ℕ :=
  ((c0 * spreadRow sd.Fj b kr sd.Nj (sd.row (j + sd.Mj - M)) +
      (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj) <<< (b * (N + 1))) +
    ((if odd then (2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj -
        c0 * spreadRowR sd.Fj b kr sd.Nj (sd.row (M + sd.Mj - j))
      else c0 * spreadRowR sd.Fj b kr sd.Nj (sd.row (M + sd.Mj - j)) +
        (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj) <<< (b * (N - sd.Nj))) +
    (centreN b M c0 odd sd j <<< (b * N))

/-- `c₀ · dexp + c · ones` is the expansion of `digN`. -/
theorem dexp_digN_false (b m c n : ℕ) (g : ℕ → ℕ) (hb : 1 ≤ b) :
    m * dexp b g n + c * onesK b n = dexp b (fun t => digN m c false (g t)) n := by
  rw [onesK_eq b n hb, mul_dexp, mul_dexp, dexp_add_fun]
  simp [digN]

/-- `c · ones − c₀ · dexp` is the expansion of the negative `digN`. -/
theorem dexp_digN_true (b m c n : ℕ) (g : ℕ → ℕ) (hb : 1 ≤ b) (hg : ∀ t, t < n → m * g t ≤ c) :
    c * onesK b n - m * dexp b g n = dexp b (fun t => digN m c true (g t)) n := by
  rw [onesK_eq b n hb, mul_dexp, mul_dexp, dexp_sub b n fun t ht => by simpa using hg t ht]
  simp [digN]

/-- **The fast row equals `rowN`.** -/
theorem rowNF_eq {b N M c0 : ℕ} {sd : SliceData} (odd : Bool) (kr dd : ℕ) (hFb : sd.Fj ≤ b)
    (hF : 1 ≤ sd.Fj) (hkr : sd.Nj ≤ 2 ^ kr) (hdd : sd.Nj ≤ 2 ^ dd)
    (hH : c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) (j : ℕ) :
    rowNF b N M c0 odd kr sd j = rowN b N M c0 odd dd sd j := by
  have hb : 1 ≤ b := le_trans hF hFb
  have h1 : c0 * spreadRow sd.Fj b kr sd.Nj (sd.row (j + sd.Mj - M)) +
      (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj =
      rpN b sd.Fj c0 (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) false dd sd.Nj
        (sd.row (j + sd.Mj - M)) := by
    rw [spreadRow_eq hFb hF hkr, dexp_digN_false _ _ _ _ _ hb, rpN_eq _ _ _ _ _ dd _ _ hdd, dexp]
    rfl
  have h2 : (if odd then (2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj -
        c0 * spreadRowR sd.Fj b kr sd.Nj (sd.row (M + sd.Mj - j))
      else c0 * spreadRowR sd.Fj b kr sd.Nj (sd.row (M + sd.Mj - j)) +
        (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj) =
      rpNR b sd.Fj c0 (if odd then 2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)
        else 2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) odd dd sd.Nj
        (sd.row (M + sd.Mj - j)) := by
    rw [rpNR_eq _ _ _ _ _ dd _ _ hdd, spreadRowR_eq hFb hF hkr]
    cases odd
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [dexp_digN_false _ _ _ _ _ hb, dexp]
      rfl
    · simp only [↓reduceIte]
      rw [dexp_digN_true _ _ _ _ _ hb, dexp]
      · rfl
      · intro t _
        have h1 := fld_lt sd.Fj (sd.row (M + sd.Mj - j)) (sd.Nj - 1 - t)
        rw [show (2 : ℕ) ^ sd.Fj = 2 * 2 ^ (sd.Fj - 1) by rw [← pow_succ']; congr 1; omega] at h1
        nlinarith
  rw [rowNF, rowN, h1, h2]

/-- **The fast offset image of a coefficient.** -/
def sliceTF (b W N M c0 : ℕ) (odd : Bool) (kr dr : ℕ) (sd : SliceData) : ℕ :=
  (bsplitN (fun r => rowNF b N M c0 odd kr sd (M - sd.Mj + r)) (b * W) dr 0 (2 * sd.Mj + 1)) <<<
    (b * W * (M - sd.Mj))

/-- The offset image of a stored coefficient by fast rows. -/
theorem sliceTF_eq {b W N M c0 : ℕ} {sd : SliceData} (odd : Bool) (kr dd dr : ℕ)
    (hFb : sd.Fj ≤ b) (hF : 1 ≤ sd.Fj) (hkr : sd.Nj ≤ 2 ^ kr) (hdd : sd.Nj ≤ 2 ^ dd)
    (hH : c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) :
    sliceTF b W N M c0 odd kr dr sd = sliceT b W N M c0 odd dd dr sd := by
  unfold sliceTF sliceT
  congr 2
  funext r
  exact rowNF_eq odd kr dd hFb hF hkr hdd hH _

/-- **The fast offset image of a grid family** (masks for the rows, divide and conquer for the
rows and the Laurent positions; natural numbers only). -/
def famTF (b W R N M D c0 : ℕ) (odd : Bool) (kr dr dw : ℕ) (l : List SliceData) : ℕ :=
  bsplitN (fun p => sliceTF b W N M c0 odd kr dr (l.getD (lpos (l.length - 1) p) SliceData.zero))
    (b * W * R) dw 0 (2 * (l.length - 1) + 1) <<< (b * W * R * (D - (l.length - 1)))

/-- The offset image of a family by fast rows. -/
theorem famTF_eq (b W R N M D c0 : ℕ) (odd : Bool) (kr dd dr dw : ℕ) (l : List SliceData)
    (hb : 1 ≤ b) (hc0 : c0 ≤ 2 ^ (b - 1))
    (h : ∀ sd ∈ l, sd.Fj ≤ b ∧ 1 ≤ sd.Fj ∧ sd.Nj ≤ 2 ^ kr ∧ sd.Nj ≤ 2 ^ dd ∧
      c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) :
    famTF b W R N M D c0 odd kr dr dw l = famT b W R N M D c0 odd dd dr dw l := by
  unfold famTF famT
  congr 2
  funext p
  obtain ⟨h1, h2, h3, h4, h5⟩ := getD_prop (Pr := fun sd : SliceData => sd.Fj ≤ b ∧ 1 ≤ sd.Fj ∧
    sd.Nj ≤ 2 ^ kr ∧ sd.Nj ≤ 2 ^ dd ∧ c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) (d := SliceData.zero) h
    (show (1 : ℕ) ≤ b ∧ 1 ≤ 1 ∧ 0 ≤ 2 ^ kr ∧ 0 ≤ 2 ^ dd ∧ c0 * 2 ^ (1 - 1) ≤ 2 ^ (b - 1) from
      ⟨hb, le_rfl, Nat.zero_le _, Nat.zero_le _, by simpa using hc0⟩) (lpos (l.length - 1) p)
  exact sliceTF_eq odd kr dd dr h1 h2 h3 h4 h5

/-! ## Fast coefficients: spreading whole blocks -/

/-- The fields of a row literal are fields of the block. -/
theorem fld_row (sd : SliceData) (r t : ℕ) (ht : t < sd.Nj) :
    fld sd.Fj (sd.row r) t = fld sd.Fj sd.blk (sd.Nj * r + t) := by
  rw [SliceData.row, ← rawF_eq_fld, ← rawF_eq_fld, show sd.Fj * sd.Nj * r = sd.Fj * (sd.Nj * r) by
    ring, rawF_mod ht, rawF_shiftRight]

/-- Spreading the rows of an expansion of `R ≤ 2^{k₂}` rows to row stride `W`. -/
theorem spread_rows {b W Nj R k2 : ℕ} (hb : 1 ≤ b) (hNj : 1 ≤ Nj) (hNW : Nj ≤ W) (hR : R ≤ 2 ^ k2)
    (g : ℕ → ℕ) (hg : ∀ i, g i < 2 ^ b) :
    spread (b * Nj) (b * W) k2 (dexp b g (R * Nj)) =
      ∑ r ∈ range R, dexp b (fun t => g (Nj * r + t)) Nj * 2 ^ (b * W * r) := by
  set S : ℕ → ℕ := fun r => if r < R then dexp b (fun t => g (Nj * r + t)) Nj else 0 with hS
  have hSlt : ∀ r, S r < 2 ^ (b * Nj) := fun r => by
    simp only [hS]; split_ifs
    · exact dexp_lt fun t _ => hg _
    · positivity
  have h1 : dexp b g (R * Nj) = dexp (b * Nj) S (2 ^ k2) := by
    rw [mul_comm R Nj, dexp_rows, dexp]
    rw [← sum_subset (range_subset_range.2 hR) fun r _ hr => by
      simp only [hS, mem_range] at hr ⊢; rw [ite_eq_right hr]; ring]
    refine sum_congr rfl fun r hr => ?_
    simp only [hS, mem_range.1 hr, ↓reduceIte, ← pow_mul]
    congr 1
    · exact dexp_congr b Nj fun t _ => by rw [add_comm, mul_comm]
  rw [h1, spread_dexp (Nat.mul_le_mul_left _ hNW) (Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (by omega))) hSlt, dexp]
  rw [← sum_subset (range_subset_range.2 hR) fun r _ hr => by
    simp only [hS, mem_range] at hr ⊢; rw [ite_eq_right hr, zero_mul]]
  refine sum_congr rfl fun r hr => ?_
  simp only [hS, mem_range.1 hr, ↓reduceIte]

/-- Termwise subtraction of natural-number sums. -/
theorem sum_sub_of_le {s : Finset ℕ} {f g : ℕ → ℕ} (h : ∀ i ∈ s, g i ≤ f i) :
    ∑ i ∈ s, f i - ∑ i ∈ s, g i = ∑ i ∈ s, (f i - g i) := by
  have : ∑ i ∈ s, f i = ∑ i ∈ s, g i + ∑ i ∈ s, (f i - g i) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i hi => by rw [Nat.add_sub_cancel' (h i hi)]
  omega

/-- The mirrored halves of all rows by block spreading. -/
theorem mirBlk_eq {b W F Nj R k1 k2 x : ℕ} (hFb : F ≤ b) (hF : 1 ≤ F) (hNj : 1 ≤ Nj)
    (hNW : Nj ≤ W) (hk1 : R * Nj ≤ 2 ^ k1) (hk2 : R ≤ 2 ^ k2) :
    mirBlk b W F Nj R k1 k2 x = ∑ r ∈ range R,
      dexp b (fun t => fld F x (Nj * (R - 1 - r) + (Nj - 1 - t))) Nj * 2 ^ (b * W * r) := by
  have hb : 1 ≤ b := le_trans hF hFb
  have hfb : ∀ t, fld F x (R * Nj - 1 - t) < 2 ^ b := fun t =>
    lt_of_lt_of_le (fld_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hFb)
  rw [mirBlk, spreadRowR_eq hFb hF hk1, spread_rows hb hNj hNW hk2 _ hfb]
  refine sum_congr rfl fun r hr => ?_
  congr 1
  refine dexp_congr b Nj fun t ht => ?_
  have hr' := mem_range.1 hr
  congr 1
  have : Nj * r + Nj * (R - 1 - r) + Nj = R * Nj := by
    rw [← mul_add, ← mul_add_one, show r + (R - 1 - r) + 1 = R by omega, mul_comm]
  omega

/-- **The block-spread image equals the row image.** -/
theorem sliceTB_eq {b W N M c0 : ℕ} {sd : SliceData} (odd : Bool) (dd dr : ℕ)
    (hFb : sd.Fj ≤ b) (hF : 1 ≤ sd.Fj) (hNW : sd.Nj ≤ W) (hMj : sd.Mj ≤ M)
    (hk1 : (2 * sd.Mj + 1) * sd.Nj ≤ 2 ^ sd.k1)
    (hk2 : 2 * sd.Mj + 1 ≤ 2 ^ sd.k2) (hdd : sd.Nj ≤ 2 ^ dd) (hdr : 2 * sd.Mj + 1 ≤ 2 ^ dr)
    (hH : c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)) :
    sliceTB b W N M c0 odd dr sd = sliceT b W N M c0 odd dd dr sd := by
  have hb : 1 ≤ b := le_trans hF hFb
  set R := 2 * sd.Mj + 1 with hR
  set c := 2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1) with hc
  have hfb : ∀ t, fld sd.Fj sd.blk t < 2 ^ b := fun t =>
    lt_of_lt_of_le (fld_lt _ _ t) (Nat.pow_le_pow_right (by norm_num) hFb)
  -- the right halves
  have hright : c0 * rightBlk b W sd.Fj sd.Nj R sd.k1 sd.k2 sd.blk +
      c * (onesK b sd.Nj * onesK (b * W) R) =
      ∑ r ∈ range R, rpN b sd.Fj c0 c false dd sd.Nj (sd.row r) * 2 ^ (b * W * r) := by
    rcases Nat.eq_zero_or_pos sd.Nj with h0 | h0
    · have e : ∀ r, rpN b sd.Fj c0 c false dd sd.Nj (sd.row r) = 0 := fun r => by
        rw [rpN_eq _ _ _ _ _ dd _ _ hdd, h0]; simp
      have e1 : rightBlk b W sd.Fj sd.Nj R sd.k1 sd.k2 sd.blk = 0 := by
        simp [rightBlk, spreadRow, h0, spread_zero, Nat.shiftLeft_eq, Nat.mod_one]
      have e2 : onesK b sd.Nj = 0 := by simp [onesK, h0, Nat.shiftLeft_eq]
      simp [e, e1, e2]
    · rw [rightBlk, spreadRow_eq hFb hF hk1, spread_rows hb h0 hNW hk2 _ hfb, mul_sum,
        onesK_eq (b * W) R (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))), dexp,
        mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun r _ => ?_
      have hS : dexp b (fun t => fld sd.Fj sd.blk (sd.Nj * r + t)) sd.Nj =
          dexp b (fld sd.Fj (sd.row r)) sd.Nj :=
        dexp_congr b _ fun t ht => (fld_row sd r t ht).symm
      have hD := dexp_digN_false b c0 c sd.Nj (fld sd.Fj (sd.row r)) hb
      rw [rpN_eq _ _ _ _ _ dd _ _ hdd]
      simp only [rawF_eq_fld]
      rw [show (∑ t ∈ range sd.Nj, digN c0 c false (fld sd.Fj (sd.row r) t) * 2 ^ (b * t)) =
        dexp b (fun t => digN c0 c false (fld sd.Fj (sd.row r) t)) sd.Nj from rfl, ← hD, hS]
      ring
  -- the mirrored halves
  set c' := if odd then 2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1) else 2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)
    with hc'
  have hmir : (if odd then (2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)) *
        (onesK b sd.Nj * onesK (b * W) R) - c0 * mirBlk b W sd.Fj sd.Nj R sd.k1 sd.k2 sd.blk
      else c0 * mirBlk b W sd.Fj sd.Nj R sd.k1 sd.k2 sd.blk +
        c * (onesK b sd.Nj * onesK (b * W) R)) =
      ∑ r ∈ range R,
        rpNR b sd.Fj c0 c' odd dd sd.Nj (sd.row (2 * sd.Mj - r)) * 2 ^ (b * W * r) := by
    rcases Nat.eq_zero_or_pos sd.Nj with h0 | h0
    · have e : ∀ r, rpNR b sd.Fj c0 c' odd dd sd.Nj (sd.row r) = 0 := fun r => by
        rw [rpNR_eq _ _ _ _ _ dd _ _ hdd, h0]; simp
      have e1 : mirBlk b W sd.Fj sd.Nj R sd.k1 sd.k2 sd.blk = 0 := by
        simp only [mirBlk, h0, mul_zero]
        rw [spreadRowR_eq hFb hF (Nat.zero_le _), dexp_zero, spread_zero]
      have e2 : onesK b sd.Nj = 0 := by simp [onesK, h0, Nat.shiftLeft_eq]
      cases odd <;> simp [e, e1, e2]
    · set S : ℕ → ℕ := fun r => dexp b (fun t => fld sd.Fj (sd.row (2 * sd.Mj - r))
        (sd.Nj - 1 - t)) sd.Nj with hS
      have hmb : mirBlk b W sd.Fj sd.Nj R sd.k1 sd.k2 sd.blk =
          ∑ r ∈ range R, S r * 2 ^ (b * W * r) := by
        rw [mirBlk_eq hFb hF h0 hNW hk1 hk2]
        refine sum_congr rfl fun r hr => ?_
        congr 1
        exact dexp_congr b _ fun t ht => by
          rw [fld_row sd _ _ (by omega), show R - 1 - r = 2 * sd.Mj - r by omega]
      have hpat : onesK b sd.Nj * onesK (b * W) R =
          ∑ r ∈ range R, onesK b sd.Nj * 2 ^ (b * W * r) := by
        rw [onesK_eq (b * W) R (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))),
          dexp, mul_sum]
        simp
      have hdig : ∀ r, rpNR b sd.Fj c0 c' odd dd sd.Nj (sd.row (2 * sd.Mj - r)) =
          (if odd then (2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj - c0 * S r
          else c0 * S r + c * onesK b sd.Nj) := fun r => by
        rw [rpNR_eq _ _ _ _ _ dd _ _ hdd]
        simp only [rawF_eq_fld]
        cases odd
        · simp only [Bool.false_eq_true, ↓reduceIte, hc', hc, hS]
          rw [dexp_digN_false _ _ _ _ _ hb]; rfl
        · simp only [↓reduceIte, hc', hS]
          rw [dexp_digN_true _ _ _ _ _ hb]
          · rfl
          · intro t _
            have h1 := fld_lt sd.Fj (sd.row (2 * sd.Mj - r)) (sd.Nj - 1 - t)
            rw [show (2 : ℕ) ^ sd.Fj = 2 * 2 ^ (sd.Fj - 1) by
              rw [← pow_succ']; congr 1; omega] at h1
            nlinarith
      rw [hmb, hpat]
      cases odd
      · simp only [Bool.false_eq_true, ↓reduceIte] at hdig ⊢
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun r _ => ?_
        rw [hdig r]
        ring
      · simp only [↓reduceIte] at hdig ⊢
        rw [mul_sum, mul_sum, sum_sub_of_le fun r _ => ?_]
        · refine sum_congr rfl fun r _ => ?_
          rw [hdig r, Nat.sub_mul, mul_assoc, mul_assoc, mul_assoc]
        · rw [← mul_assoc, ← mul_assoc]
          refine Nat.mul_le_mul_right _ ?_
          rw [hS, onesK_eq b _ hb, mul_dexp, mul_dexp]
          refine sum_le_sum fun t _ => Nat.mul_le_mul_right _ ?_
          have h1 := fld_lt sd.Fj (sd.row (2 * sd.Mj - r)) (sd.Nj - 1 - t)
          rw [show (2 : ℕ) ^ sd.Fj = 2 * 2 ^ (sd.Fj - 1) by rw [← pow_succ']; congr 1; omega] at h1
          simp only [mul_one]
          nlinarith
  -- the centre column and the assembly
  have hband : ∀ r, r < R →
      M - sd.Mj + r + sd.Mj - M = r ∧ M + sd.Mj - (M - sd.Mj + r) = 2 * sd.Mj - r :=
    fun r hr => ⟨by omega, by omega⟩
  rw [sliceTB, sliceT, hright, hmir, bsplitN_eq _ _ dr 0 _ hdr, bsplitN_eq _ _ dr 0 _ hdr]
  congr 1
  simp only [zero_add, rowN, Nat.shiftLeft_eq, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun r hr => ?_
  obtain ⟨e1, e2⟩ := hband r (mem_range.1 hr)
  rw [e1, e2]
  ring

/-- The conditions on a stored coefficient for the block-spread image. -/
def SliceFast (b W M dd dr c0 : ℕ) (sd : SliceData) : Prop :=
  sd.Fj ≤ b ∧ 1 ≤ sd.Fj ∧ sd.Nj ≤ W ∧ sd.Mj ≤ M ∧ (2 * sd.Mj + 1) * sd.Nj ≤ 2 ^ sd.k1 ∧
    2 * sd.Mj + 1 ≤ 2 ^ sd.k2 ∧ sd.Nj ≤ 2 ^ dd ∧ 2 * sd.Mj + 1 ≤ 2 ^ dr ∧
    c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1)

/-- The conditions of the fast image are decidable. -/
instance (b W M dd dr c0 : ℕ) (sd : SliceData) : Decidable (SliceFast b W M dd dr c0 sd) := by
  unfold SliceFast; infer_instance

/-- **`famTB` equals `famT`.** -/
theorem famTB_eq (b W R N M D c0 : ℕ) (odd : Bool) (dd dr dw : ℕ) (l : List SliceData)
    (hl : 1 ≤ l.length) (hdw : 2 * (l.length - 1) + 1 ≤ 2 ^ dw)
    (h : ∀ sd ∈ l, SliceFast b W M dd dr c0 sd) :
    famTB b W R N M D c0 odd dr dw l = famT b W R N M D c0 odd dd dr dw l := by
  unfold famTB famT
  rw [bsplitN_eq _ _ dw 0 _ hdw, bsplitN_eq _ _ dw 0 _ hdw]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  have hp' : lpos (l.length - 1) p < l.length := by
    have := mem_range.1 hp; unfold lpos; split_ifs <;> omega
  rw [zero_add, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hp',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp']
  simp only [Option.map_some, Option.getD_some]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h _ (List.getElem_mem hp')
  rw [sliceTB_eq odd dd dr h1 h2 h3 h4 h5 h6 h7 h8 h9]

/-! ## The constant variables -/

/-- The family centre of `t` is `1`. -/
theorem ctr3_T3 (S N M D : ℕ) {c : ℂ} (hc : c ≠ 0) : ctr3 S N M D c (1, 0, 0) (T3 S N M D) = 1 := by
  rw [T3, mul_comm (Polynomial.C (Tpoly S N M)) ((X : P3) ^ D), ctr3_X_pow_C, ctr_Tpoly, mul_one,
    mul_one, mul_inv_cancel₀ (pow_ne_zero _ hc), map_one]

/-- A family constant in `w`, of weight `(0, e, p)`, is the one-parameter centre. -/
theorem ctr3_C_w0 (S N M D : ℕ) (c : ℂ) (e p : ℕ) (P : P2) :
    ctr3 S N M D c (0, e, p) (Polynomial.C P) = ctr S N M (0, e, p) P := by
  have := ctr3_X_pow_C S N M D c (0, e, p) 0 P
  simpa using this

/-- The family centre of `V` is `1`. -/
theorem ctr3_V3 (S N M D : ℕ) (c : ℂ) : ctr3 S N M D c (0, 1, 0) V3 = 1 := by
  rw [V3, ctr3_C_w0, ctr_Vpoly]

/-! ## Embedding -/

/-- The stored half grid in a larger layout is the shifted half grid. -/
theorem sliceH_embed {N M dN dM : ℕ} {sd : SliceData} (hN : sd.Nj ≤ N) (hM : sd.Mj ≤ M) (i j : ℕ) :
    sliceH (N + dN) (M + dM) sd i j =
      if dN ≤ i ∧ i ≤ dN + 2 * N ∧ dM ≤ j ∧ j ≤ dM + 2 * M then sliceH N M sd (i - dN) (j - dM)
      else 0 := by
  unfold sliceH
  split_ifs <;> first | rfl | (congr 2 <;> omega) | omega | (congr 1; omega)

/-- Grid polynomials depend only on the grid entries in the box. -/
theorem gridPolyNM_congr {N M : ℕ} {g g' : ℕ → ℕ → ℤ}
    (h : ∀ i j, i ≤ 2 * N → j ≤ 2 * M → g i j = g' i j) : gridPolyNM N M g = gridPolyNM N M g' :=
  sum_congr rfl fun i hi => sum_congr rfl fun j hj => by
    rw [h i j (by simp at hi; omega) (by simp at hj; omega)]

/-- **Embedding a stored coefficient**: in the layout `(N + dN, M + dM)` with symbol `2^s` it is
the embedded grid. -/
theorem sliceG_embed {N M dN dM : ℕ} {sd : SliceData} (hN : sd.Nj ≤ N) (hM : sd.Mj ≤ M) (sg : ℤ)
    (s : ℕ) :
    gridPolyNM (N + dN) (M + dM) (sliceG (N + dN) (M + dM) sg (2 ^ s) 0 0 sd) =
      gridPolyNM (N + dN) (M + dM) (embedGrid N M dN dM s (sliceG N M sg 1 0 0 sd)) := by
  refine gridPolyNM_congr fun i j hi hj => ?_
  simp only [sliceG, embedGrid, symGrid, zero_mul, add_zero, one_mul]
  rw [sliceH_embed hN hM, sliceH_embed hN hM]
  by_cases h : dN ≤ i ∧ i ≤ dN + 2 * N ∧ dM ≤ j ∧ j ≤ dM + 2 * M
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left (show dN ≤ 2 * (N + dN) - i ∧
      2 * (N + dN) - i ≤ dN + 2 * N ∧ dM ≤ 2 * (M + dM) - j ∧ 2 * (M + dM) - j ≤ dM + 2 * M by
        omega)]
    rw [show 2 * (N + dN) - i - dN = 2 * N - (i - dN) by omega,
      show 2 * (M + dM) - j - dM = 2 * M - (j - dM) by omega]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (show ¬ (dN ≤ 2 * (N + dN) - i ∧
      2 * (N + dN) - i ≤ dN + 2 * N ∧ dM ≤ 2 * (M + dM) - j ∧ 2 * (M + dM) - j ≤ dM + 2 * M) by
        omega)]
    ring

/-- **Embedded families have the same centre.** -/
theorem famCtr_embed (S N M p dN dM s : ℕ) (sg : ℤ) (c : ℂ) :
    ∀ (k : ℕ) (l : List SliceData), (∀ sd ∈ l, sd.Nj ≤ N ∧ sd.Mj ≤ M) →
      famCtr (S + s) (N + dN) (M + dM) p sg (2 ^ s) 0 0 c k l = famCtr S N M p sg 1 0 0 c k l
  | _, [], _ => rfl
  | k, sd :: rest, h => by
    rw [famCtr, famCtr, famCtr_embed S N M p dN dM s sg c (k + 1) rest
      fun sd' h' => h sd' (List.mem_cons_of_mem _ h'),
      sliceG_embed (h sd List.mem_cons_self).1 (h sd List.mem_cons_self).2, ctr_embedGrid]

/-! ## Light trees and complete steps -/

/-- The tree of `KronExpr` of a light tree. -/
def toEx : ExN → Ex
  | .var i => .var i
  | .cst k => .cst k
  | .add e f => .add (toEx e) (toEx f)
  | .sub e f => .sub (toEx e) (toEx f)
  | .mul e f => .mul (toEx e) (toEx f)

/-- The bridge `toEx` preserves weights. -/
theorem toEx_wt (W : ℕ → ℕ × ℕ × ℕ) : ∀ e : ExN, Ex.wt W (toEx e) = ExN.wt W e
  | .var _ => rfl
  | .cst _ => rfl
  | .add e f => by simp only [toEx, Ex.wt, ExN.wt, toEx_wt W e, toEx_wt W f]; rfl
  | .sub e f => by simp only [toEx, Ex.wt, ExN.wt, toEx_wt W e, toEx_wt W f]; rfl
  | .mul e f => by simp only [toEx, Ex.wt, ExN.wt, toEx_wt W e, toEx_wt W f]; rfl

/-- The bridge `toEx` preserves the signs of sums. -/
theorem toEx_sgn (W : ℕ → ℕ × ℕ × ℕ) (e f : ExN) : Ex.sgn W (toEx e) (toEx f) = ExN.sgn W e f := by
  simp only [Ex.sgn, ExN.sgn, toEx_wt]
  rcases ExN.wt W e with _ | ⟨a, b, p⟩ <;> rcases ExN.wt W f with _ | ⟨a', b', p'⟩ <;> rfl

/-- The bridge `toEx` preserves the phased evaluation. -/
theorem toEx_evH (W : ℕ → ℕ × ℕ × ℕ) (x : ℕ → ℤ) : ∀ e : ExN, Ex.evH W x (toEx e) = ExN.evH W x e
  | .var _ => rfl
  | .cst _ => rfl
  | .add e f => by simp only [toEx, Ex.evH, ExN.evH, toEx_evH W x e, toEx_evH W x f, toEx_sgn]; rfl
  | .sub e f => by simp only [toEx, Ex.evH, ExN.evH, toEx_evH W x e, toEx_evH W x f, toEx_sgn]; rfl
  | .mul e f => by simp only [toEx, Ex.evH, ExN.evH, toEx_evH W x e, toEx_evH W x f]

/-- The bridge `toEx` preserves degree boxes. -/
theorem toEx_box3 (Bx : ℕ → ℕ × ℕ × ℕ) : ∀ e : ExN, Ex.box3 Bx (toEx e) = ExN.box3 Bx e
  | .var _ => rfl
  | .cst _ => rfl
  | .add e f => by simp only [toEx, Ex.box3, ExN.box3, toEx_box3 Bx e, toEx_box3 Bx f]
  | .sub e f => by simp only [toEx, Ex.box3, ExN.box3, toEx_box3 Bx e, toEx_box3 Bx f]
  | .mul e f => by simp only [toEx, Ex.box3, ExN.box3, toEx_box3 Bx e, toEx_box3 Bx f]

/-- The bridge `toEx` preserves the `ℓ¹` majorant. -/
theorem toEx_majN (L : ℕ → ℕ) : ∀ e : ExN, Ex.majN L (toEx e) = ExN.majN L e
  | .var _ => rfl
  | .cst _ => rfl
  | .add e f => by simp only [toEx, Ex.majN, ExN.majN, toEx_majN L e, toEx_majN L f]
  | .sub e f => by simp only [toEx, Ex.majN, ExN.majN, toEx_majN L e, toEx_majN L f]
  | .mul e f => by simp only [toEx, Ex.majN, ExN.majN, toEx_majN L e, toEx_majN L f]

/-- The bridge `toEx` preserves the variable bound. -/
theorem toEx_below (n : ℕ) : ∀ e : ExN, below n (toEx e) = ExN.belowN n e
  | .var _ => rfl
  | .cst _ => rfl
  | .add e f => by simp only [toEx, below, ExN.belowN, toEx_below n e, toEx_below n f]
  | .sub e f => by simp only [toEx, below, ExN.belowN, toEx_below n e, toEx_below n f]
  | .mul e f => by simp only [toEx, below, ExN.belowN, toEx_below n e, toEx_below n f]

/-- `2^S` as a shift. -/
theorem two_pow_eq_shift (S : ℕ) : (2 : ℤ) ^ S = ((1 <<< S : ℕ) : ℤ) := by
  rw [Nat.shiftLeft_eq, one_mul]; push_cast; rfl

/-- **One rounding node of a family ball chain, from light kernel data.** -/
theorem node3_fullN {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M D : ℕ}
    {c : ℂ} (hc : ‖c‖ = 1) {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P3}
    {Bx : ℕ → ℕ × ℕ × ℕ} {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    {x X : ℕ → FA} (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : ExN) (dd de p : ℕ) (c' : ℤ) (A J K b W Kw dr L fuel Ki Kj Kb : ℕ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i)
    (hv : ExN.belowN n e = true) (hwt : ExN.wt Wt e = some (1 + dd, 0 + de, p))
    (hWn : Wt n = (1, 0, p)) (hc0 : c' ≠ 0)
    (hdims : nodeDims3N N M D Bx e dd de n A J K b W R Kw dr L fuel)
    (hl1 : nodeL1N S Lv e c' dd de n < 2 ^ (b - 1))
    (hK : node3KN S N M D Wt Kv e c' dd de n b W R Kw dr L fuel Ki Kj ≤ Kb)
    (hfin : nodeFin S B E (toEx e) Kb Ki Kj dd de ≤ |(c' : ℚ)| * E n)
    (hrel : (c' : ℂ) • X n = Ex.eval X (toEx e)) :
    Bd r (X n - x n) (E n) := by
  refine node3_full hr hq hc hW hPbox hPl1 hx hB hE (toEx e) dd de p c' A J K b W Kw dr L fuel
    Ki Kj Kb hPk (by rw [toEx_below]; exact hv) (by rw [toEx_wt]; exact hwt) hWn hc0 ?_ ?_ ?_ hfin
    hrel
  · unfold nodeDims3; unfold nodeDims3N at hdims; rw [toEx_box3]; exact hdims
  · unfold nodeL1; unfold nodeL1N at hl1; rw [toEx_majN]; exact hl1
  · unfold node3K; unfold node3KN at hK; rw [toEx_evH, two_pow_eq_shift]; exact hK

/-- **One norm node of a family ball chain, from light kernel data.** -/
theorem norm3_fullN {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M D : ℕ}
    {c : ℂ} (hc : ‖c‖ = 1) {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P3}
    {Bx : ℕ → ℕ × ℕ × ℕ} {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    {x X : ℕ → FA} (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : ExN) (w : ℕ × ℕ × ℕ) (A J K b W Kw dr L fuel Ki Kj Kb : ℕ) (Rq : ℚ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i)
    (hv : ExN.belowN n e = true) (hwt : ExN.wt Wt e = some w)
    (hdims : normDims3N Bx e A J K b W R Kw dr L fuel)
    (hl1 : ExN.majN Lv e < 2 ^ (b - 1))
    (hK : norm3KN Wt Kv N M e w b W R Kw dr L fuel Ki Kj ≤ Kb)
    (hfin : normFin S B E (toEx e) w Kb Ki Kj ≤ Rq) :
    Bd r (Ex.eval X (toEx e)) Rq := by
  refine norm3_full hr hq hc hW hPbox hPl1 hx hB hE (toEx e) w A J K b W Kw dr L fuel Ki Kj Kb
    Rq hPk (by rw [toEx_below]; exact hv) (by rw [toEx_wt]; exact hwt) ?_ ?_ ?_ hfin
  · unfold normDims3; unfold normDims3N at hdims; rw [toEx_box3]; exact hdims
  · rw [toEx_majN]; exact hl1
  · unfold norm3K; unfold norm3KN at hK; rw [toEx_evH]; exact hK

/-- **The norm of one family centre, from light kernel data.** -/
theorem center3_fullN {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M D : ℕ}
    {c : ℂ} (hc : ‖c‖ = 1) {Wt : ℕ → ℕ × ℕ × ℕ} {P : ℕ → P3}
    {Bx : ℕ → ℕ × ℕ × ℕ} {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    {x : ℕ → FA} (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) (i p b W Kw dr L fuel Ki Kj Kb : ℕ)
    (Bq : ℚ) (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i) (hWi : Wt i = (1, 0, p))
    (hdims : (Bx i).1 < W ∧ (Bx i).2.1 < R ∧ (Bx i).2.2 < Kw ∧ R * Kw ≤ 2 ^ dr ∧
      W ≤ fuel * L ∧ 1 ≤ b)
    (hl1 : Lv i < 2 ^ (b - 1)) (hK : center3KN Kv N M i b W R Kw dr L fuel Ki Kj ≤ Kb)
    (hfin : (Kb : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * 1 + 0) ≤ Bq) :
    Bd r (x i) Bq :=
  center3_full hq hc hPbox hPl1 hx i p b W Kw dr L fuel Ki Kj Kb Bq hPk hWi hdims hl1 hK hfin

end PlasmaLean.Certificates.KronBallCheb
