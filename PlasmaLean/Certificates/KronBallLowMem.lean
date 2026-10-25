/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallChebEnv
public import PlasmaLean.Certificates.KronLowMemCompute

/-!
# Soundness of the low-memory kernel quantities

The low-memory kernel quantities of `Certificates/KronLowMemCompute` equal the original ones:

* `SInt.toInt_add`, … : sign–magnitude arithmetic is integer arithmetic;
* `famS_toInt`: the signed image `famS` of a stored family is `famTB − famO` (hence its Kronecker
  image, `kron_famS`);
* `evS_toInt`: signed evaluation of trees is `ExN.evH`;
* `leafG_eq_rowBlk`: on a row whose digit sum is below `2^{b−1}`, the weighted block sums by
  multiplication (`leafG`, `leafVW_eq`) equal the loop `rowBlk` (product of digit expansions
  `dexp_mul_dexp`, masks `land_dexp`, `clsMask_eq`, extraction `dexp_shiftRight`, `dexp_mod`);
* `chebKV_eq`: hence `chebKV` equals `chebK` on Kronecker images of polynomials with `ℓ¹` norm below
  `2^{b−1}`;
* **`node3KN_le_of_S`, `norm3KN_le_of_S`, `center3KN_le_of_S`**: a low-memory kernel check proves
  the original check `node3KN … ≤ Kb` (`norm3KN`, `center3KN`) under the hypotheses of the family
  ball steps, so downstream chains are unchanged.

**Sanity.** `SInt.toInt_ofInt` (round trip), `famS_nil`, `rowBlk_closed` with zero fuel,
`leafG_fixture`, `gSel_reject` (in the light module).
-/

@[expose] public section

namespace PlasmaLean.Certificates.KronLowMem

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBallCheb PlasmaLean.Certificates.KronDigits

/-! ## Sign–magnitude arithmetic -/

namespace SInt

/-- `zero` is `0`. -/
@[simp] theorem toInt_zero : zero.toInt = 0 := by simp [zero, toInt]

/-- **Sanity**: `ofInt` is a right inverse of `toInt`. -/
@[simp] theorem toInt_ofInt (z : ℤ) : (ofInt z).toInt = z := by
  cases z with
  | ofNat n => simp [ofInt, toInt]
  | negSucc n => simp [ofInt, toInt, Int.negSucc_eq]

/-- Sums. -/
@[simp] theorem toInt_add (x y : SInt) : (add x y).toInt = x.toInt + y.toInt := by
  rcases x with ⟨_ | _, m⟩ <;> rcases y with ⟨_ | _, n⟩ <;> simp only [add, toInt] <;>
    split_ifs <;> simp_all <;> omega

/-- Negation. -/
@[simp] theorem toInt_neg (x : SInt) : (neg x).toInt = -x.toInt := by
  rcases x with ⟨_ | _, m⟩ <;> simp [neg, toInt]

/-- Differences. -/
@[simp] theorem toInt_sub (x y : SInt) : (sub x y).toInt = x.toInt - y.toInt := by
  rw [sub, toInt_add, toInt_neg, sub_eq_add_neg]

/-- Products. -/
@[simp] theorem toInt_mul (x y : SInt) : (mul x y).toInt = x.toInt * y.toInt := by
  rcases x with ⟨_ | _, m⟩ <;> rcases y with ⟨_ | _, n⟩ <;> simp [mul, toInt]

/-- Shifts. -/
@[simp] theorem toInt_shl (x : SInt) (k : ℕ) :
    (shl x k).toInt = x.toInt * ((1 <<< k : ℕ) : ℤ) := by
  rcases x with ⟨_ | _, m⟩ <;> by_cases hk : k = 0 <;> simp [shl, toInt, hk, Nat.shiftLeft_eq]

/-- Differences of natural numbers. -/
@[simp] theorem toInt_subNat (a b : ℕ) : (subNat a b).toInt = (a : ℤ) - b := by
  unfold subNat toInt; split_ifs <;> simp_all; omega

/-- Multiplication by a constant. -/
@[simp] theorem toInt_mulC (c : ℤ) (x : SInt) : (mulC c x).toInt = c * x.toInt := by
  unfold mulC; split_ifs with h <;> simp [h]

/-- The offset value. -/
theorem offNat_eq (x : SInt) (o : ℕ) : x.offNat o = (x.toInt + (o : ℤ)).toNat := by
  rcases x with ⟨_ | _, m⟩ <;> simp only [offNat, toInt] <;> simp <;> omega

end SInt

/-- **The signed divide and conquer is `bsplit`.** -/
theorem bsplitS_toInt (f : ℕ → SInt) (B : ℕ) :
    ∀ d s n, (bsplitS f B d s n).toInt = bsplit (fun t => (f t).toInt) B d s n
  | 0, s, n => by
    rw [bsplit_zero']
    change (if n = 0 then SInt.zero else f s).toInt = _
    split_ifs <;> simp
  | d + 1, s, n => by
    rw [bsplit_succ]
    change (if n ≤ 1 then (if n = 0 then SInt.zero else f s) else
      SInt.add (bsplitS f B d s (n / 2))
        (SInt.shl (bsplitS f B d (s + n / 2) (n - n / 2)) (B * (n / 2)))).toInt = _
    split_ifs
    · simp
    · rfl
    · rw [SInt.toInt_add, SInt.toInt_shl, bsplitS_toInt f B d, bsplitS_toInt f B d]

/-! ## Images of stored families -/

/-- The light rows are `rowNF`. -/
theorem rowNFL_eq : rowNFL = rowNF := rfl

/-- The light coefficient images are `sliceTF`. -/
theorem sliceTFL_eq : sliceTFL = sliceTF := rfl

/-- **Sanity**: the empty family has image `0`. -/
theorem famS_nil (b W R N M D c0 : ℕ) (odd : Bool) (kr dr dw : ℕ) :
    (famS b W R N M D c0 odd kr dr dw []).toInt = 0 := by
  rw [famS, SInt.toInt_shl, bsplitS_toInt]
  simp
  cases dw <;> simp [bsplit_zero', bsplit_succ]

/-- **The signed image of a stored family is `famTB − famO`** (spreading per row with `kr = dd`
levels). -/
theorem famS_toInt {N M D dd dr dw b W c0 : ℕ} {l : List SliceData}
    (hs : FamStatic N M D dd dr dw l) (hd : FamDyn b W c0 l) (odd : Bool) (R : ℕ) :
    (famS b W R N M D c0 odd dd dr dw l).toInt =
      ((famTB b W R N M D c0 odd dr dw l : ℕ) : ℤ) - ((famO b W R N M D dw l : ℕ) : ℤ) := by
  obtain ⟨hl, hD, hdw, hsl⟩ := hs
  obtain ⟨hb, hW, hdl⟩ := hd
  have hfast : ∀ sd ∈ l, SliceFast b W M dd dr c0 sd := fun sd h => by
    obtain ⟨⟨o1, o2, o3, o4, o5⟩, k1, k2⟩ := hsl sd h
    obtain ⟨d1, d2, d3⟩ := hdl sd h
    refine ⟨d1, o5, d3, o2, k1, k2, o3, o4, le_trans ?_ d2⟩
    calc c0 * 2 ^ (sd.Fj - 1) ≤ 2 * (c0 * 2 ^ (sd.Fj - 1)) :=
          Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 2 * c0 * 2 ^ (sd.Fj - 1) := by ring
  rw [famTB_eq b W R N M D c0 odd dd dr dw l hl hdw hfast,
    famT_sub_famO b W R N M D c0 odd dd dr dw l hl hD hdw,
    ← famPackB_eq b W R N M D c0 odd dd dr dw l hl hD hdw, famS, famPackB,
    SInt.toInt_shl, bsplitS_toInt, bsplit_eq _ _ dw 0 _ hdw, bsplit_eq _ _ dw 0 _ hdw]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  have hp' : lpos (l.length - 1) p < l.length := by
    have := mem_range.1 hp; unfold lpos; split_ifs <;> omega
  rw [zero_add, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hp',
    List.getD_eq_getElem?_getD]
  simp only [Option.map_some, Option.getD_some]
  have hlp : (if p ≤ l.length - 1 then l.length - 1 - p else p - (l.length - 1)) =
      lpos (l.length - 1) p := rfl
  rw [hlp, List.getElem?_eq_getElem hp', Option.getD_some]
  obtain ⟨h1, h2, _, _, _, _, h7, _, h9⟩ := hfast _ (List.getElem_mem hp')
  rw [sliceS, SInt.toInt_subNat, sliceTFL_eq, sliceTF_eq odd dd dd dr h1 h2 h7 h7 h9,
    slicePackN_eq_sub]

/-- **The Kronecker image of a stored family** is its signed image. -/
theorem kron_famS {N M D dd dr dw b W c0 : ℕ} {l : List SliceData}
    (hs : FamStatic N M D dd dr dw l) (hd : FamDyn b W c0 l) (odd : Bool) (R : ℕ) :
    kron b W (flat R (famPoly N M D (if odd then -1 else 1) (c0 : ℤ) 0 0 0 l)) =
      (famS b W R N M D c0 odd dd dr dw l).toInt := by
  rw [famS_toInt hs hd, kron_famTB hs hd]

/-! ## Expression trees -/

/-- The sign of a sum is `±1`. -/
theorem ExN.sgn_cases (W : ℕ → ℕ × ℕ × ℕ) (e f : ExN) : ExN.sgn W e f = 1 ∨ ExN.sgn W e f = -1 := by
  unfold ExN.sgn; split <;> [split_ifs <;> simp; simp]

/-- **Signed evaluation is `ExN.evH`.** -/
theorem evS_toInt (W : ℕ → ℕ × ℕ × ℕ) (x : ℕ → SInt) :
    ∀ e : ExN, (evS W x e).toInt = ExN.evH W (fun i => (x i).toInt) e
  | .var i => rfl
  | .cst k => by simp [evS, ExN.evH]
  | .add e f => by
    rcases ExN.sgn_cases W e f with h | h <;>
      simp [evS, ExN.evH, h, evS_toInt W x e, evS_toInt W x f, sub_eq_add_neg]
  | .sub e f => by
    rcases ExN.sgn_cases W e f with h | h <;>
      simp [evS, ExN.evH, h, evS_toInt W x e, evS_toInt W x f, sub_eq_add_neg]
  | .mul e f => by simp [evS, ExN.evH, evS_toInt W x e, evS_toInt W x f]


/-! ## Products of digit expansions -/

/-- The convolution of two digit sequences of lengths `n` and `m` at position `k`. -/
def cv (f g : ℕ → ℕ) (n m k : ℕ) : ℕ :=
  ∑ i ∈ range n, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0

/-- A window of a sum over a range. -/
theorem sum_window (h : ℕ → ℕ) {i₀ m N : ℕ} (hN : i₀ + m ≤ N) :
    ∑ i ∈ range N, (if i₀ ≤ i ∧ i < i₀ + m then h i else 0) = ∑ j ∈ range m, h (i₀ + j) := by
  rw [← sum_filter]
  have : (range N).filter (fun i => i₀ ≤ i ∧ i < i₀ + m) = (range m).map (addLeftEmbedding i₀) := by
    ext i
    simp only [mem_filter, mem_range, mem_map, addLeftEmbedding_apply]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨i - i₀, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [this, sum_map]
  rfl

/-- **Product of digit expansions**: the digits of the product are the convolution (no carries
are assumed). -/
theorem dexp_mul_dexp (B : ℕ) (f g : ℕ → ℕ) (n m : ℕ) :
    dexp B f n * dexp B g m = dexp B (cv f g n m) (n + m) := by
  unfold dexp cv
  rw [sum_mul_sum]
  simp only [sum_mul]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have h1 : ∀ k, (if i ≤ k ∧ k - i < m then f i * g (k - i) else 0) * 2 ^ (B * k) =
      if i ≤ k ∧ k < i + m then f i * g (k - i) * 2 ^ (B * k) else 0 := fun k => by
    by_cases h : i ≤ k ∧ k - i < m
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega), zero_mul]
  symm
  rw [Finset.sum_congr (s₁ := range (n + m)) rfl fun k _ => h1 k,
    sum_window _ (by omega : i + m ≤ n + m)]
  refine sum_congr rfl fun j _ => ?_
  rw [show i + j - i = j by omega, mul_add, pow_add]
  ring

/-- Convolution coefficients are bounded by the product of the digit sums. -/
theorem cv_le (f g : ℕ → ℕ) (n m k : ℕ) :
    cv f g n m k ≤ (∑ i ∈ range n, f i) * ∑ j ∈ range m, g j := by
  unfold cv
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  split_ifs with h
  · exact Nat.mul_le_mul_left _ (single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 h.2))
  · exact Nat.zero_le _

/-- Convolution with digits at most `1` is bounded by the digit sum. -/
theorem cv_le_of_le_one {f g : ℕ → ℕ} {n m : ℕ} (hg : ∀ j, g j ≤ 1) (k : ℕ) :
    cv f g n m k ≤ ∑ i ∈ range n, f i := by
  unfold cv
  refine sum_le_sum fun i _ => ?_
  split_ifs
  · calc f i * g (k - i) ≤ f i * 1 := Nat.mul_le_mul_left _ (hg _)
      _ = f i := mul_one _
  · exact Nat.zero_le _

/-- The window sums of length `L`: the convolution with `L` ones at the end of a block. -/
theorem cv_ones_block {a : ℕ → ℕ} {N L c : ℕ} (hL : 1 ≤ L) (hc : L * c + L ≤ N) :
    cv a (fun _ => 1) N L (L * c + L - 1) = ∑ t ∈ range L, a (L * c + t) := by
  unfold cv
  rw [← sum_window a hc]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : L * c ≤ i ∧ i < L * c + L
  · rw [ite_eq_left (by omega), ite_eq_left h, mul_one]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- An expansion with zero digits beyond `m` is the expansion of length `m`. -/
theorem dexp_zero_tail {b : ℕ} {e : ℕ → ℕ} {m n : ℕ} (h : ∀ k, m ≤ k → e k = 0) :
    dexp b e (m + n) = dexp b e m := by
  rw [dexp_add]
  have : dexp b (fun k => e (m + k)) n = 0 := by
    unfold dexp
    exact sum_eq_zero fun k _ => by
      change e (m + k) * _ = 0
      rw [h _ (by omega), zero_mul]
  rw [this, mul_zero, add_zero]

/-- An expansion by blocks of `L` digits with one nonzero digit, at the top of each block. -/
theorem dexp_top_digits (b L nB : ℕ) (hL : 1 ≤ L) (v : ℕ → ℕ) :
    dexp b (fun k => if k < L * nB ∧ k % L = L - 1 then v (k / L) else 0) (L * nB + L) =
      2 ^ (b * (L - 1)) * dexp (b * L) v nB := by
  rw [dexp_zero_tail fun k hk => ite_eq_right (by omega), dexp, sum_range_mul_eq, dexp, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  rw [sum_eq_single (L - 1)]
  · have hjL := Nat.mul_le_mul_left L (show j + 1 ≤ nB by omega)
    rw [mul_add, mul_one] at hjL
    rw [ite_eq_left ⟨by omega, by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]⟩,
      show (L - 1 + L * j) / L = j by
        rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]]
    rw [show b * (L - 1 + L * j) = b * (L - 1) + b * L * j by
      rw [mul_add, mul_assoc], pow_add]
    ring
  · intro i hi hne
    have hi' := mem_range.1 hi
    rw [ite_eq_right, zero_mul]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']
    omega
  · intro h; exact absurd (mem_range.2 (by omega)) h

/-- **The mask of the top digits of the blocks.** -/
theorem topMask_eq {b L nB : ℕ} (hb : 1 ≤ b) (hL : 1 ≤ L) :
    (((1 <<< b) - 1) * onesK (b * L) nB) <<< (b * (L - 1)) =
      dexp b (fun k => if k < L * nB ∧ k % L = L - 1 then 2 ^ b - 1 else 0) (L * nB + L) := by
  rw [dexp_top_digits b L nB hL (fun _ => 2 ^ b - 1), onesK_eq _ _ (by nlinarith),
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, mul_comm, dexp, dexp, mul_sum, mul_sum,
    mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- `∑_{t<n} f t` by `natSum`. -/
theorem natSum_eq (f : ℕ → ℕ) : ∀ n, natSum f n = ∑ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by rw [sum_range_succ, ← natSum_eq f n]; rfl

/-- **The weighted block sums by multiplication**: for digits with digit sum below `2^{b−1}` and
reversed block weights `cw` whose sum fits, `leafVW` is `∑_c cw(nB − 1 − c) × (block sum c)`. -/
theorem leafVW_eq {b L nB : ℕ} {cw a : ℕ → ℕ} (hb : 1 ≤ b) (hL : 1 ≤ L) (hnB : 1 ≤ nB)
    (hd : nB ≤ 2 ^ 8) (hs : ∑ t ∈ range (L * nB), a t < 2 ^ (b - 1))
    (hw : 2 ^ (b - 1) * ∑ c ∈ range nB, cw c ≤ 2 ^ (b * L)) :
    leafVW b L nB cw (dexp b a (L * nB)) = ∑ c ∈ range nB,
      cw (nB - 1 - c) * ∑ t ∈ range L, a (L * c + t) := by
  have hH : 2 ^ (b - 1) < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) (by omega)
  set w := cv a (fun _ => 1) (L * nB) L with hw_def
  have hwlt : ∀ k, w k < 2 ^ b := fun k =>
    ((cv_le_of_le_one (fun _ => le_refl 1) k).trans_lt hs).trans hH
  have h1 : dexp b a (L * nB) * onesK b L = dexp b w (L * nB + L) := by
    rw [onesK_eq b L hb, dexp_mul_dexp]
  have h2 : dexp b w (L * nB + L) &&& (((1 <<< b) - 1) * onesK (b * L) nB) <<< (b * (L - 1)) =
      2 ^ (b * (L - 1)) * dexp (b * L) (fun c => w (L * c + L - 1)) nB := by
    rw [topMask_eq hb hL, land_dexp (fun k _ => hwlt k) (fun k _ => by
      split_ifs <;> omega), ← dexp_top_digits b L nB hL]
    refine dexp_congr b _ fun k _ => ?_
    split_ifs with h
    · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hwlt k)]
      congr 1
      have := Nat.div_add_mod k L
      rw [h.2] at this
      rw [mul_comm] at this ⊢; omega
    · exact Nat.and_zero _
  set bs : ℕ → ℕ := fun c => w (L * c + L - 1) with hbs
  have hbs_eq : ∀ c, c < nB → bs c = ∑ t ∈ range L, a (L * c + t) := fun c hc =>
    cv_ones_block hL (by nlinarith)
  have hsum_bs : ∑ c ∈ range nB, bs c = ∑ t ∈ range (L * nB), a t := by
    rw [sum_range_mul_eq]
    refine sum_congr rfl fun c hc => ?_
    rw [hbs_eq c (mem_range.1 hc)]
    exact sum_congr rfl fun t _ => by rw [add_comm]
  have h3 : bsplitN cw (b * L) 8 0 nB = dexp (b * L) cw nB := by
    rw [bsplitN_eq _ _ 8 0 nB hd, dexp]
    simp only [zero_add]
  set u := cv bs cw nB nB with hu
  have hult : ∀ k, u k < 2 ^ (b * L) := fun k => by
    refine (cv_le _ _ _ _ k).trans_lt ?_
    rw [hsum_bs]
    rcases Nat.eq_zero_or_pos (∑ c ∈ range nB, cw c) with h0 | hpos
    · rw [h0, mul_zero]; positivity
    · calc (∑ t ∈ range (L * nB), a t) * ∑ c ∈ range nB, cw c
          < 2 ^ (b - 1) * ∑ c ∈ range nB, cw c := Nat.mul_lt_mul_of_pos_right hs hpos
        _ ≤ 2 ^ (b * L) := hw
  have h4 : dexp (b * L) bs nB * dexp (b * L) cw nB = dexp (b * L) u (nB + nB) :=
    dexp_mul_dexp _ _ _ _ _
  have h5 : (dexp (b * L) u (nB + nB) >>> (b * L * (nB - 1))) % (1 <<< (b * L)) = u (nB - 1) := by
    rw [show nB + nB = (nB - 1) + (1 + nB) by omega, dexp_shiftRight fun k _ => hult k,
      Nat.shiftLeft_eq, one_mul]
    have h6 := dexp_mod (b := b * L) (e := fun k => u (nB - 1 + k)) (m := 1) (n := nB)
      fun k _ => hult _
    rw [mul_one] at h6
    rw [h6]
    simp [dexp]
  rw [leafVW, h1, h2, Nat.shiftRight_eq_div_pow (2 ^ (b * (L - 1)) * _) (b * (L - 1)),
    Nat.mul_div_cancel_left _ (by positivity), h3]
  change ((dexp (b * L) bs nB * dexp (b * L) cw nB) >>> (b * L * (nB - 1))) %
    (1 <<< (b * L)) = _
  rw [h4, h5, hu, cv]
  refine sum_congr rfl fun c hc => ?_
  have hc' := mem_range.1 hc
  rw [ite_eq_left ⟨by omega, by omega⟩, hbs_eq c hc', mul_comm]

/-- A sum over a range cut at `len ≤ L`. -/
theorem sum_range_ite_lt (h : ℕ → ℕ) {len L : ℕ} (hle : len ≤ L) :
    ∑ t ∈ range L, (if t < len then h t else 0) = ∑ t ∈ range len, h t := by
  have := sum_window h (i₀ := 0) (m := len) (N := L) (by omega)
  simp only [zero_add, Nat.zero_le, true_and] at this
  exact this

/-- **`rowBlk` in closed form**: for digits with digit sum below `2^b − 1` and enough fuel, the
weighted block sums `∑_c max(wA(i + Lc), wA(i + min(Lc + L, len) − 1)) × (block sum c)`. -/
theorem rowBlk_closed {b L : ℕ} {wA : ℕ → ℕ} (hL : 1 ≤ L) :
    ∀ (f i len : ℕ) (a : ℕ → ℕ), (∀ t, t < len → a t < 2 ^ b) →
      ∑ t ∈ range len, a t < 2 ^ b - 1 → len ≤ f * L →
      rowBlk b L wA f i len (dexp b a len) = ∑ c ∈ range ((len + L - 1) / L),
        max (wA (i + L * c)) (wA (i + min (L * c + L) len - 1)) *
          ∑ t ∈ range L, (if L * c + t < len then a (L * c + t) else 0) := by
  have hpred : (1 <<< b) - 1 = 2 ^ b - 1 := by rw [Nat.shiftLeft_eq, one_mul]
  intro f
  induction f with
  | zero =>
    intro i len a _ _ hlen
    have : len = 0 := by simpa using hlen
    subst this
    rw [rowBlk_zero, Nat.div_eq_of_lt (by omega)]
    simp
  | succ f ih =>
    intro i len a ha hs hlen
    rw [rowBlk_succ, hpred]
    split_ifs with hle
    · rw [dexp_mod_pred_eq hs]
      rcases Nat.eq_zero_or_pos len with h0 | hpos
      · subst h0; simp
      · rw [show (len + L - 1) / L = 1 by
          rw [Nat.div_eq_iff (by omega)]; constructor <;> omega, sum_range_one]
        simp only [mul_zero, add_zero, zero_add]
        rw [show min L len = len by omega, mul_comm, sum_range_ite_lt _ hle]
    · obtain ⟨m, rfl⟩ : ∃ m, len = L + m := ⟨len - L, by omega⟩
      have h1 : dexp b a (L + m) % (1 <<< (b * L)) = dexp b a L := by
        rw [Nat.shiftLeft_eq, one_mul, dexp_mod ha]
      have h2 : dexp b a (L + m) >>> (b * L) = dexp b (fun t => a (L + t)) m :=
        dexp_shiftRight ha
      rw [sum_range_add] at hs
      have hs1 : ∑ t ∈ range L, a t < 2 ^ b - 1 := by omega
      have hs2 : ∑ t ∈ range m, a (L + t) < 2 ^ b - 1 := by omega
      rw [h1, h2, dexp_mod_pred_eq hs1, show L + m - L = m by omega,
        ih (i + L) m (fun t => a (L + t)) (fun t ht => ha _ (by omega)) hs2
          (by rw [Nat.succ_mul] at hlen; omega),
        show (L + m + L - 1) / L = (m + L - 1) / L + 1 by
          rw [show L + m + L - 1 = (m + L - 1) + L * 1 by omega, Nat.add_mul_div_left _ _ hL],
        sum_range_succ', add_comm]
      congr 1
      · refine sum_congr rfl fun c _ => ?_
        rw [show i + L + L * c = i + L * (c + 1) by ring,
          show i + L + min (L * c + L) m - 1 = i + min (L * (c + 1) + L) (L + m) - 1 by
            rw [mul_add, mul_one]; omega]
        congr 1
        refine sum_congr rfl fun t _ => ?_
        rw [show L * (c + 1) + t = L + (L * c + t) by ring]
        by_cases h : L * c + t < m
        · rw [ite_eq_left h, ite_eq_left (by omega)]
        · rw [ite_eq_right h, ite_eq_right (by omega)]
      · simp only [mul_zero, add_zero, zero_add]
        rw [show min L (L + m) = L by omega, mul_comm]
        congr 1
        exact sum_congr rfl fun t ht => by rw [ite_eq_left (by have := mem_range.1 ht; omega)]

/-- A nonzero class count satisfies `okG`. -/
theorem gSel_ok {b W L : ℕ} {wA : ℕ → ℕ} (h : gSel b W L wA ≠ 0) :
    okG b W L (gSel b W L wA) wA := by
  unfold gSel at *
  split_ifs at * with h1 h2 h3 <;> simp_all

/-- The expansion with all digits `2^b − 1`. -/
theorem dexp_pred (b L : ℕ) : dexp b (fun _ => 2 ^ b - 1) L = 2 ^ (b * L) - 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [dexp_succ, ih, mul_add, mul_one, pow_add]
    have h1 := Nat.one_le_two_pow (n := b * L)
    have h2 := Nat.one_le_two_pow (n := b)
    rw [Nat.sub_mul, one_mul]
    have : 2 ^ b * 2 ^ (b * L) = 2 ^ (b * L) * 2 ^ b := mul_comm _ _
    rw [this]
    have h3 : 2 ^ (b * L) ≤ 2 ^ (b * L) * 2 ^ b := Nat.le_mul_of_pos_right _ (by positivity)
    omega

/-- Quotients as windows. -/
theorem div_eq_iff_window {u L r : ℕ} (hL : 1 ≤ L) : u / L = r ↔ L * r ≤ u ∧ u < L * r + L := by
  rw [show (u / L = r) ↔ (r ≤ u / L ∧ u / L < r + 1) by omega, Nat.le_div_iff_mul_le (by omega),
    Nat.div_lt_iff_lt_mul (by omega), mul_comm r L, add_mul, one_mul, mul_comm r L]

/-- The class of a digit inside a superblock. -/
theorem cls_cond {L g r c u : ℕ} (hL : 1 ≤ L) (hu : u < g * L) :
    ((u + g * L * c) / L) % g = r ↔ L * r ≤ u ∧ u < L * r + L := by
  have e1 : (u + g * L * c) / L = u / L + g * c := by
    rw [show g * L * c = L * (g * c) by ring, Nat.add_mul_div_left _ _ (by omega)]
  have e2 : u / L < g := (Nat.div_lt_iff_lt_mul (by omega)).2 hu
  rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e2, div_eq_iff_window hL]

/-- **The mask of a class of blocks** as a digit expansion. -/
theorem clsMask_eq {b L g nB r : ℕ} (hb : 1 ≤ b) (hL : 1 ≤ L) (hr : r < g) :
    clsMask b L g nB r =
      dexp b (fun t => if (t / L) % g = r then 2 ^ b - 1 else 0) (g * L * nB) := by
  have hg : 1 ≤ g := by omega
  rw [clsMask, onesK_eq _ _ (Nat.one_le_iff_ne_zero.2 (by positivity)), dexp, dexp,
    sum_range_mul_eq, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  have hcond : ∀ u, u < g * L → ((((u + g * L * c) / L) % g = r) ↔ L * r ≤ u ∧ u < L * r + L) :=
    fun u hu => cls_cond hL hu
  rw [← Finset.sum_congr (s₁ := range (g * L)) rfl fun u hu => (show
      (if L * r ≤ u ∧ u < L * r + L then (2 ^ b - 1) * 2 ^ (b * (u + g * L * c)) else 0) =
        (if ((u + g * L * c) / L) % g = r then 2 ^ b - 1 else 0) * 2 ^ (b * (u + g * L * c)) by
      by_cases h : L * r ≤ u ∧ u < L * r + L
      · rw [ite_eq_left h, ite_eq_left ((hcond u (mem_range.1 hu)).2 h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hcond u (mem_range.1 hu)).1 h')),
          zero_mul]),
    sum_window _ (by nlinarith : L * r + L ≤ g * L)]
  have := dexp_pred b L
  unfold dexp at this
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, ← this, sum_mul, sum_mul]
  refine sum_congr rfl fun s _ => ?_
  rw [one_mul, show b * (L * r + s + g * L * c) = b * s + b * (L * r) + b * (g * L) * c by ring,
    pow_add, pow_add, pow_mul]
  ring

/-- **The weighted block sums by classes are `rowBlk`** on a row of `W ≥ 1` digits whose digit sum
is below `2^{b−1}`, when `okG` holds and the fuel suffices. -/
theorem leafG_eq_rowBlk {b W L g fuel : ℕ} {wA a : ℕ → ℕ} (hok : okG b W L g wA = true)
    (hW : 1 ≤ W) (hfuel : W ≤ fuel * L) (hs : ∑ t ∈ range W, a t < 2 ^ (b - 1)) :
    leafG b W L g wA (dexp b a W) = rowBlk b L wA fuel 0 W (dexp b a W) := by
  simp only [okG, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    natSum_eq] at hok
  obtain ⟨⟨hL, hb, hg, hd⟩, hw⟩ := hok
  have hH : 2 ^ (b - 1) ≤ 2 ^ b - 1 := by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ']; congr 1; omega
    have := Nat.one_le_two_pow (n := b - 1); omega
  -- the closed form of `rowBlk`
  rw [rowBlk_closed hL fuel 0 W a (fun t ht => (single_le_sum (fun _ _ => Nat.zero_le _)
    (mem_range.2 ht)).trans_lt (hs.trans_le (hH.trans (Nat.sub_le _ _)))) (hs.trans_le hH) hfuel]
  have hdm1 := Nat.div_add_mod (W + L - 1) L
  have hml1 := Nat.mod_lt (W + L - 1) (show 0 < L by omega)
  generalize hnB1 : (W + L - 1) / L = n1 at hdm1
  generalize (W + L - 1) % L = r1 at hdm1 hml1
  have hW1 : W ≤ L * n1 := by omega
  have hW1' : L * n1 < W + L := by omega
  have hdm := Nat.div_add_mod (W + g * L - 1) (g * L)
  have hml := Nat.mod_lt (W + g * L - 1) (show 0 < g * L by positivity)
  have hnB : 1 ≤ (W + g * L - 1) / (g * L) :=
    Nat.le_div_iff_mul_le (by positivity) |>.2 (by rw [one_mul]; omega)
  unfold leafG
  generalize (W + g * L - 1) / (g * L) = nB at hd hw hdm hnB ⊢
  generalize (W + g * L - 1) % (g * L) = rr at hdm hml
  have hWn : W ≤ g * L * nB := by omega
  have hn1 : n1 ≤ g * nB := by
    by_contra h
    have : L * (g * nB) + L ≤ L * n1 := by nlinarith
    nlinarith
  set a' : ℕ → ℕ := fun t => if t < W then a t else 0 with ha'
  have hx : dexp b a W = dexp b a' (g * L * nB) := by
    rw [show g * L * nB = W + (g * L * nB - W) by omega, dexp_zero_tail fun k hk => by
      simp only [ha']; rw [ite_eq_right (by omega)]]
    exact dexp_congr b W fun k hk => by simp only [ha']; rw [ite_eq_left hk]
  have ha'lt : ∀ t, a' t < 2 ^ b := fun t => by
    simp only [ha']; split_ifs with h
    · exact (single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 h)).trans_lt
        (hs.trans_le (hH.trans (Nat.sub_le _ _)))
    · positivity
  have hsum' : ∑ t ∈ range (g * L * nB), a' t = ∑ t ∈ range W, a t := by
    rw [show g * L * nB = W + (g * L * nB - W) by omega, sum_range_add]
    have hz : ∑ x ∈ range (g * L * nB - W), a' (W + x) = 0 :=
      sum_eq_zero fun k _ => by simp only [ha']; rw [ite_eq_right (by omega)]
    rw [hz, add_zero]
    exact sum_congr rfl fun k hk => by simp only [ha']; rw [ite_eq_left (mem_range.1 hk)]
  -- each class
  set F : ℕ → ℕ := fun k => max (wA (L * k)) (wA (min (L * k + L) W - 1)) *
    ∑ s ∈ range L, a' (L * k + s) with hF
  have hclass : ∀ r, r < g → leafVW b (g * L) nB (blkG W L g nB r wA)
      (dexp b a' (g * L * nB) &&& clsMask b L g nB r) = ∑ c ∈ range nB, F (g * c + r) := by
    intro r hr
    rw [clsMask_eq hb hL hr, land_dexp (fun t _ => ha'lt t) (fun t _ => by split_ifs <;> omega)]
    have hcl : dexp b (fun t => a' t &&& if t / L % g = r then 2 ^ b - 1 else 0) (g * L * nB) =
        dexp b (fun t => if t / L % g = r then a' t else 0) (g * L * nB) :=
      dexp_congr b _ fun t _ => by
        split_ifs
        · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (ha'lt t)]
        · exact Nat.and_zero _
    rw [hcl, leafVW_eq hb (by nlinarith) hnB hd ?_ (hw r hr)]
    · refine sum_congr rfl fun c hc => ?_
      have hc' := mem_range.1 hc
      simp only [hF, blkG, show nB - 1 - (nB - 1 - c) = c by omega]
      congr 1
      calc ∑ t ∈ range (g * L), (if (g * L * c + t) / L % g = r then a' (g * L * c + t) else 0)
          = ∑ t ∈ range (g * L), (if L * r ≤ t ∧ t < L * r + L then a' (g * L * c + t) else 0) :=
            sum_congr rfl fun t ht => by
              have ht' := mem_range.1 ht
              rw [add_comm (g * L * c) t]
              by_cases h : L * r ≤ t ∧ t < L * r + L
              · rw [ite_eq_left ((cls_cond hL ht').2 h), ite_eq_left h]
              · rw [ite_eq_right (fun h' => h ((cls_cond hL ht').1 h')), ite_eq_right h]
        _ = ∑ j ∈ range L, a' (g * L * c + (L * r + j)) :=
            sum_window (fun t => a' (g * L * c + t)) (show L * r + L ≤ g * L by nlinarith)
        _ = _ := sum_congr rfl fun j _ => by ring_nf
    · calc ∑ t ∈ range (g * L * nB), (if t / L % g = r then a' t else 0)
          ≤ ∑ t ∈ range (g * L * nB), a' t := sum_le_sum fun t _ => by split_ifs <;> omega
        _ < 2 ^ (b - 1) := by rw [hsum']; exact hs
  rw [hx, natSum_eq, sum_congr rfl fun r hr => hclass r (mem_range.1 hr), sum_comm]
  have hreg : ∑ c ∈ range nB, ∑ r ∈ range g, F (g * c + r) = ∑ k ∈ range (g * nB), F k := by
    rw [sum_range_mul_eq]
    exact sum_congr rfl fun c _ => sum_congr rfl fun r _ => by rw [add_comm]
  rw [hreg, show g * nB = n1 + (g * nB - n1) by omega, sum_range_add]
  have hz : ∑ k ∈ range (g * nB - n1), F (n1 + k) = 0 := sum_eq_zero fun k _ => by
    simp only [hF]
    rw [sum_eq_zero fun s _ => by simp only [ha']; rw [ite_eq_right (by nlinarith)], mul_zero]
  rw [hz, add_zero]
  refine sum_congr rfl fun k _ => ?_
  simp only [hF, ha', zero_add]

/-! ## The kernel quantity -/

/-- **The low-memory kernel quantity is `chebK`** on the Kronecker image of a polynomial with
`ℓ¹` norm below `2^{b−1}` (the hypotheses of `sum_le_chebK`). -/
theorem chebKV_eq {P : P2} {a J' b W R Kw dr L fuel i₀ j₀ Ki Kj : ℕ} {Nv : SInt} (hb : 1 ≤ b)
    (hbox : InBox P a J') (ha : a < W) (hJ' : J' + 1 ≤ R * Kw) (hdr : R * Kw ≤ 2 ^ dr)
    (hfuel : W ≤ fuel * L) (hl1 : l1 P < 2 ^ (b - 1)) (hk : kron b W P = Nv.toInt) :
    chebKV b W R Kw dr L fuel i₀ j₀ Ki Kj Nv = chebK b W R Kw dr L fuel i₀ j₀ Ki Kj Nv.toInt := by
  set H := 2 ^ (b - 1) with hH
  have hbH : 2 ^ b = 2 * H := by rw [hH, ← pow_succ']; congr 1; omega
  set Ntot := W * (R * Kw) with hNtot
  have hS : W * (J' + 1) ≤ Ntot := Nat.mul_le_mul_left _ hJ'
  have hsl : ∀ n, (slot P W n).natAbs < H := fun n =>
    (natAbs_coeff_le_l1 P _ _).trans_lt hl1
  set e : ℕ → ℕ := fun n => (slot P W n + H).toNat with he_def
  have he_int : ∀ n, ((e n : ℕ) : ℤ) = slot P W n + H := fun n => by
    have := hsl n
    simp only [he_def]
    rw [Int.toNat_of_nonneg (by omega)]
  have hbHz : (2 : ℤ) ^ b = 2 * (H : ℤ) := by exact_mod_cast hbH
  have he_lt : ∀ n, e n < 2 ^ b := fun n => by
    have h1 := he_int n; have h2 := hsl n
    have : ((e n : ℕ) : ℤ) < 2 ^ b := by rw [h1, hbHz]; omega
    exact_mod_cast this
  have hT : (Nv.toInt + ((H * onesK b Ntot : ℕ) : ℤ)).toNat = dexp b e Ntot := by
    rw [← hk, kron_eq_sum b hbox ha hS, onesK_eq b Ntot hb, mul_dexp]
    have : (∑ n ∈ range Ntot, slot P W n * ((2 : ℤ) ^ b) ^ n) +
        ((dexp b (fun _ => H * 1) Ntot : ℕ) : ℤ) = ((dexp b e Ntot : ℕ) : ℤ) := by
      simp only [dexp]
      push_cast
      rw [← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [he_int n, ← pow_mul]; ring
    rw [this, Int.toNat_natCast]
  have hA : absDig b Ntot (dexp b e Ntot) = dexp b (fun n => (slot P W n).natAbs) Ntot := by
    rw [absDig_dexp hb fun n _ => he_lt n]
    refine dexp_congr b Ntot fun n _ => ?_
    have h1 := he_int n
    omega
  set row : ℕ → ℕ := fun j => if j < R * Kw then
    dexp b (fun i => (slot P W (i + W * j)).natAbs) W else 0 with hrow
  have hrow_lt : ∀ j, row j < 2 ^ (b * W) := fun j => by
    simp only [hrow]; split_ifs
    · exact dexp_lt fun i _ => (hsl _).trans (by rw [hbH]; omega)
    · positivity
  have hrows : dexp b (fun n => (slot P W n).natAbs) Ntot =
      ∑ n ∈ range (2 ^ dr), row (0 + n) * (2 ^ (b * W)) ^ n := by
    rw [hNtot, dexp_rows]
    rw [← sum_subset (range_subset_range.2 hdr) fun n _ hn => by
      have : ¬ n < R * Kw := by simpa using hn
      simp [hrow, this]]
    refine sum_congr rfl fun n hn => ?_
    have : n < R * Kw := mem_range.1 hn
    simp [hrow, this]
  rw [chebKV, chebK, SInt.offNat_eq, pdigL_eq, ← hH, hT, hA, hrows,
    pdig_spec (b * W) _ row hrow_lt dr 0 (R * Kw), pdig_spec (b * W) _ row hrow_lt dr 0 (R * Kw)]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < R * Kw := (mem_range.1 hj).trans_le (min_le_left _ _)
  simp only [zero_add, hrow, hj', ↓reduceIte]
  congr 1
  split_ifs with hok
  · rfl
  · refine leafG_eq_rowBlk (gSel_ok hok) (by omega) hfuel ?_
    calc ∑ t ∈ range W, (slot P W (t + W * j)).natAbs ≤ l1 P := by
          rw [l1_eq_sum hbox ha hS, hNtot, sum_range_mul_eq]
          exact single_le_sum (f := fun j => ∑ t ∈ range W, (slot P W (t + W * j)).natAbs)
            (fun _ _ => Nat.zero_le _) (mem_range.2 hj')
      _ < 2 ^ (b - 1) := hl1

/-! ## The low-memory checks prove the original checks -/

/-- The signed node value is the integer node value of `node3KN`. -/
theorem node3_val (S N M D : ℕ) (Wt : ℕ → ℕ × ℕ × ℕ) {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    {KvS : ℕ → ℕ → ℕ → ℕ → SInt} (e : ExN) (c' : ℤ) (dd de n b W R : ℕ)
    (hKv : ∀ i, (KvS b W R i).toInt = Kv b W R i) :
    (SInt.sub (evS Wt (KvS b W R) e) (SInt.mulC c' (SInt.shl (KvS b W R n)
        (dd * (S + b * (N + W * (M + R * D))) + de * (1 + b * W))))).toInt =
      ExN.evH Wt (Kv b W R) e - c' * ((((1 <<< S : ℕ) : ℤ) *
        ((1 <<< (b * (N + W * (M + R * D)))) : ℕ)) ^ dd * (2 * ((1 <<< (b * W)) : ℕ)) ^ de) *
          Kv b W R n := by
  rw [SInt.toInt_sub, evS_toInt, SInt.toInt_mulC, SInt.toInt_shl, hKv]
  simp only [hKv, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_add, pow_mul, pow_mul, pow_add, pow_add, mul_pow, mul_pow, pow_one]
  ring

/-- **A low-memory node check proves the original node check** (`node3KN`), under the hypotheses
of `node3_fullN`. -/
theorem node3KN_le_of_S {S N M D : ℕ} {Wt : ℕ → ℕ × ℕ × ℕ} {P : ℕ → P3} {Bx : ℕ → ℕ × ℕ × ℕ}
    {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ} {KvS : ℕ → ℕ → ℕ → ℕ → SInt}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    (e : ExN) (dd de n : ℕ) (c' : ℤ) (A J K b W Kw dr L fuel Ki Kj Kb : ℕ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i)
    (hKv : ∀ i, (KvS b W R i).toInt = Kv b W R i)
    (hdims : nodeDims3N N M D Bx e dd de n A J K b W R Kw dr L fuel)
    (hl1 : nodeL1N S Lv e c' dd de n < 2 ^ (b - 1))
    (hK : node3KS S N M D Wt KvS e c' dd de n b W R Kw dr L fuel Ki Kj ≤ Kb) :
    node3KN S N M D Wt Kv e c' dd de n b W R Kw dr L fuel Ki Kj ≤ Kb := by
  obtain ⟨hA, hJ, hK', hA', hJ', hK'', hAW, hJR, hKw, hdr, hfuel, hb⟩ := hdims
  obtain ⟨fb, fl, fk⟩ := node3_facts (S := S) (N := N) (M := M) (D := D) (Wt := Wt) hPbox hPl1
    (toEx e) c' n dd de A J K b W hPk (by rw [toEx_box3]; exact hA) (by rw [toEx_box3]; exact hJ)
    (by rw [toEx_box3]; exact hK') hA' hJ' hK''
  unfold node3KS at hK
  unfold node3KN
  rw [chebKV_eq hb (inBox_flat fb) hAW (by
      have : R * K + R ≤ R * Kw := by nlinarith
      omega) hdr hfuel (fl.trans_lt (by unfold nodeL1N at hl1; rw [toEx_majN]; exact hl1))
      (by rw [fk, node3_val S N M D Wt e c' dd de n b W R hKv, toEx_evH, two_pow_eq_shift]),
    node3_val S N M D Wt e c' dd de n b W R hKv] at hK
  exact hK

/-- **A low-memory norm check proves the original norm check** (`norm3KN`). -/
theorem norm3KN_le_of_S {Wt : ℕ → ℕ × ℕ × ℕ} {P : ℕ → P3} {Bx : ℕ → ℕ × ℕ × ℕ}
    {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ} {KvS : ℕ → ℕ → ℕ → ℕ → SInt} {N M : ℕ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    (e : ExN) (w : ℕ × ℕ × ℕ) (A J K b W Kw dr L fuel Ki Kj Kb : ℕ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i)
    (hKv : ∀ i, (KvS b W R i).toInt = Kv b W R i)
    (hdims : normDims3N Bx e A J K b W R Kw dr L fuel)
    (hl1 : ExN.majN Lv e < 2 ^ (b - 1))
    (hK : norm3KS Wt KvS N M e w b W R Kw dr L fuel Ki Kj ≤ Kb) :
    norm3KN Wt Kv N M e w b W R Kw dr L fuel Ki Kj ≤ Kb := by
  obtain ⟨hA, hJ, hK', hAW, hJR, hKw, hdr, hfuel, hb⟩ := hdims
  rw [← toEx_box3] at hA hJ hK'
  have fb := (inBox3_evH Wt hPbox (toEx e)).mono hA hJ hK'
  have hev : flat R (Ex.evH Wt P (toEx e)) = Ex.evH Wt (fun i => flat R (P i)) (toEx e) :=
    Ex.evH_map _ Wt P (toEx e)
  have fl : l1 (flat R (Ex.evH Wt P (toEx e))) ≤ Ex.majN Lv (toEx e) := by
    rw [hev]; exact Ex.l1_evH Wt hPl1 (toEx e)
  have fk : kron b W (flat R (Ex.evH Wt P (toEx e))) = Ex.evH Wt (Kv b W R) (toEx e) := by
    rw [hev, Ex.evH_map]; exact congrArg (fun y => Ex.evH Wt y (toEx e)) (funext fun i => hPk i)
  have hval : (evS Wt (KvS b W R) e).toInt = ExN.evH Wt (Kv b W R) e := by
    rw [evS_toInt]; simp only [hKv]
  unfold norm3KS at hK
  unfold norm3KN
  rw [chebKV_eq hb (inBox_flat fb) hAW (by
      have : R * K + R ≤ R * Kw := by nlinarith
      omega) hdr hfuel (fl.trans_lt (by rw [toEx_majN]; exact hl1))
      (by rw [fk, hval, toEx_evH]), hval] at hK
  exact hK

/-- **A low-memory centre check proves the original centre check** (`center3KN`). -/
theorem center3KN_le_of_S {P : ℕ → P3} {Bx : ℕ → ℕ × ℕ × ℕ} {R : ℕ} {Lv : ℕ → ℕ}
    {Kv : ℕ → ℕ → ℕ → ℕ → ℤ} {KvS : ℕ → ℕ → ℕ → ℕ → SInt} {N M : ℕ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i) (i b W Kw dr L fuel Ki Kj Kb : ℕ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i)
    (hKv : ∀ i, (KvS b W R i).toInt = Kv b W R i)
    (hdims : (Bx i).1 < W ∧ (Bx i).2.1 < R ∧ (Bx i).2.2 < Kw ∧ R * Kw ≤ 2 ^ dr ∧
      W ≤ fuel * L ∧ 1 ≤ b)
    (hl1 : Lv i < 2 ^ (b - 1)) (hK : center3KS KvS N M i b W R Kw dr L fuel Ki Kj ≤ Kb) :
    center3KN Kv N M i b W R Kw dr L fuel Ki Kj ≤ Kb := by
  obtain ⟨hAW, hJR, hKw, hdr, hfuel, hb⟩ := hdims
  unfold center3KS at hK
  unfold center3KN
  rw [chebKV_eq hb (inBox_flat (hPbox i)) hAW (by
      have : R * (Bx i).2.2 + R ≤ R * Kw := by nlinarith
      omega) hdr hfuel ((hPl1 i).trans_lt hl1) (by rw [hPk, hKv]), hKv] at hK
  exact hK

end PlasmaLean.Certificates.KronLowMem
