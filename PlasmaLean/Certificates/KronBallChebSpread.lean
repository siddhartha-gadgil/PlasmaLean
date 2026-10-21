/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallChebDigits

/-!
# Spreading and reversing digit expansions with masks

Kernel-cheap transformations of digit expansions (`KronDigits.dexp`) by `O(log n)` big-integer
operations (`Nat.land`, shifts, additions):

* **spreading** `spread F b k`: `∑_{t < 2^k} f_t 2^{Ft} ↦ ∑_{t < 2^k} f_t 2^{bt}` (`F ≤ b`,
  `f_t < 2^F`), level by level: at level `ℓ` the blocks of `2^{ℓ+1}` fields are split into halves
  and
  the upper halves move up (`spreadStep_dexp`);
* **reversing** `rev b k`: `∑_{t < 2^k} f_t 2^{bt} ↦ ∑_{t < 2^k} f_{2^k − 1 − t} 2^{bt}`
  (`f_t < 2^b`), by swapping the halves of the blocks at every level (`revStep_dexp`).

Both are proved through block expansions: an expansion in base `2^{F 2^{ℓ+1}}`-blocks spaced by
`2^{b 2^{ℓ+1}}` (`dexp (b 2^{ℓ+1}) B`), whose digits split into two halves (`dexp_add`).

**Sanity.** `spread_fixture`, `rev_fixture`.
-/

@[expose] public section

namespace PlasmaLean.Certificates.KronDigits

open Finset

/-! ## Block decompositions -/

/-- The block `β` of `2^ℓ` fields of `f` (width `F`). -/
def blk (F ℓ : ℕ) (f : ℕ → ℕ) (β : ℕ) : ℕ := dexp F (fun s => f (β * 2 ^ ℓ + s)) (2 ^ ℓ)

/-- Blocks of fields are below their width. -/
theorem blk_lt {F ℓ : ℕ} {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ F) (β : ℕ) :
    blk F ℓ f β < 2 ^ (F * 2 ^ ℓ) :=
  dexp_lt fun _ _ => hf _

/-- A block of `2^{ℓ+1}` fields is its lower half plus its upper half shifted. -/
theorem blk_succ (F ℓ : ℕ) (f : ℕ → ℕ) (β : ℕ) :
    blk F (ℓ + 1) f β = blk F ℓ f (2 * β) + 2 ^ (F * 2 ^ ℓ) * blk F ℓ f (2 * β + 1) := by
  unfold blk
  rw [pow_succ, mul_two, dexp_add]
  congr 1
  · exact dexp_congr F _ fun s _ => by congr 1; ring
  · congr 1
    exact dexp_congr F _ fun s _ => by congr 1; ring

/-- Interleaving: an expansion of pairs is an expansion of twice as many digits. -/
theorem dexp_pairs (c : ℕ) (g : ℕ → ℕ) (n : ℕ) :
    dexp (2 * c) (fun β => g (2 * β) + 2 ^ c * g (2 * β + 1)) n = dexp c g (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [dexp_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, dexp_succ, dexp_succ,
      show c * (2 * n) = 2 * c * n by ring, show c * (2 * n + 1) = c + 2 * c * n by ring, pow_add]
    ring

/-! ## Spreading -/

/-- `land` with a digit mask `2^c − 1` keeps the low `c` bits. -/
theorem land_low {c x y : ℕ} (hy : y < 2 ^ c) : (y + 2 ^ c * x) &&& (2 ^ c - 1) = y := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]

/-- `land` with a shifted digit mask keeps the high part. -/
theorem land_high {c d x y : ℕ} (hy : y < 2 ^ c) (hx : x < 2 ^ d) :
    (y + 2 ^ c * x) &&& ((2 ^ d - 1) <<< c) = 2 ^ c * x := by
  have h1 : (2 ^ d - 1) <<< c = 2 ^ c * (2 ^ d - 1) + 0 := by rw [Nat.shiftLeft_eq]; ring
  rw [h1, add_comm y, land_two_pow_mul_add hy (by positivity), Nat.and_zero, add_zero,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

/-- **One spreading level on a block expansion.** -/
theorem spreadStep_dexp {F b ℓ : ℕ} (hFb : F ≤ b) {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ F)
    (hF : 1 ≤ F) (cnt : ℕ) :
    spreadStep F b ℓ cnt (dexp (b * 2 ^ (ℓ + 1)) (blk F (ℓ + 1) f) cnt) =
      dexp (b * 2 ^ ℓ) (blk F ℓ f) (2 * cnt) := by
  have hc : F * 2 ^ ℓ ≤ b * 2 ^ ℓ := Nat.mul_le_mul_right _ hFb
  have hB : ∀ β, blk F (ℓ + 1) f β < 2 ^ (b * 2 ^ (ℓ + 1)) := fun β =>
    lt_of_lt_of_le (blk_lt hf β) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hFb))
  have hlo : lowMask F b ℓ cnt = dexp (b * 2 ^ (ℓ + 1)) (fun _ => 2 ^ (F * 2 ^ ℓ) - 1) cnt := by
    rw [lowMask, onesK_eq _ _ (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega)
      (by positivity))), mul_dexp, Nat.shiftLeft_eq, one_mul]
    simp
  have hhi : lowMask F b ℓ cnt <<< (F * 2 ^ ℓ) =
      dexp (b * 2 ^ (ℓ + 1)) (fun _ => (2 ^ (F * 2 ^ ℓ) - 1) <<< (F * 2 ^ ℓ)) cnt := by
    rw [hlo, Nat.shiftLeft_eq, mul_comm, mul_dexp]
    exact dexp_congr _ _ fun _ _ => by rw [Nat.shiftLeft_eq, mul_comm]
  have hmlo : 2 ^ (F * 2 ^ ℓ) - 1 < 2 ^ (b * 2 ^ (ℓ + 1)) :=
    lt_of_lt_of_le (Nat.sub_lt (by positivity) one_pos) (Nat.pow_le_pow_right (by norm_num)
      (by rw [pow_succ]; nlinarith [Nat.one_le_two_pow (n := ℓ)]))
  have hmhi : (2 ^ (F * 2 ^ ℓ) - 1) <<< (F * 2 ^ ℓ) < 2 ^ (b * 2 ^ (ℓ + 1)) := by
    rw [Nat.shiftLeft_eq]
    calc (2 ^ (F * 2 ^ ℓ) - 1) * 2 ^ (F * 2 ^ ℓ) < 2 ^ (F * 2 ^ ℓ) * 2 ^ (F * 2 ^ ℓ) :=
          Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by positivity) one_pos) (by positivity)
      _ = 2 ^ (F * 2 ^ (ℓ + 1)) := by rw [← pow_add, pow_succ]; ring_nf
      _ ≤ 2 ^ (b * 2 ^ (ℓ + 1)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hFb)
  unfold spreadStep
  rw [hlo, land_dexp (fun β _ => hB β) (fun _ _ => hmlo), ← hlo, hhi,
    land_dexp (fun β _ => hB β) (fun _ _ => hmhi)]
  have hL : ∀ β, blk F (ℓ + 1) f β &&& (2 ^ (F * 2 ^ ℓ) - 1) = blk F ℓ f (2 * β) := fun β => by
    rw [blk_succ, land_low (blk_lt hf _)]
  have hH : ∀ β, blk F (ℓ + 1) f β &&& ((2 ^ (F * 2 ^ ℓ) - 1) <<< (F * 2 ^ ℓ)) =
      2 ^ (F * 2 ^ ℓ) * blk F ℓ f (2 * β + 1) := fun β => by
    rw [blk_succ, land_high (blk_lt hf _) (blk_lt hf _)]
  rw [dexp_congr _ _ fun β _ => hL β, dexp_congr _ _ fun β _ => hH β, Nat.shiftLeft_eq,
    ← mul_dexp]
  have e1 : 2 ^ (F * 2 ^ ℓ) * 2 ^ ((b - F) * 2 ^ ℓ) = 2 ^ (b * 2 ^ ℓ) := by
    rw [← pow_add, ← add_mul, Nat.add_sub_cancel' hFb]
  calc dexp (b * 2 ^ (ℓ + 1)) (fun β => blk F ℓ f (2 * β)) cnt +
        2 ^ (F * 2 ^ ℓ) * dexp (b * 2 ^ (ℓ + 1)) (fun β => blk F ℓ f (2 * β + 1)) cnt *
          2 ^ ((b - F) * 2 ^ ℓ)
      = dexp (b * 2 ^ (ℓ + 1)) (fun β => blk F ℓ f (2 * β)) cnt +
          2 ^ (b * 2 ^ ℓ) * dexp (b * 2 ^ (ℓ + 1)) (fun β => blk F ℓ f (2 * β + 1)) cnt := by
        rw [← e1]; ring
    _ = dexp (2 * (b * 2 ^ ℓ)) (fun β => blk F ℓ f (2 * β) + 2 ^ (b * 2 ^ ℓ) *
          blk F ℓ f (2 * β + 1)) cnt := by
        rw [mul_dexp, dexp_add_fun, show b * 2 ^ (ℓ + 1) = 2 * (b * 2 ^ ℓ) by ring]
    _ = dexp (b * 2 ^ ℓ) (blk F ℓ f) (2 * cnt) := dexp_pairs _ _ _

/-- The single block of `2^k` fields. -/
theorem blk_full (F k : ℕ) (f : ℕ → ℕ) : dexp (F * 2 ^ k) (blk F k f) 1 = dexp F f (2 ^ k) := by
  simp [dexp, blk]

/-- Blocks of one field. -/
theorem blk_zero (F : ℕ) (f : ℕ → ℕ) (β : ℕ) : blk F 0 f β = f β := by simp [blk, dexp]

/-- The spreading iteration on an expansion. -/
theorem spreadIt_dexp {F b k : ℕ} (hFb : F ≤ b) (hF : 1 ≤ F) {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ F) :
    ∀ m, m ≤ k →
      spreadIt F b k m (dexp F f (2 ^ k)) = dexp (b * 2 ^ (k - m)) (blk F (k - m) f) (2 ^ m)
  | 0, _ => by
    simp only [spreadIt, Nat.sub_zero, pow_zero]
    simp [dexp, blk]
  | m + 1, hm => by
    have ih := spreadIt_dexp (k := k) hFb hF hf m (by omega)
    change spreadStep F b (k - 1 - m) (2 ^ m) (spreadIt F b k m (dexp F f (2 ^ k))) = _
    have e1 : k - m = (k - 1 - m) + 1 := by omega
    have e2 : k - (m + 1) = k - 1 - m := by omega
    rw [ih, e1, spreadStep_dexp hFb hf hF, e2, pow_succ, mul_comm (2 ^ m) 2]

/-- **Spreading is correct**: `spread F b k (∑_{t<2^k} f_t 2^{Ft}) = ∑_{t<2^k} f_t 2^{bt}`. -/
theorem spread_dexp {F b k : ℕ} (hFb : F ≤ b) (hF : 1 ≤ F) {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ F) :
    spread F b k (dexp F f (2 ^ k)) = dexp b f (2 ^ k) := by
  rw [spread, spreadIt_dexp hFb hF hf k le_rfl, Nat.sub_self, pow_zero, mul_one]
  exact dexp_congr b _ fun β _ => blk_zero F f β

/-! ## Reversing -/

/-- **One reversing level on a block expansion.** -/
theorem revStep_dexp {c : ℕ} (hc : 1 ≤ c) {p q : ℕ → ℕ} (hp : ∀ t, p t < 2 ^ c)
    (hq : ∀ t, q t < 2 ^ c) (cnt : ℕ) :
    revStep c cnt (dexp (2 * c) (fun β => p β + 2 ^ c * q β) cnt) =
      dexp (2 * c) (fun β => q β + 2 ^ c * p β) cnt := by
  have hB : ∀ β, p β + 2 ^ c * q β < 2 ^ (2 * c) := fun β => by
    have h1 := hp β; have h2 := hq β
    calc p β + 2 ^ c * q β < 2 ^ c + 2 ^ c * q β := by omega
      _ = 2 ^ c * (q β + 1) := by ring
      _ ≤ 2 ^ c * 2 ^ c := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (2 * c) := by rw [← pow_add]; ring_nf
  have hlo : ((1 <<< c) - 1) * onesK (2 * c) cnt = dexp (2 * c) (fun _ => 2 ^ c - 1) cnt := by
    rw [onesK_eq _ _ (by omega), mul_dexp, Nat.shiftLeft_eq, one_mul]
    simp
  have hm1 : 2 ^ c - 1 < 2 ^ (2 * c) :=
    lt_of_lt_of_le (Nat.sub_lt (by positivity) one_pos)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hm2 : (2 ^ c - 1) <<< c < 2 ^ (2 * c) := by
    rw [Nat.shiftLeft_eq]
    calc (2 ^ c - 1) * 2 ^ c < 2 ^ c * 2 ^ c :=
          Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by positivity) one_pos) (by positivity)
      _ = 2 ^ (2 * c) := by rw [← pow_add]; ring_nf
  have hhi : (((1 <<< c) - 1) * onesK (2 * c) cnt) <<< c =
      dexp (2 * c) (fun _ => (2 ^ c - 1) <<< c) cnt := by
    rw [hlo, Nat.shiftLeft_eq, mul_comm, mul_dexp]
    exact dexp_congr _ _ fun _ _ => by rw [Nat.shiftLeft_eq, mul_comm]
  unfold revStep
  rw [hlo, land_dexp (fun β _ => hB β) (fun _ _ => hm1), ← hlo, hhi,
    land_dexp (fun β _ => hB β) (fun _ _ => hm2)]
  rw [dexp_congr _ _ fun β _ => land_low (c := c) (x := q β) (hp β),
    dexp_congr _ _ fun β _ => land_high (d := c) (hp β) (hq β)]
  have e1 : dexp (2 * c) p cnt <<< c = dexp (2 * c) (fun β => 2 ^ c * p β) cnt := by
    rw [Nat.shiftLeft_eq, mul_comm, mul_dexp]
  have e2 : dexp (2 * c) (fun β => 2 ^ c * q β) cnt >>> c = dexp (2 * c) q cnt := by
    rw [Nat.shiftRight_eq_div_pow, ← mul_dexp, Nat.mul_div_cancel_left _ (by positivity)]
  rw [e1, e2, dexp_add_fun]
  exact dexp_congr _ _ fun β _ => by ring

/-- The reversing iteration on an expansion. -/
theorem revIt_dexp {b k : ℕ} (hb : 1 ≤ b) {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ b) :
    ∀ m, m ≤ k → revIt b k m (dexp b f (2 ^ k)) =
      dexp (b * 2 ^ (k - m)) (fun β => blk b (k - m) f (2 ^ m - 1 - β)) (2 ^ m)
  | 0, _ => by
    simp only [revIt, Nat.sub_zero, pow_zero]
    simp [dexp, blk]
  | m + 1, hm => by
    have ih := revIt_dexp (k := k) hb hf m (by omega)
    change revStep (b * 2 ^ (k - 1 - m)) (2 ^ m) (revIt b k m (dexp b f (2 ^ k))) = _
    set ℓ := k - 1 - m with hℓ
    have hkm : k - m = ℓ + 1 := by omega
    have hkm' : k - (m + 1) = ℓ := by omega
    rw [ih, hkm, hkm']
    have hc : 1 ≤ b * 2 ^ ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by positivity))
    have hsplit : ∀ β, blk b (ℓ + 1) f (2 ^ m - 1 - β) =
        blk b ℓ f (2 * (2 ^ m - 1 - β)) + 2 ^ (b * 2 ^ ℓ) * blk b ℓ f (2 * (2 ^ m - 1 - β) + 1) :=
      fun β => blk_succ b ℓ f _
    rw [show b * 2 ^ (ℓ + 1) = 2 * (b * 2 ^ ℓ) by ring, dexp_congr _ _ fun β _ => hsplit β,
      revStep_dexp hc (fun t => blk_lt hf _) (fun t => blk_lt hf _),
      pow_succ, mul_comm (2 ^ m) 2, ← dexp_pairs]
    refine dexp_congr _ _ fun β hβ => ?_
    have hβ' : β < 2 ^ m := hβ
    rw [show 2 * 2 ^ m - 1 - 2 * β = 2 * (2 ^ m - 1 - β) + 1 by omega,
      show 2 * 2 ^ m - 1 - (2 * β + 1) = 2 * (2 ^ m - 1 - β) by omega]

/-- **Reversing is correct**:
`rev b k (∑_{t<2^k} f_t 2^{bt}) = ∑_{t<2^k} f_{2^k − 1 − t} 2^{bt}`. -/
theorem rev_dexp {b k : ℕ} (hb : 1 ≤ b) {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ b) :
    rev b k (dexp b f (2 ^ k)) = dexp b (fun t => f (2 ^ k - 1 - t)) (2 ^ k) := by
  rw [rev, revIt_dexp hb hf k le_rfl, Nat.sub_self, pow_zero, mul_one]
  exact dexp_congr b _ fun β _ => blk_zero b f _

/-! ## Digit decomposition -/

/-- The fields of `x` of width `F`. -/
def fld (F x t : ℕ) : ℕ := (x >>> (F * t)) % 2 ^ F

/-- **Digit decomposition**: `x mod 2^{Fn}` is the expansion of its first `n` fields. -/
theorem mod_eq_dexp_fld (F x : ℕ) : ∀ n, x % 2 ^ (F * n) = dexp F (fld F x) n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [dexp_succ, ← mod_eq_dexp_fld F x n, mul_add, mul_one, pow_add, Nat.mod_mul, fld,
      Nat.shiftRight_eq_div_pow]
    ring

/-- Fields are below `2^F`. -/
theorem fld_lt (F x t : ℕ) : fld F x t < 2 ^ F := Nat.mod_lt _ (by positivity)

/-- **Sanity**: spreading the fields `1, 2` of width `2` to width `4`. -/
theorem spread_fixture : spread 2 4 1 (1 + 2 * 4) = 1 + 2 * 16 := by decide +kernel

/-- **Sanity**: reversing the digits `1, 2` of width `4`. -/
theorem rev_fixture : rev 4 1 (1 + 2 * 16) = 2 + 1 * 16 := by decide +kernel

/-- Spreading `0`. -/
theorem spreadIt_zero (F b k : ℕ) : ∀ m, spreadIt F b k m 0 = 0
  | 0 => rfl
  | m + 1 => by
    change spreadStep F b (k - 1 - m) (2 ^ m) (spreadIt F b k m 0) = 0
    rw [spreadIt_zero F b k m]
    simp [spreadStep]

/-- Spreading `0`. -/
theorem spread_zero (F b k : ℕ) : spread F b k 0 = 0 := spreadIt_zero F b k k

/-! ## Rows of fields -/

/-- The spread row is the digit expansion with width `b`. -/
theorem spreadRow_eq {F b k n x : ℕ} (hFb : F ≤ b) (hF : 1 ≤ F) (hn : n ≤ 2 ^ k) :
    spreadRow F b k n x = dexp b (fld F x) n := by
  have hb : 1 ≤ b := le_trans hF hFb
  have hfb : ∀ t, fld F x t < 2 ^ b := fun t =>
    lt_of_lt_of_le (fld_lt F x t) (Nat.pow_le_pow_right (by norm_num) hFb)
  rw [spreadRow, Nat.shiftLeft_eq, one_mul, Nat.shiftLeft_eq, one_mul, mod_eq_dexp_fld F x (2 ^ k),
    spread_dexp hFb hF (fld_lt F x)]
  have := dexp_mod (b := b) (e := fld F x) (m := n) (n := 2 ^ k - n) fun t _ => hfb t
  rwa [show n + (2 ^ k - n) = 2 ^ k by omega] at this

/-- The reversed spread row is the reversed digit expansion with width `b`. -/
theorem spreadRowR_eq {F b k n x : ℕ} (hFb : F ≤ b) (hF : 1 ≤ F) (hn : n ≤ 2 ^ k) :
    spreadRowR F b k n x = dexp b (fun t => fld F x (n - 1 - t)) n := by
  have hb : 1 ≤ b := le_trans hF hFb
  have hfb : ∀ t, fld F x t < 2 ^ b := fun t =>
    lt_of_lt_of_le (fld_lt F x t) (Nat.pow_le_pow_right (by norm_num) hFb)
  rw [spreadRowR, Nat.shiftLeft_eq, one_mul, mod_eq_dexp_fld F x (2 ^ k),
    spread_dexp hFb hF (fld_lt F x), rev_dexp hb hfb]
  have := dexp_shiftRight (b := b) (e := fun t => fld F x (2 ^ k - 1 - t)) (m := 2 ^ k - n) (n := n)
    fun t _ => hfb _
  rw [show 2 ^ k - n + n = 2 ^ k by omega] at this
  rw [this]
  refine dexp_congr b n fun t ht => ?_
  congr 1
  omega

end PlasmaLean.Certificates.KronDigits
