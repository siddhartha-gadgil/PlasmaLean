/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BounceIntegrals

/-!
# Signed cell sums for bounce integrals with oscillatory integrands

Companion to `Theory/Kinetic/BounceIntegrals` (`integral_le_cell_sum`), for integrands of
**either sign** (such as `g cos 2(φ − φ₀)` along a banana orbit). On a stretch `[a, b]` where a
coordinate `x` increases from `x a = 0`, a pointwise bound `Ω ≤ U_i ẋ` whenever `x t` lies in
the `i`-th cell `[i h, (i+1) h]` integrates **exactly cell by cell**:

`∫_a^b Ω ≤ Σ_{i ≤ n} U_i · clampW h (x b − i h)`, `clampW h y = max 0 (min y h)`,

(`integral_le_clamp_sum`); `clampW h (x b − i h)` is the length of the part of cell `i` swept by
`x`, so the bound is the integral of the step function `U` over `[0, x b]`. The decreasing
version is `integral_le_clamp_sum_rev`. No division by `ẋ` occurs.

Corollaries:
* `clamp_sum_le_flags`: if cell `i` is known to be fully swept whenever the flag `F i` holds,
  then `Σ U_i clampW … ≤ h Σ (if F i then U_i else max U_i 0)`; `flags_le_clamp_sum` is the lower
  version with `min L_i 0`;
* `clamp_sum_le_partial`, `partial_le_clamp_sum`: when `x b` lies in cell `i`,
  `Σ_{j ≤ i} U_j clampW … ≤ h Σ_{j < i} U_j + h max U_i 0` (and the lower version).

These are the tools for enclosing `C = ∫ g cos 2(φ − φ₀)`, `S = ∫ g sin 2(φ − φ₀)` and the
accumulated phase `φ(t) − φ₀` along an exact-QA banana (`Design/NearAxisQATrappedOscKick`).

Sanity: `clampW_fixture` (the clamp weights of one cell), `clamp_sum_fixture` (the comparison for
`Ω = −ẋ` on one cell gives `∫ ≤ −h`, an equality: signed bounds are kept).
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open Real Set

/-- The length `max 0 (min y h)` of `[0, y] ∩ [0, h]`. -/
@[expose] def clampW (h y : ℝ) : ℝ := max 0 (min y h)

/-- Clamp weights are nonnegative. -/
theorem clampW_nonneg (h y : ℝ) : 0 ≤ clampW h y := le_max_left _ _

/-- Clamp weights are at most `h`. -/
theorem clampW_le {h y : ℝ} (hh : 0 ≤ h) : clampW h y ≤ h :=
  max_le hh (min_le_right _ _)

/-- A fully swept cell has weight `h`. -/
theorem clampW_of_le {h y : ℝ} (hh : 0 ≤ h) (hy : h ≤ y) : clampW h y = h := by
  unfold clampW; rw [min_eq_right hy, max_eq_right hh]

/-- An unswept cell has weight `0`. -/
theorem clampW_of_nonpos {h y : ℝ} (hh : 0 ≤ h) (hy : y ≤ 0) : clampW h y = 0 := by
  unfold clampW; rw [min_eq_left (hy.trans hh), max_eq_left hy]

/-- A partially swept cell has weight `y`. -/
theorem clampW_of_mem {h y : ℝ} (hy0 : 0 ≤ y) (hyh : y ≤ h) : clampW h y = y := by
  unfold clampW; rw [min_eq_left hyh, max_eq_right hy0]

/-- Helper for `integral_le_clamp_sum`: induction on the number of cells. -/
theorem integral_le_clamp_sum_aux {Ω x x' : ℝ → ℝ} {a B h : ℝ} {U : ℕ → ℝ} {N : ℕ}
    (hh : 0 < h)
    (hx : ∀ t ∈ Icc a B, HasDerivAt x (x' t) t) (hx'0 : ∀ t ∈ Icc a B, 0 ≤ x' t)
    (hΩ : ContinuousOn Ω (Icc a B)) (hx'c : ContinuousOn x' (Icc a B)) (hxa : x a = 0)
    (hcell : ∀ t ∈ Icc a B, ∀ i : ℕ, i ≤ N → x t ∈ Icc (i * h) ((i + 1) * h) →
      Ω t ≤ U i * x' t) :
    ∀ n : ℕ, n ≤ N → ∀ b ∈ Icc a B, x b ≤ (n + 1) * h →
      ∫ t in a..b, Ω t ≤ ∑ i ∈ Finset.range (n + 1), U i * clampW h (x b - i * h) := by
  have hmono := monotoneOn_of_hasDerivAt_nonneg hx hx'0
  have haB : ∀ b ∈ Icc a B, Icc a b ⊆ Icc a B := fun b hb => Icc_subset_Icc le_rfl hb.2
  have one : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ B → ∀ i : ℕ, i ≤ N →
      (∀ t ∈ Icc c d, x t ∈ Icc (i * h) ((i + 1) * h)) →
      ∫ t in c..d, Ω t ≤ U i * (x d - x c) := by
    intro c d hac hcd hdB i hiN hin
    have hs : Icc c d ⊆ Icc a B := Icc_subset_Icc hac hdB
    exact integral_le_mul_sub hcd (fun t ht => hx t (hs ht)) (hΩ.mono hs) (hx'c.mono hs)
      (fun t ht => hcell t (hs ht) i hiN (hin t ht))
  have hxb0 : ∀ b ∈ Icc a B, 0 ≤ x b := fun b hb => by
    rw [← hxa]; exact hmono ⟨le_rfl, hb.1.trans hb.2⟩ hb hb.1
  intro n
  induction n with
  | zero =>
    intro _ b hb hxb
    have hin : ∀ t ∈ Icc a b, x t ∈ Icc (((0 : ℕ) : ℝ) * h) ((((0 : ℕ) : ℝ) + 1) * h) := by
      intro t ht
      have h1 : x a ≤ x t := hmono ⟨le_rfl, hb.1.trans hb.2⟩ (haB b hb ht) ht.1
      have h2 : x t ≤ x b := hmono (haB b hb ht) ⟨hb.1, hb.2⟩ ht.2
      push_cast at hxb ⊢
      constructor <;> linarith
    have := one a b le_rfl hb.1 hb.2 0 (Nat.zero_le N) hin
    rw [hxa, sub_zero] at this
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul,
      sub_zero, one_mul] at this hxb ⊢
    rwa [clampW_of_mem (hxb0 b hb) hxb]
  | succ n ih =>
    intro hnN b hb hxb
    rw [Finset.sum_range_succ]
    rcases le_or_gt (x b) ((n + 1) * h) with hle | hgt
    · have := ih (by omega) b hb hle
      have e : clampW h (x b - ((n + 1 : ℕ) : ℝ) * h) = 0 :=
        clampW_of_nonpos hh.le (by push_cast; linarith)
      rw [e, mul_zero, add_zero]; exact this
    · -- the time `c` at which `x` reaches the cell boundary `(n+1) h`
      have hxc : ContinuousOn x (Icc a b) :=
        fun t ht => (hx t (haB b hb ht)).continuousAt.continuousWithinAt
      have hlev : ((n : ℝ) + 1) * h ∈ Icc (x a) (x b) := by
        rw [hxa]; exact ⟨by positivity, hgt.le⟩
      obtain ⟨c, hc, hxc'⟩ := intermediate_value_Icc hb.1 hxc hlev
      have hcB : c ∈ Icc a B := haB b hb hc
      have h1 := ih (by omega) c hcB (by rw [hxc'])
      have hin : ∀ t ∈ Icc c b,
          x t ∈ Icc (((n + 1 : ℕ) : ℝ) * h) ((((n + 1 : ℕ) : ℝ) + 1) * h) := by
        intro t ht
        have htI : t ∈ Icc a B := ⟨hc.1.trans ht.1, ht.2.trans hb.2⟩
        have e1 : x c ≤ x t := hmono hcB htI ht.1
        have e2 : x t ≤ x b := hmono htI ⟨hb.1, hb.2⟩ ht.2
        push_cast at hxb ⊢
        constructor <;> linarith
      have h2 := one c b hc.1 hc.2 hb.2 (n + 1) hnN hin
      have hsplit : ∫ t in a..b, Ω t = (∫ t in a..c, Ω t) + ∫ t in c..b, Ω t := by
        have hi : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ B →
            IntervalIntegrable Ω MeasureTheory.volume u v := by
          intro u v hau huv hvB
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le huv]; exact hΩ.mono (Icc_subset_Icc hau hvB)
        rw [intervalIntegral.integral_add_adjacent_intervals (hi a c le_rfl hc.1 hcB.2)
          (hi c b hc.1 hc.2 hb.2)]
      -- the first `n + 1` cells are fully swept, both at `c` and at `b`
      have hfull : ∀ i ∈ Finset.range (n + 1),
          U i * clampW h (x c - i * h) = U i * clampW h (x b - i * h) := by
        intro i hi
        have hi' : (i : ℝ) + 1 ≤ n + 1 := by
          have := Finset.mem_range.mp hi; exact_mod_cast this
        rw [clampW_of_le hh.le (by rw [hxc']; nlinarith),
          clampW_of_le hh.le (by nlinarith)]
      rw [Finset.sum_congr rfl hfull] at h1
      have e : clampW h (x b - ((n + 1 : ℕ) : ℝ) * h) = x b - x c := by
        rw [hxc']; push_cast
        exact clampW_of_mem (by linarith) (by push_cast at hxb; linarith)
      rw [hsplit, e]
      linarith

/-- **Signed cell comparison, increasing coordinate.** Let `x` have derivative `x' ≥ 0` on
`[a, b]`, `x a = 0`, `x b ≤ (n+1) h`, and suppose that whenever `x t` lies in the cell
`[i h, (i+1) h]` the integrand satisfies `Ω t ≤ U i · x' t` (`U i` of any sign). Then
`∫_a^b Ω ≤ Σ_{i ≤ n} U i · clampW h (x b − i h)`. -/
theorem integral_le_clamp_sum {Ω x x' : ℝ → ℝ} {a b h : ℝ} {U : ℕ → ℝ} {n : ℕ} (hab : a ≤ b)
    (hh : 0 < h) (hx : ∀ t ∈ Icc a b, HasDerivAt x (x' t) t) (hx'0 : ∀ t ∈ Icc a b, 0 ≤ x' t)
    (hΩ : ContinuousOn Ω (Icc a b)) (hx'c : ContinuousOn x' (Icc a b)) (hxa : x a = 0)
    (hxb : x b ≤ (n + 1) * h)
    (hcell : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n → x t ∈ Icc (i * h) ((i + 1) * h) →
      Ω t ≤ U i * x' t) :
    ∫ t in a..b, Ω t ≤ ∑ i ∈ Finset.range (n + 1), U i * clampW h (x b - i * h) :=
  integral_le_clamp_sum_aux hh hx hx'0 hΩ hx'c hxa hcell n le_rfl b ⟨hab, le_rfl⟩ hxb

/-- **Signed cell comparison, decreasing coordinate.** If `x' ≤ 0` on `[a, b]`, `x b = 0`,
`x a ≤ (n+1) h`, and `Ω t ≤ U i · (−x' t)` whenever `x t ∈ [i h, (i+1) h]`, then
`∫_a^b Ω ≤ Σ_{i ≤ n} U i · clampW h (x a − i h)` (time reversal of `integral_le_clamp_sum`). -/
theorem integral_le_clamp_sum_rev {Ω x x' : ℝ → ℝ} {a b h : ℝ} {U : ℕ → ℝ} {n : ℕ}
    (hab : a ≤ b) (hh : 0 < h) (hx : ∀ t ∈ Icc a b, HasDerivAt x (x' t) t)
    (hx'0 : ∀ t ∈ Icc a b, x' t ≤ 0)
    (hΩ : ContinuousOn Ω (Icc a b)) (hx'c : ContinuousOn x' (Icc a b)) (hxb : x b = 0)
    (hxa : x a ≤ (n + 1) * h)
    (hcell : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n → x t ∈ Icc (i * h) ((i + 1) * h) →
      Ω t ≤ U i * -x' t) :
    ∫ t in a..b, Ω t ≤ ∑ i ∈ Finset.range (n + 1), U i * clampW h (x a - i * h) := by
  have hneg : ∀ s ∈ Icc (-b) (-a), -s ∈ Icc a b := fun s hs => ⟨by linarith [hs.2], by
    linarith [hs.1]⟩
  have key := integral_le_clamp_sum (Ω := fun s => Ω (-s)) (x := fun s => x (-s))
    (x' := fun s => -x' (-s)) (a := -b) (b := -a) (h := h) (U := U) (n := n)
    (by linarith) hh
    (fun s hs => by
      have := (hx (-s) (hneg s hs)).comp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this)
    (fun s hs => by simpa using hx'0 (-s) (hneg s hs))
    (hΩ.comp continuousOn_neg (fun s hs => hneg s hs))
    ((hx'c.comp continuousOn_neg (fun s hs => hneg s hs)).neg)
    (by simpa using hxb) (by simpa using hxa)
    (fun s hs i hin hi => hcell (-s) (hneg s hs) i hin hi)
  rw [intervalIntegral.integral_comp_neg (fun s => Ω s), neg_neg, neg_neg] at key
  simpa using key

/-- **Lower signed cell comparison, increasing coordinate**: `L i · x' ≤ Ω` in cell `i` gives
`Σ_{i ≤ n} L i · clampW h (x b − i h) ≤ ∫_a^b Ω`. -/
theorem clamp_sum_le_integral {Ω x x' : ℝ → ℝ} {a b h : ℝ} {L : ℕ → ℝ} {n : ℕ} (hab : a ≤ b)
    (hh : 0 < h) (hx : ∀ t ∈ Icc a b, HasDerivAt x (x' t) t) (hx'0 : ∀ t ∈ Icc a b, 0 ≤ x' t)
    (hΩ : ContinuousOn Ω (Icc a b)) (hx'c : ContinuousOn x' (Icc a b)) (hxa : x a = 0)
    (hxb : x b ≤ (n + 1) * h)
    (hcell : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n → x t ∈ Icc (i * h) ((i + 1) * h) →
      L i * x' t ≤ Ω t) :
    ∑ i ∈ Finset.range (n + 1), L i * clampW h (x b - i * h) ≤ ∫ t in a..b, Ω t := by
  have := integral_le_clamp_sum (Ω := fun t => -Ω t) (U := fun i => -L i) hab hh hx hx'0
    hΩ.neg hx'c hxa hxb (fun t ht i hin hi => by have := hcell t ht i hin hi; linarith)
  rw [intervalIntegral.integral_neg] at this
  have e : ∑ i ∈ Finset.range (n + 1), -L i * clampW h (x b - i * h) =
      -∑ i ∈ Finset.range (n + 1), L i * clampW h (x b - i * h) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext i; ring
  linarith

/-- **Lower signed cell comparison, decreasing coordinate.** -/
theorem clamp_sum_le_integral_rev {Ω x x' : ℝ → ℝ} {a b h : ℝ} {L : ℕ → ℝ} {n : ℕ}
    (hab : a ≤ b) (hh : 0 < h) (hx : ∀ t ∈ Icc a b, HasDerivAt x (x' t) t)
    (hx'0 : ∀ t ∈ Icc a b, x' t ≤ 0)
    (hΩ : ContinuousOn Ω (Icc a b)) (hx'c : ContinuousOn x' (Icc a b)) (hxb : x b = 0)
    (hxa : x a ≤ (n + 1) * h)
    (hcell : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n → x t ∈ Icc (i * h) ((i + 1) * h) →
      L i * -x' t ≤ Ω t) :
    ∑ i ∈ Finset.range (n + 1), L i * clampW h (x a - i * h) ≤ ∫ t in a..b, Ω t := by
  have := integral_le_clamp_sum_rev (Ω := fun t => -Ω t) (U := fun i => -L i) hab hh hx hx'0
    hΩ.neg hx'c hxb hxa (fun t ht i hin hi => by have := hcell t ht i hin hi; linarith)
  rw [intervalIntegral.integral_neg] at this
  have e : ∑ i ∈ Finset.range (n + 1), -L i * clampW h (x a - i * h) =
      -∑ i ∈ Finset.range (n + 1), L i * clampW h (x a - i * h) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext i; ring
  linarith

/-! ## Weight bounds -/

/-- **Flagged weights, upper bound.** If cell `i` is fully swept (`(i+1) h ≤ y`) whenever the
flag `F i` holds, then `Σ_{i ≤ n} U i clampW h (y − i h) ≤ h Σ_{i ≤ n} (if F i then U i else
max (U i) 0)`. -/
theorem clamp_sum_le_flags {h y : ℝ} (hh : 0 ≤ h) (U : ℕ → ℝ) (F : ℕ → Bool) (n : ℕ)
    (hF : ∀ i ≤ n, F i = true → ((i : ℝ) + 1) * h ≤ y) :
    ∑ i ∈ Finset.range (n + 1), U i * clampW h (y - i * h) ≤
      h * ∑ i ∈ Finset.range (n + 1), (if F i then U i else max (U i) 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h0 := clampW_nonneg h (y - i * h)
  have h1 := clampW_le (y := y - i * h) hh
  by_cases hf : F i = true
  · simp only [hf, ite_true]
    rw [clampW_of_le hh (by linarith [hF i hin hf])]; ring_nf; rfl
  · simp only [hf, Bool.false_eq_true, ite_false]
    rcases le_total 0 (U i) with hu | hu
    · rw [max_eq_left hu]; nlinarith
    · rw [max_eq_right hu]; nlinarith

/-- **Flagged weights, lower bound**: `h Σ (if F i then L i else min (L i) 0) ≤
Σ L i clampW h (y − i h)`. -/
theorem flags_le_clamp_sum {h y : ℝ} (hh : 0 ≤ h) (L : ℕ → ℝ) (F : ℕ → Bool) (n : ℕ)
    (hF : ∀ i ≤ n, F i = true → ((i : ℝ) + 1) * h ≤ y) :
    h * ∑ i ∈ Finset.range (n + 1), (if F i then L i else min (L i) 0) ≤
      ∑ i ∈ Finset.range (n + 1), L i * clampW h (y - i * h) := by
  have := clamp_sum_le_flags hh (fun i => -L i) F n hF
  have e1 : ∑ i ∈ Finset.range (n + 1), -L i * clampW h (y - i * h) =
      -∑ i ∈ Finset.range (n + 1), L i * clampW h (y - i * h) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext i; ring
  have e2 : ∑ i ∈ Finset.range (n + 1), (if F i then -L i else max (-L i) 0) =
      -∑ i ∈ Finset.range (n + 1), (if F i then L i else min (L i) 0) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext i
    split_ifs
    · rfl
    · rw [← max_neg_neg, neg_zero]
  rw [e1, e2] at this
  linarith

/-- **Partial sweep, upper bound.** If `y ∈ [i h, (i+1) h]` then
`Σ_{j ≤ i} U j clampW h (y − j h) ≤ h Σ_{j < i} U j + h max (U i) 0`. -/
theorem clamp_sum_le_partial {h y : ℝ} (hh : 0 ≤ h) (U : ℕ → ℝ) (i : ℕ)
    (hy : y ∈ Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :
    ∑ j ∈ Finset.range (i + 1), U j * clampW h (y - j * h) ≤
      h * ∑ j ∈ Finset.range i, U j + h * max (U i) 0 := by
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hfull : ∀ j ∈ Finset.range i, U j * clampW h (y - j * h) = h * U j := by
    intro j hj
    have : (j : ℝ) + 1 ≤ i := by have := Finset.mem_range.mp hj; exact_mod_cast this
    rw [clampW_of_le hh (by nlinarith [hy.1])]; ring
  rw [Finset.sum_congr rfl hfull]
  have h0 := clampW_nonneg h (y - i * h)
  have h1 := clampW_le (y := y - i * h) hh
  have : U i * clampW h (y - i * h) ≤ h * max (U i) 0 := by
    rcases le_total 0 (U i) with hu | hu
    · rw [max_eq_left hu]; nlinarith
    · rw [max_eq_right hu]; nlinarith
  linarith

/-- **Partial sweep, lower bound.** If `y ∈ [i h, (i+1) h]` then
`h Σ_{j < i} L j + h min (L i) 0 ≤ Σ_{j ≤ i} L j clampW h (y − j h)`. -/
theorem partial_le_clamp_sum {h y : ℝ} (hh : 0 ≤ h) (L : ℕ → ℝ) (i : ℕ)
    (hy : y ∈ Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :
    h * ∑ j ∈ Finset.range i, L j + h * min (L i) 0 ≤
      ∑ j ∈ Finset.range (i + 1), L j * clampW h (y - j * h) := by
  have := clamp_sum_le_partial hh (fun j => -L j) i hy
  have e1 : ∑ j ∈ Finset.range (i + 1), -L j * clampW h (y - j * h) =
      -∑ j ∈ Finset.range (i + 1), L j * clampW h (y - j * h) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext j; ring
  rw [e1, Finset.sum_neg_distrib, show max (-L i) 0 = -min (L i) 0 by
    rw [show (0 : ℝ) = -0 by simp, max_neg_neg]; simp] at this
  linarith

/-! ## Sanity checks -/

/-- Sanity (`clampW`): the weights of the cell `[0, 1]` at `y = 1/2`, `y = 2`, `y = −1`. -/
theorem clampW_fixture : clampW 1 (1 / 2) = 1 / 2 ∧ clampW 1 2 = 1 ∧ clampW 1 (-1) = 0 := by
  norm_num [clampW]

/-- Sanity (signed bounds are kept): with `x t = t − a`, `Ω = −ẋ = −1` and one cell of width
`h = b − a`, `integral_le_clamp_sum` gives `∫_a^b (−1) ≤ −h`, which is an equality. -/
theorem clamp_sum_fixture {a b : ℝ} (hab : a < b) : ∫ _t in a..b, (-1 : ℝ) ≤ -(b - a) := by
  have := integral_le_clamp_sum (Ω := fun _ => (-1 : ℝ)) (x := fun t => t - a)
    (x' := fun _ => 1) (h := b - a) (U := fun _ => -1) (n := 0) hab.le (by linarith)
    (fun t _ => (hasDerivAt_id t).sub_const a) (fun _ _ => zero_le_one) continuousOn_const
    continuousOn_const (by ring) (by push_cast; linarith) (fun _ _ _ _ _ => by norm_num)
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul,
    sub_zero] at this
  rwa [clampW_of_le (by linarith) le_rfl, neg_one_mul] at this

end PlasmaLean.Kinetic.Boozer
