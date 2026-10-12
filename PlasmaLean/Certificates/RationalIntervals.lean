/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Exact rational enclosure core

Endpoints are exact rational numbers. Membership means real containment; reversed
intervals are empty. Arithmetic soundness is kernel-checked. No floating-point or
string-parser trust is introduced. Nonnegative multiplication is intentionally
restricted; a general signed interval product and text parser remain separate work.
-/
public section

namespace PlasmaLean.Certificates

/-- Serializable rational endpoints; validity is checked rather than assumed. -/
structure RationalInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace RationalInterval
/-- Meaning of an enclosure after exact coercion into the reals. -/
@[expose] def Contains (I : RationalInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

/-- Executable endpoint-order check. -/
@[expose] def check (I : RationalInterval) : Bool := decide (I.lo ≤ I.hi)

/-- An accepted interval has ordered real endpoints. -/
theorem check_sound (I : RationalInterval) (h : I.check = true) : (I.lo : ℝ) ≤ I.hi := by
  have hq : I.lo ≤ I.hi := of_decide_eq_true h
  exact_mod_cast hq

/-- A collapsed enclosure denotes exactly its single rational value. -/
theorem singleton_iff (q : ℚ) (x : ℝ) : Contains ⟨q, q⟩ x ↔ x = q := by
  dsimp [Contains]
  constructor
  · intro h; exact le_antisymm h.2 h.1
  · intro h; rw [h]; exact ⟨le_rfl, le_rfl⟩

/-- Any inhabited enclosure has a passing endpoint check. -/
theorem check_of_contains {I : RationalInterval} {x : ℝ} (h : I.Contains x) : I.check = true := by
  have hr : (I.lo : ℝ) ≤ I.hi := h.1.trans h.2
  have hq : I.lo ≤ I.hi := by exact_mod_cast hr
  simp [check, hq]

/-- Exact interval sum. -/
@[expose] def add (I J : RationalInterval) : RationalInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Soundness of exact interval addition. -/
theorem add_sound {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  simp only [Contains, add, Rat.cast_add] at *
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

/-- Exact endpoint reversal under negation. -/
@[expose] def neg (I : RationalInterval) : RationalInterval := ⟨-I.hi, -I.lo⟩

/-- Soundness of interval negation, including negative enclosures. -/
theorem neg_sound {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    I.neg.Contains (-x) := by
  simp only [Contains, neg, Rat.cast_neg] at *
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

/-- Endpoint product for intervals known separately to be nonnegative. -/
@[expose] def mulNonneg (I J : RationalInterval) : RationalInterval := ⟨I.lo * J.lo, I.hi * J.hi⟩

/-- Product soundness requires both lower endpoints to be nonnegative. -/
theorem mulNonneg_sound {I J : RationalInterval} {x y : ℝ}
    (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) (hx : I.Contains x) (hy : J.Contains y) :
    (I.mulNonneg J).Contains (x * y) := by
  have hi : (0 : ℝ) ≤ I.lo := by exact_mod_cast hI
  have hj : (0 : ℝ) ≤ J.lo := by exact_mod_cast hJ
  have hxn : 0 ≤ x := hi.trans hx.1
  have hyn : 0 ≤ y := hj.trans hy.1
  simp only [Contains, mulNonneg, Rat.cast_mul]
  exact ⟨mul_le_mul hx.1 hy.1 hj hxn, mul_le_mul hx.2 hy.2 hyn (hxn.trans hx.2)⟩

/-- Reversed endpoints are rejected by exact computation. -/
theorem reversed_rejected : (⟨2, 1⟩ : RationalInterval).check = false := by norm_num [check]

/-- A valid interval passes by kernel-checked rational comparison. -/
theorem valid_accepted : (⟨-1, 2⟩ : RationalInterval).check = true := by norm_num [check]
end RationalInterval

/-- Decode an integer mantissa with a decimal scale, as an exact rational. -/
@[expose] def decodeDecimal (mantissa : ℤ) (places : ℕ) : ℚ := mantissa / 10 ^ places

/-- The decimal denominator is always nonzero. -/
theorem decimal_denominator_ne_zero (places : ℕ) : (10 : ℚ) ^ places ≠ 0 := by positivity

/-- Exact arithmetic example: the decimal 0.125 denotes one eighth. -/
theorem decimal_example : decodeDecimal 125 3 = 1 / 8 := by norm_num [decodeDecimal]

end PlasmaLean.Certificates
