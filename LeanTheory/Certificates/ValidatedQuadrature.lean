/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Validated quadrature: fixed-point interval arithmetic and sound cell sums

This module provides three reusable, kernel-checkable ingredients for turning a numerical
integral into a theorem.

**1. Fixed-point interval arithmetic (`FIv`).** An enclosure is a pair of integers
`lo, hi` read as `lo / 2³²`, `hi / 2³²`, plus a validity flag `ok`. Its meaning
(`FIv.Mem I x`) is "if `ok` then `lo/2³² ≤ x ≤ hi/2³²`"; an invalid enclosure contains
every real number (it is the "top" element), so every operation is total and its soundness
lemma is unconditional. Operations round outward with exact integer floor division:
`add`, `neg`, `sub`, `mul` (four corner products), `sq`, `inv` (valid only for strictly
positive enclosures, otherwise `ok := false`), `sqrt` (integer Newton iteration whose
result is CHECKED by squaring; a failed check widens or invalidates, never unsound) and
exact rational constants `ofFrac`. Integer arithmetic keeps kernel evaluation
(`rfl`, `eval_cert`) fast: no `gcd` normalisation, no floating point.

**2. Cell sums (`integral_mem_sumIv`).** If the unit interval is split into `N` equal cells
and an enclosure `c i` contains `g τ` for every real `τ` in cell `i`, then
`∫₀¹ g ∈ [Σ lo_i / (2³² N), Σ hi_i / (2³² N)]`. This is the rectangle (Riemann-sum)
bound with per-cell enclosures; it rests on the general lemmas
`integral_le_sum_of_cells` / `sum_le_integral_of_cells` (any `a`, `h`, `N`). A
Lipschitz-type cell enclosure (`cell_bounds_of_lipschitz`) is included for integrands
where a derivative bound is easier than an interval evaluation.

**3. Rational parametrisation of trigonometric integrals (`integral_sin_eq_rational`).**
For `f` continuous on `[-1, 1]`,
`∫_{-π}^{π} f(sin t) dt = 4 ∫₀¹ (f(y(τ)) + f(-y(τ))) / (1 + τ²) dτ`,
`y(τ) = 2τ/(1+τ²) = sin(2 arctan τ)`. This removes all transcendental functions from an
integrand that depends on `t` only through `sin t`, so cell enclosures need only rational
arithmetic and square roots.

Sanity fixtures: `fixture_sqrt_two` (an accepted enclosure of `√2`), `fixture_inv_rejected`
(inverting an enclosure that contains `0` is rejected), `fixture_square_integral`
(`∫₀¹ x² ≤ 15/32` from four cells) and `fixture_arctan_quarter` (the substitution lemma
with `f = 1` recovers `∫₀¹ 1/(1+τ²) = π/4`).
-/

public section

namespace LeanTheory.Certificates.ValidatedQuadrature

open Real Set MeasureTheory intervalIntegral

/-! ## Fixed-point numbers -/

/-- The fixed-point scale `2³²`. -/
@[expose] def fxScale : ℤ := 4294967296

/-- The real value `n / 2³²` of a fixed-point integer `n`. -/
@[expose] noncomputable def fxVal (n : ℤ) : ℝ := (n : ℝ) / (fxScale : ℝ)

/-- The scale as a real number. -/
theorem fxScale_real : ((fxScale : ℤ) : ℝ) = 4294967296 := by norm_num [fxScale]

/-- The scale is positive (as a real). -/
theorem fxScale_pos : (0 : ℝ) < (fxScale : ℝ) := by rw [fxScale_real]; norm_num

/-- The scale is positive (as an integer). -/
theorem fxScale_pos' : (0 : ℤ) < fxScale := by norm_num [fxScale]

/-- Floor division by a positive integer rounds down. -/
theorem fdiv_le (a d : ℤ) (hd : 0 < d) : ((a / d : ℤ) : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
  have h := Int.ediv_mul_le a hd.ne'
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast h

/-- Negated floor division of the negation rounds up. -/
theorem le_cdiv (a d : ℤ) (hd : 0 < d) : (a : ℝ) / (d : ℝ) ≤ ((-((-a) / d) : ℤ) : ℝ) := by
  have h := fdiv_le (-a) d hd
  push_cast at h ⊢
  have : -((a : ℝ) / d) = (-(a : ℝ)) / d := by ring
  linarith

/-! ## Enclosures -/

/-- A fixed-point enclosure: `[lo/2³², hi/2³²]` when `ok`, everything otherwise. -/
structure FIv where
  /-- Scaled lower endpoint. -/
  lo : ℤ
  /-- Scaled upper endpoint. -/
  hi : ℤ
  /-- Validity flag; an invalid enclosure contains every real number. -/
  ok : Bool
  deriving DecidableEq, Repr

namespace FIv

/-- Membership: if the enclosure is valid then `lo/2³² ≤ x ≤ hi/2³²`. -/
@[expose] def Mem (I : FIv) (x : ℝ) : Prop := I.ok = true → fxVal I.lo ≤ x ∧ x ≤ fxVal I.hi

/-- Membership in scaled form: `lo ≤ 2³² x ≤ hi`. -/
theorem mem_iff (I : FIv) (x : ℝ) :
    I.Mem x ↔ (I.ok = true → (I.lo : ℝ) ≤ fxScale * x ∧ fxScale * x ≤ I.hi) := by
  unfold Mem fxVal
  have h := fxScale_pos
  constructor
  · intro hm hok
    obtain ⟨h1, h2⟩ := hm hok
    rw [div_le_iff₀ h] at h1
    rw [le_div_iff₀ h] at h2
    constructor <;> linarith
  · intro hm hok
    obtain ⟨h1, h2⟩ := hm hok
    rw [div_le_iff₀ h, le_div_iff₀ h]
    constructor <;> linarith

/-- The exact enclosure of an integer. -/
@[expose] def ofInt (n : ℤ) : FIv := ⟨n * fxScale, n * fxScale, true⟩

/-- Outward-rounded enclosure of the rational `p / q` (valid only for `q > 0`). -/
@[expose] def ofFrac (p q : ℤ) : FIv :=
  ⟨(p * fxScale) / q, -((-(p * fxScale)) / q), decide (0 < q)⟩

/-- Interval sum (exact on the scaled integers). -/
@[expose] def add (I J : FIv) : FIv := ⟨I.lo + J.lo, I.hi + J.hi, I.ok && J.ok⟩

/-- Interval negation. -/
@[expose] def neg (I : FIv) : FIv := ⟨-I.hi, -I.lo, I.ok⟩

/-- Interval difference. -/
@[expose] def sub (I J : FIv) : FIv := ⟨I.lo - J.hi, I.hi - J.lo, I.ok && J.ok⟩

/-- Interval product from the four corner products, rounded outward. -/
@[expose] def mul (I J : FIv) : FIv :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) / fxScale,
    -((-(max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))) / fxScale),
    I.ok && J.ok⟩

/-- Interval square (tight when the enclosure straddles `0`). -/
@[expose] def sq (I : FIv) : FIv :=
  if 0 ≤ I.lo then ⟨I.lo * I.lo / fxScale, -((-(I.hi * I.hi)) / fxScale), I.ok⟩
  else if I.hi ≤ 0 then ⟨I.hi * I.hi / fxScale, -((-(I.lo * I.lo)) / fxScale), I.ok⟩
  else ⟨0, -((-(max (I.lo * I.lo) (I.hi * I.hi))) / fxScale), I.ok⟩

/-- Interval reciprocal; valid only for strictly positive enclosures. -/
@[expose] def inv (I : FIv) : FIv :=
  if 0 < I.lo then ⟨fxScale * fxScale / I.hi, -((-(fxScale * fxScale)) / I.lo), I.ok⟩
  else ⟨0, 0, false⟩

/-- Newton iteration for the integer square root (untrusted: results are checked). -/
@[expose] def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | k + 1, n, g => if (g + n / g) / 2 < g then isqrtAux k n ((g + n / g) / 2) else g

/-- Approximate integer square root (untrusted: results are checked by squaring). -/
@[expose] def isqrt (n : ℕ) : ℕ := isqrtAux 64 n (n / 4294967296 + 4294967296)

/-- Interval square root. The lower end is a checked integer square root of `lo · 2³²`
(or `0`); the upper end `s` is accepted only if `s² ≥ hi · 2³²`. -/
@[expose] def sqrt (I : FIv) : FIv :=
  ⟨if (isqrt (I.lo * fxScale).toNat : ℤ) * (isqrt (I.lo * fxScale).toNat : ℤ) ≤ I.lo * fxScale
      then (isqrt (I.lo * fxScale).toNat : ℤ) else 0,
    (isqrt (I.hi * fxScale).toNat : ℤ) + 1,
    I.ok && decide (I.hi * fxScale ≤
      ((isqrt (I.hi * fxScale).toNat : ℤ) + 1) * ((isqrt (I.hi * fxScale).toNat : ℤ) + 1))⟩

/-! ### Soundness of the operations -/

/-- Soundness of integer constants. -/
theorem mem_ofInt (n : ℤ) : (ofInt n).Mem (n : ℝ) := by
  rw [mem_iff]; intro _; simp only [ofInt]; push_cast; constructor <;> linarith

/-- Soundness of rational constants (for `q ≤ 0` the enclosure is invalid, hence vacuous). -/
theorem mem_ofFrac (p q : ℤ) : (ofFrac p q).Mem ((p : ℝ) / (q : ℝ)) := by
  rw [mem_iff]
  intro hok
  simp only [ofFrac, decide_eq_true_eq] at hok ⊢
  have hq : (0 : ℝ) < q := by exact_mod_cast hok
  have h1 := fdiv_le (p * fxScale) q hok
  have h2 := le_cdiv (p * fxScale) q hok
  push_cast at h1 h2 ⊢
  have e : (p : ℝ) * fxScale / q = fxScale * (p / q) := by field_simp
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-- Soundness of interval addition. -/
theorem mem_add {I J : FIv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.add J).Mem (x + y) := by
  rw [mem_iff] at *
  intro hok
  simp only [add, Bool.and_eq_true] at hok ⊢
  obtain ⟨a1, a2⟩ := hx hok.1
  obtain ⟨b1, b2⟩ := hy hok.2
  push_cast
  constructor <;> nlinarith

/-- Soundness of interval negation. -/
theorem mem_neg {I : FIv} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) := by
  rw [mem_iff] at *
  intro hok
  simp only [neg] at hok ⊢
  obtain ⟨a1, a2⟩ := hx hok
  push_cast
  constructor <;> nlinarith

/-- Soundness of interval subtraction. -/
theorem mem_sub {I J : FIv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.sub J).Mem (x - y) := by
  rw [mem_iff] at *
  intro hok
  simp only [sub, Bool.and_eq_true] at hok ⊢
  obtain ⟨a1, a2⟩ := hx hok.1
  obtain ⟨b1, b2⟩ := hy hok.2
  push_cast
  constructor <;> nlinarith

/-- A product is bracketed by the endpoint products in one factor. -/
theorem lin_bound {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) (c : ℝ) :
    min (a * c) (b * c) ≤ x * c ∧ x * c ≤ max (a * c) (b * c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_right h1 hc),
      le_max_of_le_right (mul_le_mul_of_nonneg_right h2 hc)⟩
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_right h2 hc),
      le_max_of_le_left (mul_le_mul_of_nonpos_right h1 hc)⟩

/-- Corner-product bounds for a product of two enclosed reals. -/
theorem corner_bounds {a1 a2 b1 b2 x y : ℝ} (ha1 : a1 ≤ x) (ha2 : x ≤ a2) (hb1 : b1 ≤ y)
    (hb2 : y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ x * y ∧
      x * y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  obtain ⟨hx1, hx2⟩ := lin_bound ha1 ha2 y
  obtain ⟨p1, p2⟩ := lin_bound hb1 hb2 a1
  obtain ⟨q1, q2⟩ := lin_bound hb1 hb2 a2
  rw [mul_comm b1 a1, mul_comm b2 a1, mul_comm y a1] at p1 p2
  rw [mul_comm b1 a2, mul_comm b2 a2, mul_comm y a2] at q1 q2
  constructor
  · exact le_trans (min_le_min p1 q1) hx1
  · exact le_trans hx2 (max_le_max p2 q2)

/-- Soundness of the outward-rounded interval product. -/
theorem mem_mul {I J : FIv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.mul J).Mem (x * y) := by
  rw [mem_iff] at *
  intro hok
  simp only [mul, Bool.and_eq_true] at hok ⊢
  obtain ⟨a1, a2⟩ := hx hok.1
  obtain ⟨b1, b2⟩ := hy hok.2
  have hS := fxScale_pos
  obtain ⟨c1, c2⟩ := corner_bounds a1 a2 b1 b2
  have e : fxScale * x * (fxScale * y) = (fxScale : ℝ) * (fxScale * (x * y)) := by ring
  rw [e] at c1 c2
  have l1 := fdiv_le (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)))
    fxScale fxScale_pos'
  have l2 := le_cdiv (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))
    fxScale fxScale_pos'
  push_cast at l1 l2 c1 c2 ⊢
  constructor
  · calc _ ≤ _ := l1
      _ ≤ (fxScale : ℝ) * (fxScale * (x * y)) / fxScale := div_le_div_of_nonneg_right c1 hS.le
      _ = _ := by field_simp
  · calc fxScale * (x * y) = (fxScale : ℝ) * (fxScale * (x * y)) / fxScale := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right c2 hS.le
      _ ≤ _ := l2

/-- Soundness of the interval square. -/
theorem mem_sq {I : FIv} {x : ℝ} (hx : I.Mem x) : I.sq.Mem (x ^ 2) := by
  rw [mem_iff] at *
  have hS := fxScale_pos
  have key : fxScale * x ^ 2 = (fxScale * x) * (fxScale * x) / fxScale := by field_simp
  unfold sq
  split_ifs with h0 h1
  · intro hok
    dsimp only at hok ⊢
    obtain ⟨a1, a2⟩ := hx hok
    have h0' : (0 : ℝ) ≤ I.lo := by exact_mod_cast h0
    have l1 := fdiv_le (I.lo * I.lo) fxScale fxScale_pos'
    have l2 := le_cdiv (I.hi * I.hi) fxScale fxScale_pos'
    push_cast at l1 l2 ⊢
    rw [key]
    constructor
    · exact le_trans l1 (div_le_div_of_nonneg_right (by nlinarith) hS.le)
    · exact le_trans (div_le_div_of_nonneg_right (by nlinarith) hS.le) l2
  · intro hok
    dsimp only at hok ⊢
    obtain ⟨a1, a2⟩ := hx hok
    have h1' : (I.hi : ℝ) ≤ 0 := by exact_mod_cast h1
    have l1 := fdiv_le (I.hi * I.hi) fxScale fxScale_pos'
    have l2 := le_cdiv (I.lo * I.lo) fxScale fxScale_pos'
    push_cast at l1 l2 ⊢
    rw [key]
    constructor
    · exact le_trans l1 (div_le_div_of_nonneg_right (by nlinarith) hS.le)
    · exact le_trans (div_le_div_of_nonneg_right (by nlinarith) hS.le) l2
  · intro hok
    dsimp only at hok ⊢
    obtain ⟨a1, a2⟩ := hx hok
    have l2 := le_cdiv (max (I.lo * I.lo) (I.hi * I.hi)) fxScale fxScale_pos'
    push_cast at l2 ⊢
    rw [key]
    constructor
    · exact div_nonneg (mul_self_nonneg _) hS.le
    · refine le_trans (div_le_div_of_nonneg_right ?_ hS.le) l2
      rcases le_total 0 (fxScale * x) with h | h
      · exact le_max_of_le_right (by nlinarith)
      · exact le_max_of_le_left (by nlinarith)

/-- Soundness of the interval reciprocal (invalid unless strictly positive). -/
theorem mem_inv {I : FIv} {x : ℝ} (hx : I.Mem x) : I.inv.Mem x⁻¹ := by
  rw [mem_iff] at *
  have hS := fxScale_pos
  unfold inv
  split_ifs with h0
  · intro hok
    dsimp only at hok ⊢
    obtain ⟨a1, a2⟩ := hx hok
    have h0' : (0 : ℝ) < I.lo := by exact_mod_cast h0
    have hhi : (0 : ℤ) < I.hi := by
      have : (0 : ℝ) < I.hi := by linarith
      exact_mod_cast this
    have hhi' : (0 : ℝ) < I.hi := by exact_mod_cast hhi
    have hxpos : 0 < x := by
      have : 0 < fxScale * x := lt_of_lt_of_le h0' a1
      exact pos_of_mul_pos_right this hS.le
    have l1 := fdiv_le (fxScale * fxScale) I.hi hhi
    have l2 := le_cdiv (fxScale * fxScale) I.lo h0
    push_cast at l1 l2 ⊢
    constructor
    · calc _ ≤ _ := l1
        _ ≤ (fxScale : ℝ) * fxScale / (fxScale * x) := by gcongr
        _ = _ := by field_simp
    · calc fxScale * x⁻¹ = (fxScale : ℝ) * fxScale / (fxScale * x) := by field_simp
        _ ≤ (fxScale : ℝ) * fxScale / I.lo := by gcongr
        _ ≤ _ := l2
  · intro hok; simp at hok

/-- Soundness of the checked interval square root (for every real `x`; `√x = 0` if `x < 0`). -/
theorem mem_sqrt {I : FIv} {x : ℝ} (hx : I.Mem x) : I.sqrt.Mem (√x) := by
  rw [mem_iff] at *
  have hS := fxScale_pos
  intro hok
  simp only [sqrt, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨a1, a2⟩ := hx hok.1
  have hsq := Real.sqrt_nonneg x
  constructor
  · split_ifs with h
    · set r : ℤ := (isqrt (I.lo * fxScale).toNat : ℤ)
      have hr0 : (0 : ℝ) ≤ r := by simp [r]
      have h' : (r : ℝ) * r ≤ I.lo * fxScale := by exact_mod_cast h
      have hle : ((r : ℝ) / fxScale) ^ 2 ≤ x := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        nlinarith
      have := Real.le_sqrt_of_sq_le hle
      rw [div_le_iff₀ hS] at this
      linarith
    · simp only [Int.cast_zero]; positivity
  · set s : ℤ := (isqrt (I.hi * fxScale).toNat : ℤ) + 1
    have hs0 : (0 : ℝ) ≤ s := by simp only [s]; push_cast; positivity
    have h' : (I.hi : ℝ) * fxScale ≤ s * s := by exact_mod_cast hok.2
    have hle : x ≤ ((s : ℝ) / fxScale) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      nlinarith
    have := Real.sqrt_le_sqrt hle
    rw [Real.sqrt_sq (by positivity), le_div_iff₀ hS] at this
    linarith

/-- Validity of an enclosure gives real bounds. -/
theorem Mem.bounds {I : FIv} {x : ℝ} (h : I.Mem x) (hok : I.ok = true) :
    fxVal I.lo ≤ x ∧ x ≤ fxVal I.hi := h hok

end FIv

/-! ## Cell sums -/

/-- Exact accumulation of the enclosures `c 0, …, c (k-1)` (no rounding: integer sums). -/
@[expose] def sumIv (c : ℕ → FIv) : ℕ → FIv
  | 0 => ⟨0, 0, true⟩
  | k + 1 => (sumIv c k).add (c k)

/-- The accumulated lower end is the exact sum of the lower ends. -/
theorem sumIv_lo (c : ℕ → FIv) (k : ℕ) : (sumIv c k).lo = ∑ i ∈ Finset.range k, (c i).lo := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sumIv, FIv.add, ih, Finset.sum_range_succ]

/-- The accumulated upper end is the exact sum of the upper ends. -/
theorem sumIv_hi (c : ℕ → FIv) (k : ℕ) : (sumIv c k).hi = ∑ i ∈ Finset.range k, (c i).hi := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sumIv, FIv.add, ih, Finset.sum_range_succ]

/-- A valid accumulation has only valid summands. -/
theorem sumIv_ok (c : ℕ → FIv) (k : ℕ) (h : (sumIv c k).ok = true) :
    ∀ i < k, (c i).ok = true := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [sumIv, FIv.add, Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · exact ih h.1 i h'
    · rw [h']; exact h.2

/-- **Upper Riemann bound.** If `f ≤ U i` on the `i`-th cell `[a + i h, a + (i+1) h]`, then
`∫_a^{a+Nh} f ≤ Σ h U i`. -/
theorem integral_le_sum_of_cells {f : ℝ → ℝ} {a h : ℝ} (hh : 0 ≤ h) (U : ℕ → ℝ) :
    ∀ N : ℕ, IntervalIntegrable f volume a (a + N * h) →
      (∀ i < N, ∀ x ∈ Icc (a + i * h) (a + (i + 1) * h), f x ≤ U i) →
      ∫ x in a..a + N * h, f x ≤ ∑ i ∈ Finset.range N, h * U i
  | 0, _, _ => by simp
  | N + 1, hint, hU => by
    have hle1 : a ≤ a + N * h := by have : (0 : ℝ) ≤ N * h := by positivity
                                    linarith
    have hle2 : a + N * h ≤ a + ((N + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have hsub1 : IntervalIntegrable f volume a (a + N * h) :=
      hint.mono_set (by rw [uIcc_of_le hle1, uIcc_of_le (hle1.trans hle2)]
                        exact Icc_subset_Icc le_rfl hle2)
    have hsub2 : IntervalIntegrable f volume (a + N * h) (a + ((N + 1 : ℕ) : ℝ) * h) :=
      hint.mono_set (by rw [uIcc_of_le hle2, uIcc_of_le (hle1.trans hle2)]
                        exact Icc_subset_Icc hle1 le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hsub1 hsub2, Finset.sum_range_succ]
    apply add_le_add
    · exact integral_le_sum_of_cells hh U N hsub1 (fun i hi => hU i (by omega))
    · have hm := intervalIntegral.integral_mono_on hle2 hsub2 intervalIntegrable_const
        (fun x hx => hU N (by omega) x (by push_cast at hx ⊢; exact hx))
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      have e : a + ((N + 1 : ℕ) : ℝ) * h - (a + N * h) = h := by push_cast; ring
      rwa [e] at hm

/-- **Lower Riemann bound.** If `L i ≤ f` on the `i`-th cell, then `Σ h L i ≤ ∫_a^{a+Nh} f`. -/
theorem sum_le_integral_of_cells {f : ℝ → ℝ} {a h : ℝ} (hh : 0 ≤ h) (L : ℕ → ℝ) :
    ∀ N : ℕ, IntervalIntegrable f volume a (a + N * h) →
      (∀ i < N, ∀ x ∈ Icc (a + i * h) (a + (i + 1) * h), L i ≤ f x) →
      ∑ i ∈ Finset.range N, h * L i ≤ ∫ x in a..a + N * h, f x := by
  intro N hint hL
  have h1 := integral_le_sum_of_cells (f := fun x => -f x) hh (fun i => -L i) N hint.neg
    (fun i hi x hx => neg_le_neg (hL i hi x hx))
  rw [intervalIntegral.integral_neg] at h1
  simp only [mul_neg, Finset.sum_neg_distrib] at h1
  linarith

/-- **Validated quadrature on `[0, 1]`.** With `N` equal cells and enclosures `c i` valid on
cell `i`, the accumulated enclosure `sumIv c N` bounds `N · 2³² · ∫₀¹ g`. -/
theorem integral_mem_sumIv {g : ℝ → ℝ} {N : ℕ} (hN : 0 < N) (c : ℕ → FIv)
    (hg : IntervalIntegrable g volume 0 1)
    (hc : ∀ i < N, ∀ τ ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N), (c i).Mem (g τ))
    (hok : (sumIv c N).ok = true) :
    ((sumIv c N).lo : ℝ) / (fxScale * N) ≤ ∫ τ in (0 : ℝ)..1, g τ ∧
      ∫ τ in (0 : ℝ)..1, g τ ≤ ((sumIv c N).hi : ℝ) / (fxScale * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hS := fxScale_pos
  have hend : (0 : ℝ) + N * (1 / N) = 1 := by rw [zero_add, mul_one_div_cancel hN'.ne']
  have hcell : ∀ i < N, ∀ x ∈ Icc ((0 : ℝ) + i * (1 / N)) (0 + (i + 1) * (1 / N)),
      fxVal (c i).lo ≤ g x ∧ g x ≤ fxVal (c i).hi := by
    intro i hi x hx
    have e1 : (0 : ℝ) + i * (1 / N) = i / N := by ring
    have e2 : (0 : ℝ) + (i + 1) * (1 / N) = (i + 1) / N := by ring
    have hx' : x ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by rw [e1, e2] at hx; exact hx
    exact hc i hi x hx' (sumIv_ok c N hok i hi)
  have hg' : IntervalIntegrable g volume 0 (0 + N * (1 / N)) := by rw [hend]; exact hg
  have hup := integral_le_sum_of_cells (f := g) (a := 0) (h := 1 / N) (by positivity)
    (fun i => fxVal (c i).hi) N hg' (fun i hi x hx => (hcell i hi x hx).2)
  have hlow := sum_le_integral_of_cells (f := g) (a := 0) (h := 1 / N) (by positivity)
    (fun i => fxVal (c i).lo) N hg' (fun i hi x hx => (hcell i hi x hx).1)
  rw [hend] at hup hlow
  have es : ∀ v : ℕ → ℤ, ∑ i ∈ Finset.range N, (1 / (N : ℝ)) * fxVal (v i) =
      ((∑ i ∈ Finset.range N, v i : ℤ) : ℝ) / (fxScale * N) := by
    intro v
    rw [← Finset.mul_sum]
    unfold fxVal
    rw [← Finset.sum_div]
    push_cast
    field_simp
  rw [es] at hup hlow
  rw [sumIv_lo, sumIv_hi]
  exact ⟨hlow, hup⟩

/-- A Lipschitz-type cell enclosure: if `|f x - f c| ≤ M |x - c|` on `[c - r, c + r]` then
`f c - M r ≤ f x ≤ f c + M r` there. -/
theorem cell_bounds_of_lipschitz {f : ℝ → ℝ} {c r M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (c - r) (c + r), |f x - f c| ≤ M * |x - c|) :
    ∀ x ∈ Icc (c - r) (c + r), f c - M * r ≤ f x ∧ f x ≤ f c + M * r := by
  intro x hx
  have h1 := hM x hx
  have h2 : |x - c| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h3 : M * |x - c| ≤ M * r := mul_le_mul_of_nonneg_left h2 hM0
  have h4 := abs_le.mp (h1.trans h3)
  constructor <;> linarith [h4.1, h4.2]

/-! ## Rational parametrisation of `∫ f(sin t) dt` -/

/-- The rational parametrisation `y(τ) = 2τ/(1+τ²) = sin(2 arctan τ)`. -/
@[expose] noncomputable def wy (τ : ℝ) : ℝ := 2 * τ / (1 + τ ^ 2)

/-- `sin (2 arctan τ) = 2τ/(1+τ²)`. -/
theorem sin_two_arctan (τ : ℝ) : Real.sin (2 * arctan τ) = wy τ := by
  rw [sin_two_mul, sin_arctan, cos_arctan, wy]
  have hs : 0 < √(1 + τ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : √(1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := Real.sq_sqrt (by positivity)
  calc 2 * (τ / √(1 + τ ^ 2)) * (1 / √(1 + τ ^ 2)) = 2 * τ / √(1 + τ ^ 2) ^ 2 := by
        field_simp
    _ = 2 * τ / (1 + τ ^ 2) := by rw [hs2]

/-- `y` is odd. -/
theorem wy_neg (τ : ℝ) : wy (-τ) = -wy τ := by unfold wy; ring

/-- `y` is continuous. -/
theorem continuous_wy : Continuous wy := by
  unfold wy
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)

/-- `|y(τ)| ≤ 1`. -/
theorem wy_mem (τ : ℝ) : wy τ ∈ Icc (-1 : ℝ) 1 := by
  unfold wy
  have h : 0 < 1 + τ ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ h]; nlinarith [sq_nonneg (τ + 1)]
  · rw [div_le_iff₀ h]; nlinarith [sq_nonneg (τ - 1)]

/-- `y` is increasing on `[0, 1]`. -/
theorem wy_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : wy a ≤ wy b := by
  unfold wy
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ (b - a) * (1 - a * b) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith

/-- **Rational substitution.** For `f` continuous on `[-1, 1]`,
`∫_{-π}^{π} f(sin t) dt = 4 ∫₀¹ (f(y τ) + f(-y τ)) / (1 + τ²) dτ`. -/
theorem integral_sin_eq_rational {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    ∫ t in (-π)..π, f (Real.sin t) =
      4 * ∫ τ in (0 : ℝ)..1, (f (wy τ) + f (-wy τ)) / (1 + τ ^ 2) := by
  set g : ℝ → ℝ := fun t => f (Real.sin t) with hgdef
  have hg : Continuous g :=
    hf.comp_continuous Real.continuous_sin (fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩)
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  -- reflections
  have href1 : ∫ t in (π / 2)..π, g t = ∫ t in (0 : ℝ)..(π / 2), g t := by
    have h := intervalIntegral.integral_comp_sub_left g (a := 0) (b := π / 2) π
    have e1 : π - π / 2 = π / 2 := by ring
    rw [e1, sub_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hgdef, Real.sin_pi_sub]
  have href2 : ∫ t in (-π)..(-(π / 2)), g t = ∫ t in (-(π / 2))..0, g t := by
    have h := intervalIntegral.integral_comp_sub_left g (a := -(π / 2)) (b := 0) (-π)
    have e1 : -π - 0 = -π := by ring
    have e2 : -π - -(π / 2) = -(π / 2) := by ring
    rw [e1, e2] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    have hs : Real.sin (-π - x) = Real.sin x := by
      rw [show -π - x = -(x + π) by ring, Real.sin_neg, Real.sin_add_pi, neg_neg]
    simp only [hgdef, hs]
  have hsplit : ∫ t in (-π)..π, g t = 2 * ∫ t in (-(π / 2))..(π / 2), g t := by
    rw [← integral_add_adjacent_intervals (hgi (-π) (-(π / 2))) (hgi (-(π / 2)) π),
      ← integral_add_adjacent_intervals (hgi (-(π / 2)) (π / 2)) (hgi (π / 2) π), href1, href2,
      ← integral_add_adjacent_intervals (hgi (-(π / 2)) 0) (hgi 0 (π / 2))]
    ring
  -- substitution t = 2 arctan τ
  have hsubst : ∫ t in (-(π / 2))..(π / 2), g t =
      ∫ τ in (-1 : ℝ)..1, f (wy τ) * (2 * (1 / (1 + τ ^ 2))) := by
    have hd : ∀ x ∈ uIcc (-1 : ℝ) 1,
        HasDerivAt (fun τ => 2 * arctan τ) (2 * (1 / (1 + x ^ 2))) x :=
      fun x _ => (hasDerivAt_arctan x).const_mul 2
    have hc : ContinuousOn (fun x : ℝ => 2 * (1 / (1 + x ^ 2))) (uIcc (-1 : ℝ) 1) :=
      (Continuous.mul continuous_const
        (Continuous.div continuous_const (by fun_prop) (fun x => by positivity))).continuousOn
    have h : ∫ x in (-1 : ℝ)..1, (g ∘ (fun τ => 2 * arctan τ)) x * (2 * (1 / (1 + x ^ 2))) =
        ∫ x in (2 * arctan (-1))..(2 * arctan 1), g x :=
      intervalIntegral.integral_comp_mul_deriv hd hc hg
    have e1 : 2 * arctan (-1) = -(π / 2) := by rw [arctan_neg, arctan_one]; ring
    have e2 : 2 * arctan 1 = π / 2 := by rw [arctan_one]; ring
    rw [e1, e2] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Function.comp, hgdef, sin_two_arctan]
  -- fold [-1, 0] onto [0, 1]
  set k : ℝ → ℝ := fun τ => f (wy τ) * (2 * (1 / (1 + τ ^ 2))) with hkdef
  have hfw : Continuous (fun τ => f (wy τ)) := hf.comp_continuous continuous_wy wy_mem
  have hfw' : Continuous (fun τ => f (-wy τ)) :=
    hf.comp_continuous continuous_wy.neg (fun τ => by
      have := wy_mem τ; constructor <;> linarith [this.1, this.2])
  have hw : Continuous (fun τ : ℝ => 1 / (1 + τ ^ 2)) :=
    Continuous.div continuous_const (by fun_prop) (fun x => by positivity)
  have hk : Continuous k := hfw.mul (continuous_const.mul hw)
  have hfold : ∫ τ in (-1 : ℝ)..1, k τ = ∫ τ in (0 : ℝ)..1, (k τ + k (-τ)) := by
    rw [← integral_add_adjacent_intervals (hk.intervalIntegrable (-1) 0)
      (hk.intervalIntegrable 0 1)]
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun τ => k τ)
    rw [neg_zero] at h
    have hkn : IntervalIntegrable (fun τ => k (-τ)) volume 0 1 :=
      (hk.comp continuous_neg).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add (hk.intervalIntegrable 0 1) hkn, ← h]
    ring
  rw [hsplit, hsubst, hfold, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  simp only [hkdef, wy_neg, neg_sq]
  have : 0 < 1 + τ ^ 2 := by positivity
  field_simp
  ring

/-! ## Sanity fixtures -/

/-- Accepted fixture: the interval square root of `2` is a valid enclosure, and it contains
`√2`. -/
theorem fixture_sqrt_two : (FIv.ofInt 2).sqrt.ok = true ∧ (FIv.ofInt 2).sqrt.Mem (√2) := by
  refine ⟨by rfl, ?_⟩
  have := FIv.mem_sqrt (FIv.mem_ofInt 2)
  simpa using this

/-- Rejected fixture: inverting an enclosure that contains `0` is flagged invalid. -/
theorem fixture_inv_rejected : (FIv.ofFrac (-1) 2).inv.ok = false := by rfl

/-- Quadrature fixture: four cells give `∫₀¹ x² ≤ Σ (1/4) ((i+1)/4)² = 15/32`. -/
theorem fixture_square_integral : ∫ x in (0 : ℝ)..1, x ^ 2 ≤ 15 / 32 := by
  have h := integral_le_sum_of_cells (f := fun x : ℝ => x ^ 2) (a := 0) (h := 1 / 4)
    (by norm_num) (fun i => (((i : ℝ) + 1) / 4) ^ 2) 4
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (fun i _ x hx => by
      have h0 : 0 ≤ x := le_trans (by positivity) hx.1
      have h1 : x ≤ ((i : ℝ) + 1) / 4 := by
        have := hx.2; simp only [zero_add] at this; linarith
      exact pow_le_pow_left₀ h0 h1 2)
  have e : (0 : ℝ) + ((4 : ℕ) : ℝ) * (1 / 4) = 1 := by norm_num
  have hs : ∑ i ∈ Finset.range 4, (1 / 4 : ℝ) * (((i : ℝ) + 1) / 4) ^ 2 = 15 / 32 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [e, hs] at h
  exact h

/-- Substitution fixture: with `f = 1`, `integral_sin_eq_rational` reproduces
`∫₀¹ 1/(1+τ²) = arctan 1 = π/4`. -/
theorem fixture_arctan_quarter : ∫ τ in (0 : ℝ)..1, 1 / (1 + τ ^ 2) = π / 4 := by
  have h := integral_sin_eq_rational (f := fun _ => (1 : ℝ)) continuousOn_const
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_neg_eq_add] at h
  have e : ∀ τ : ℝ, (1 + 1) / (1 + τ ^ 2) = 2 * (1 / (1 + τ ^ 2)) := fun τ => by ring
  simp only [e, intervalIntegral.integral_const_mul] at h
  linarith

end LeanTheory.Certificates.ValidatedQuadrature
