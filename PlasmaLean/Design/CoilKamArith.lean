/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.Diophantine
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Integer approximants for the sampled coil-KAM certificate

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). The sampled residual
certificate evaluates real quantities (trigonometric values at grid angles, torus coordinates,
segment fields) as **approximants**: a pair `(V, e) : ℤ × ℕ` approximates `x : ℝ` at scale `D`
if `|x - V/D| ≤ e/D` (`Approx`). All operations are computable on integers, so the kernel can
evaluate them (`decide +kernel`), and each comes with a soundness lemma proved once:

* `apAdd`, `apSub`, `apNeg`, `apSmul` (exact) and `apMul` (product, rounded down to scale `D`,
  error `(|V₁|e₂ + |V₂|e₁ + e₁e₂)/D + 1`): `Approx.add`, `Approx.sub`, `Approx.neg`,
  `Approx.smul`, `Approx.mul`; sums over lists `Approx.sum`.
* `isqrtF` (Newton's method with fuel and a fixed initial guess, no `Nat.log2`) and the checked
  bracket `sqrtBr n = (A, A+1)` with fallback `(0, n+1)`: `sqrtBr_sound`
  (`lo ≤ √n ≤ hi` always).
* **Grid exponentials** `e^{2πit/L}`: a table `tbl` of Gaussian integers is accepted by the checker
  `expTableOK` if its entry `0` is `D`, entry `1` is within `e₁` of `e^{2πi/L}` and every entry is
  the rounded product of the previous one with entry `1`; `expTableOK_sound` gives
  `‖e^{2πit/L} - tbl_t/D‖ ≤ E/D` for all `t < L`. The base enclosure comes from
  `sqrtTwoAddSeries` brackets (`cos (π/2^{n+1}) = sqrtTwoAddSeries 0 n / 2`, Mathlib):
  `twoAddBr`, `twoAddBr_sound`, `base_exp_approx`.
* `iota_approx`: rational enclosure of `ι_A = (75 + √5)/562` from an integer square check.

**Sanity.** `approx_exact` (zero error), `apMul_one` fixture, `sqrtBr_fixture` (accepted:
`√16 ∈ [4,5]`) and `not_approx_fixture` (rejected: `(0,0)` does not approximate `1`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open Complex

/-! ## Approximants -/

/-- `(V, e)` approximates `x` at scale `D`: `|x - V/D| ≤ e/D`. -/
def Approx (D : ℕ) (x : ℝ) (p : ℤ × ℕ) : Prop := |x - (p.1 : ℝ) / D| ≤ (p.2 : ℝ) / D

/-- Ceiling division of natural numbers. -/
def cdivN (a b : ℕ) : ℕ := (a + (b - 1)) / b

/-- Sum of approximants. -/
def apAdd (p q : ℤ × ℕ) : ℤ × ℕ := (p.1 + q.1, p.2 + q.2)

/-- Negation of an approximant. -/
def apNeg (p : ℤ × ℕ) : ℤ × ℕ := (-p.1, p.2)

/-- Difference of approximants. -/
def apSub (p q : ℤ × ℕ) : ℤ × ℕ := (p.1 - q.1, p.2 + q.2)

/-- Integer multiple of an approximant (exact). -/
def apSmul (n : ℤ) (p : ℤ × ℕ) : ℤ × ℕ := (n * p.1, n.natAbs * p.2)

/-- Product of approximants, rounded down to scale `D`. -/
def apMul (D : ℕ) (p q : ℤ × ℕ) : ℤ × ℕ :=
  (Int.fdiv (p.1 * q.1) D, cdivN (p.1.natAbs * q.2 + q.1.natAbs * p.2 + p.2 * q.2) D + 1)

/-- The bound `|V| + e` (an upper bound of `D |x|`). -/
def apAbs (p : ℤ × ℕ) : ℕ := p.1.natAbs + p.2

theorem natAbs_cast (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  simp only [Nat.cast_natAbs, Int.cast_abs]

theorem cdivN_ge (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdivN a b : ℕ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have h1 : a ≤ cdivN a b * b := by
    unfold cdivN
    have := Nat.lt_div_mul_add (a := a + (b - 1)) hb
    have h2 := Nat.div_mul_le_self (a + (b - 1)) b
    by_contra hc
    push Not at hc
    omega
  exact_mod_cast h1

theorem Approx.abs_le {D : ℕ} (hD : 0 < D) {x : ℝ} {p : ℤ × ℕ} (h : Approx D x p) :
    |x| ≤ (apAbs p : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold Approx at h
  unfold apAbs
  push_cast
  have h1 : |x| ≤ |x - (p.1 : ℝ) / D| + |(p.1 : ℝ) / D| := by
    have := abs_add_le (x - (p.1 : ℝ) / D) ((p.1 : ℝ) / D); simpa using this
  rw [abs_div, Nat.abs_cast] at h1
  rw [add_div, natAbs_cast]
  linarith

theorem approx_exact (D : ℕ) (V : ℤ) : Approx D ((V : ℝ) / D) (V, 0) := by
  simp [Approx]

theorem Approx.add {D : ℕ} {x y : ℝ} {p q : ℤ × ℕ} (hx : Approx D x p) (hy : Approx D y q) :
    Approx D (x + y) (apAdd p q) := by
  unfold Approx at *
  simp only [apAdd, Int.cast_add, Nat.cast_add, add_div]
  calc |x + y - ((p.1 : ℝ) / D + (q.1 : ℝ) / D)|
      = |(x - (p.1 : ℝ) / D) + (y - (q.1 : ℝ) / D)| := by ring_nf
    _ ≤ |x - (p.1 : ℝ) / D| + |y - (q.1 : ℝ) / D| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem Approx.neg {D : ℕ} {x : ℝ} {p : ℤ × ℕ} (hx : Approx D x p) : Approx D (-x) (apNeg p) := by
  unfold Approx at *
  simp only [apNeg, Int.cast_neg, neg_div]
  rw [show -x - -((p.1 : ℝ) / D) = -(x - (p.1 : ℝ) / D) by ring, abs_neg]
  exact hx

theorem Approx.sub {D : ℕ} {x y : ℝ} {p q : ℤ × ℕ} (hx : Approx D x p) (hy : Approx D y q) :
    Approx D (x - y) (apSub p q) := by
  have := hx.add hy.neg
  simpa [apAdd, apNeg, apSub, sub_eq_add_neg] using this

theorem Approx.smul {D : ℕ} (n : ℤ) {x : ℝ} {p : ℤ × ℕ} (hx : Approx D x p) :
    Approx D (n * x) (apSmul n p) := by
  unfold Approx at *
  simp only [apSmul, Int.cast_mul, Nat.cast_mul]
  rw [show (n : ℝ) * x - (n : ℝ) * (p.1 : ℝ) / D = n * (x - (p.1 : ℝ) / D) by ring, abs_mul]
  rw [← natAbs_cast, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

theorem fdiv_approx (z : ℤ) {D : ℕ} (hD : 0 < D) :
    |(z : ℝ) / D / D - ((Int.fdiv z D : ℤ) : ℝ) / D| ≤ 1 / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : ((Int.fdiv z D : ℤ) : ℝ) ≤ (z : ℝ) / D := by
    rw [le_div_iff₀ hD', Int.fdiv_eq_ediv_of_nonneg z (by positivity)]
    have := Int.ediv_mul_le z (by exact_mod_cast hD.ne' : (D : ℤ) ≠ 0)
    exact_mod_cast this
  have h2 : (z : ℝ) / D < ((Int.fdiv z D : ℤ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hD', Int.fdiv_eq_ediv_of_nonneg z (by positivity)]
    have := Int.lt_ediv_add_one_mul_self z (by exact_mod_cast hD : (0 : ℤ) < D)
    exact_mod_cast this
  have e : (z : ℝ) / D / D - ((Int.fdiv z D : ℤ) : ℝ) / D =
      ((z : ℝ) / D - ((Int.fdiv z D : ℤ) : ℝ)) / D := by ring
  rw [e, abs_div, Nat.abs_cast]
  gcongr
  rw [abs_le]; constructor <;> linarith

theorem Approx.mul {D : ℕ} (hD : 0 < D) {x y : ℝ} {p q : ℤ × ℕ} (hx : Approx D x p)
    (hy : Approx D y q) : Approx D (x * y) (apMul D p q) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold Approx at *
  simp only [apMul, Nat.cast_add, Nat.cast_one]
  set V₁ : ℝ := ((p.1 : ℤ) : ℝ); set V₂ : ℝ := ((q.1 : ℤ) : ℝ)
  set e₁ : ℝ := ((p.2 : ℕ) : ℝ); set e₂ : ℝ := ((q.2 : ℕ) : ℝ)
  have hy' : |y| ≤ |V₂| / D + e₂ / D := by
    have := abs_add_le (y - V₂ / D) (V₂ / D)
    rw [sub_add_cancel, abs_div, Nat.abs_cast] at this; linarith
  have hprod : |x * y - V₁ * V₂ / D / D| ≤ (|V₁| * e₂ + |V₂| * e₁ + e₁ * e₂) / D / D := by
    have e : x * y - V₁ * V₂ / D / D = (x - V₁ / D) * y + V₁ / D * (y - V₂ / D) := by
      field_simp; ring
    rw [e]
    calc |(x - V₁ / D) * y + V₁ / D * (y - V₂ / D)|
        ≤ |x - V₁ / D| * |y| + |V₁| / D * |y - V₂ / D| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_div, Nat.abs_cast]
      _ ≤ e₁ / D * (|V₂| / D + e₂ / D) + |V₁| / D * (e₂ / D) := by
          gcongr
      _ = (|V₁| * e₂ + |V₂| * e₁ + e₁ * e₂) / D / D := by field_simp; ring
  have habs₁ : |V₁| = ((p.1.natAbs : ℕ) : ℝ) := (natAbs_cast _).symm
  have habs₂ : |V₂| = ((q.1.natAbs : ℕ) : ℝ) := (natAbs_cast _).symm
  have hc := cdivN_ge (p.1.natAbs * q.2 + q.1.natAbs * p.2 + p.2 * q.2) hD
  push_cast at hc
  have hr := fdiv_approx (p.1 * q.1) hD
  push_cast at hr
  calc |x * y - ((Int.fdiv (p.1 * q.1) D : ℤ) : ℝ) / D|
      ≤ |x * y - V₁ * V₂ / D / D| + |V₁ * V₂ / D / D - ((Int.fdiv (p.1 * q.1) D : ℤ) : ℝ) / D| := by
        have := abs_add_le (x * y - V₁ * V₂ / D / D)
          (V₁ * V₂ / D / D - ((Int.fdiv (p.1 * q.1) D : ℤ) : ℝ) / D)
        simpa using this
    _ ≤ (|V₁| * e₂ + |V₂| * e₁ + e₁ * e₂) / D / D + 1 / D := add_le_add hprod hr
    _ ≤ ((cdivN (p.1.natAbs * q.2 + q.1.natAbs * p.2 + p.2 * q.2) D : ℕ) : ℝ) / D + 1 / D := by
        have hX : (|V₁| * e₂ + |V₂| * e₁ + e₁ * e₂) / D ≤
            ((cdivN (p.1.natAbs * q.2 + q.1.natAbs * p.2 + p.2 * q.2) D : ℕ) : ℝ) := by
          rw [habs₁, habs₂]; exact hc
        exact add_le_add (div_le_div_of_nonneg_right hX hD'.le) le_rfl
    _ = (((cdivN (p.1.natAbs * q.2 + q.1.natAbs * p.2 + p.2 * q.2) D : ℕ) : ℝ) + 1) / D := by
        ring

/-- Sum of a list of approximants. -/
def apSum : List (ℤ × ℕ) → ℤ × ℕ
  | [] => (0, 0)
  | p :: ps => apAdd p (apSum ps)

theorem Approx.sum {D : ℕ} {ι : Type*} (l : List ι) (f : ι → ℝ) (g : ι → ℤ × ℕ)
    (h : ∀ i ∈ l, Approx D (f i) (g i)) : Approx D (l.map f).sum (apSum (l.map g)) := by
  induction l with
  | nil => simp [apSum, Approx]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, apSum]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

/-! ## Square-root brackets -/

/-- Newton's method for `⌊√n⌋` from an initial guess `g ≥ √n`, with fuel. -/
def isqrtF : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f + 1, n, g =>
    match (g + n / g) / 2 with
    | nx => match Nat.blt nx g with
      | true => isqrtF f n nx
      | false => g

/-- The checked bracket `(lo, hi)` of `√n`: `(A, A+1)` if `A² ≤ n < (A+1)²` for the Newton
value `A` started at the guess `g`, else the trivial `(0, n+1)`. -/
def sqrtBr (g n : ℕ) : ℕ × ℕ := sqrtBrOf n (isqrtF 300 n (g + 1))
where
  /-- The bracket from a candidate `A`. -/
  sqrtBrOf (n A : ℕ) : ℕ × ℕ :=
    match Nat.ble (A * A) n && Nat.blt n ((A + 1) * (A + 1)) with
    | true => (A, A + 1)
    | false => (0, n + 1)

theorem sqrtBrOf_sound (n A : ℕ) :
    ((sqrtBr.sqrtBrOf n A).1 : ℝ) ≤ Real.sqrt n ∧ Real.sqrt n ≤ (sqrtBr.sqrtBrOf n A).2 := by
  unfold sqrtBr.sqrtBrOf
  split
  · rename_i h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast (by rw [sq]; exact h1 : A ^ 2 ≤ n)), ?_⟩
    rw [Real.sqrt_le_left (by positivity)]
    push_cast
    exact_mod_cast (by rw [sq]; exact h2.le : n ≤ (A + 1) ^ 2)
  · refine ⟨by simp, ?_⟩
    rw [Real.sqrt_le_left (by positivity)]
    push_cast
    nlinarith

theorem sqrtBr_sound (g n : ℕ) :
    ((sqrtBr g n).1 : ℝ) ≤ Real.sqrt n ∧ Real.sqrt n ≤ (sqrtBr g n).2 :=
  sqrtBrOf_sound n _

/-- Accepted fixture: `√16 ∈ [4, 5]`. -/
theorem sqrtBr_fixture : sqrtBr 8 16 = (4, 5) := by decide +kernel

/-! ## Grid exponentials -/

/-- The grid exponential `e^{2πit/L}`. -/
def gexp (L t : ℕ) : ℂ := Complex.exp (2 * Real.pi * I * t / L)

/-- The Gaussian approximant `(C + S i)/D`. -/
def gauss (D : ℕ) (w : ℤ × ℤ) : ℂ := ((w.1 : ℂ) + w.2 * I) / D

theorem gexp_succ (L t : ℕ) : gexp L (t + 1) = gexp L t * gexp L 1 := by
  unfold gexp; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem norm_gexp (L t : ℕ) : ‖gexp L t‖ = 1 := by
  unfold gexp
  rw [show 2 * (Real.pi : ℂ) * I * t / L = ((2 * Real.pi * t / L : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_gauss_le (D : ℕ) (hD : 0 < D) (w : ℤ × ℤ) :
    ‖gauss D w‖ ≤ ((w.1.natAbs + w.2.natAbs : ℕ) : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold gauss
  rw [norm_div, Complex.norm_natCast]
  gcongr
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast,
    Nat.cast_add, natAbs_cast, natAbs_cast]

/-- Table lookup with default `(0, 0)`. -/
def tget (tbl : List (ℤ × ℤ)) (t : ℕ) : ℤ × ℤ := tbl.getD t (0, 0)

/-- The error recursion of the table: from entry `t` with error `e` to entry `t+1`. -/
def stepErr (D e₁ : ℕ) (w w' w₁ : ℤ × ℤ) (e : ℕ) : ℕ :=
  e + cdivN ((w.1.natAbs + w.2.natAbs) * e₁) D +
    cdivN ((w.1 * w₁.1 - w.2 * w₁.2 - w'.1 * D).natAbs +
      (w.1 * w₁.2 + w.2 * w₁.1 - w'.2 * D).natAbs) D

/-- Walk the table from entry `t` (current error `e`): returns the maximal error. -/
def tableErr (D e₁ : ℕ) (w₁ : ℤ × ℤ) : List (ℤ × ℤ) → ℕ → ℕ
  | [], e => e
  | [_], e => e
  | w :: w' :: ws, e => max e (tableErr D e₁ w₁ (w' :: ws) (stepErr D e₁ w w' w₁ e))

theorem gauss_mul_sub (D : ℕ) (hD : 0 < D) (w w' w₁ : ℤ × ℤ) :
    ‖gauss D w * gauss D w₁ - gauss D w'‖ ≤
      (((w.1 * w₁.1 - w.2 * w₁.2 - w'.1 * D).natAbs +
        (w.1 * w₁.2 + w.2 * w₁.1 - w'.2 * D).natAbs : ℕ) : ℝ) / D / D := by
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have e : gauss D w * gauss D w₁ - gauss D w' =
      ((((w.1 * w₁.1 - w.2 * w₁.2 - w'.1 * D : ℤ) : ℂ)) +
        ((w.1 * w₁.2 + w.2 * w₁.1 - w'.2 * D : ℤ) : ℂ) * I) / D / D := by
    unfold gauss; push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e, norm_div, norm_div, Complex.norm_natCast]
  gcongr
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast,
    Nat.cast_add, natAbs_cast, natAbs_cast]

theorem tableErr_sound (D L e₁ : ℕ) (hD : 0 < D) (w₁ : ℤ × ℤ)
    (h₁ : ‖gexp L 1 - gauss D w₁‖ ≤ (e₁ : ℝ) / D) :
    ∀ (ws : List (ℤ × ℤ)) (t e : ℕ), ‖gexp L t - gauss D (ws.headD (0, 0))‖ ≤ (e : ℝ) / D →
      ∀ i < ws.length, ‖gexp L (t + i) - gauss D (ws.getD i (0, 0))‖ ≤
        (tableErr D e₁ w₁ ws e : ℝ) / D
  | [], t, e, _, i, hi => by simp at hi
  | [w], t, e, h, i, hi => by
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi; simpa [tableErr] using h
  | w :: w' :: ws, t, e, h, i, hi => by
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    rcases i with _ | i
    · simp only [List.headD_cons] at h
      simp only [add_zero, List.getD_cons_zero, tableErr]
      refine h.trans ?_
      gcongr; exact_mod_cast le_max_left _ _
    · -- the error at entry t + 1
      have hstep : ‖gexp L (t + 1) - gauss D w'‖ ≤ (stepErr D e₁ w w' w₁ e : ℝ) / D := by
        simp only [List.headD_cons] at h
        rw [gexp_succ]
        have e1 : gexp L t * gexp L 1 - gauss D w' =
            (gexp L t - gauss D w) * gexp L 1 + gauss D w * (gexp L 1 - gauss D w₁) +
              (gauss D w * gauss D w₁ - gauss D w') := by ring
        rw [e1]
        have hm := gauss_mul_sub D hD w w' w₁
        have hg := norm_gauss_le D hD w
        have hc1 := cdivN_ge ((w.1.natAbs + w.2.natAbs) * e₁) hD
        have hc2 := cdivN_ge ((w.1 * w₁.1 - w.2 * w₁.2 - w'.1 * D).natAbs +
          (w.1 * w₁.2 + w.2 * w₁.1 - w'.2 * D).natAbs) hD
        unfold stepErr
        set A := ‖gexp L t - gauss D w‖
        set G := ‖gauss D w‖
        set B := ‖gexp L 1 - gauss D w₁‖
        set Cm := ‖gauss D w * gauss D w₁ - gauss D w'‖
        set n1 : ℝ := (((w.1.natAbs + w.2.natAbs) * e₁ : ℕ) : ℝ)
        set n2 : ℝ := (((w.1 * w₁.1 - w.2 * w₁.2 - w'.1 * D).natAbs +
          (w.1 * w₁.2 + w.2 * w₁.1 - w'.2 * D).natAbs : ℕ) : ℝ)
        have hG0 : 0 ≤ G := norm_nonneg _
        have hGB : G * B ≤ n1 / D / D := by
          have h3 : G * B ≤ ((w.1.natAbs + w.2.natAbs : ℕ) : ℝ) / D * ((e₁ : ℝ) / D) :=
            mul_le_mul hg h₁ (norm_nonneg _) (by positivity)
          refine h3.trans (le_of_eq ?_)
          simp only [n1]; push_cast; field_simp
        have t2 : n1 / D / D ≤ ((cdivN ((w.1.natAbs + w.2.natAbs) * e₁) D : ℕ) : ℝ) / D :=
          div_le_div_of_nonneg_right hc1 hD'.le
        have t3 : n2 / D / D ≤ ((cdivN ((w.1 * w₁.1 - w.2 * w₁.2 - w'.1 * D).natAbs +
            (w.1 * w₁.2 + w.2 * w₁.1 - w'.2 * D).natAbs) D : ℕ) : ℝ) / D :=
          div_le_div_of_nonneg_right hc2 hD'.le
        have hsum : ‖(gexp L t - gauss D w) * gexp L 1 + gauss D w * (gexp L 1 - gauss D w₁) +
              (gauss D w * gauss D w₁ - gauss D w')‖ ≤ A + G * B + Cm := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
          rw [norm_mul, norm_mul, norm_gexp, mul_one]
        refine hsum.trans ?_
        push_cast
        rw [add_div, add_div]
        have : Cm ≤ n2 / D / D := hm
        linarith
      have := tableErr_sound D L e₁ hD w₁ h₁ (w' :: ws) (t + 1) _ (by simpa using hstep) i
        (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [show t + (i + 1) = t + 1 + i by ring]
      refine this.trans ?_
      gcongr
      simp only [tableErr]
      exact_mod_cast le_max_right _ _

/-- **The table checker**: entry `0` is `(D, 0)` and the maximal error is at most `E`. -/
def expTableOK (D L e₁ E : ℕ) (tbl : List (ℤ × ℤ)) : Bool :=
  tbl.length == L && tget tbl 0 == ((D : ℤ), 0) && Nat.ble (tableErr D e₁ (tget tbl 1) tbl 0) E

theorem expTableOK_sound {D L e₁ E : ℕ} (hD : 0 < D) {tbl : List (ℤ × ℤ)}
    (h₁ : ‖gexp L 1 - gauss D (tget tbl 1)‖ ≤ (e₁ : ℝ) / D) (h : expTableOK D L e₁ E tbl = true) :
    ∀ t < L, ‖gexp L t - gauss D (tget tbl t)‖ ≤ (E : ℝ) / D := by
  simp only [expTableOK, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
  obtain ⟨⟨hlen, h0⟩, hE⟩ := h
  intro t ht
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hstart : ‖gexp L 0 - gauss D (tbl.headD (0, 0))‖ ≤ ((0 : ℕ) : ℝ) / D := by
    have : tbl.headD (0, 0) = ((D : ℤ), 0) := by
      rw [← h0]; cases tbl <;> simp [tget]
    rw [this]
    have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    simp [gexp, gauss, hD0]
  have := tableErr_sound D L e₁ hD (tget tbl 1) h₁ tbl 0 0 hstart t (by omega)
  rw [zero_add] at this
  exact this.trans (div_le_div_of_nonneg_right (by exact_mod_cast hE) hD'.le)

/-! ## The base exponential `e^{2πi/L}` from `sqrtTwoAddSeries` -/

/-- Brackets `(lo, hi)` of `D · sqrtTwoAddSeries 0 n` (`n` nested square roots). -/
def twoAddBr (D : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
    match twoAddBr D n with
    | (lo, hi) => ((sqrtBr (2 * D) ((2 * D + lo) * D)).1, (sqrtBr (2 * D) ((2 * D + hi) * D)).2)

theorem twoAddBr_sound (D : ℕ) (hD : 0 < D) : ∀ n,
    ((twoAddBr D n).1 : ℝ) ≤ D * Real.sqrtTwoAddSeries 0 n ∧
      D * Real.sqrtTwoAddSeries 0 n ≤ (twoAddBr D n).2
  | 0 => by simp [twoAddBr]
  | n + 1 => by
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    obtain ⟨h1, h2⟩ := twoAddBr_sound D hD n
    have hs := Real.sqrtTwoAddSeries_zero_nonneg n
    simp only [twoAddBr, Real.sqrtTwoAddSeries]
    have e : (D : ℝ) * Real.sqrt (2 + Real.sqrtTwoAddSeries 0 n) =
        Real.sqrt ((2 * D + D * Real.sqrtTwoAddSeries 0 n) * D) := by
      rw [show (2 * (D : ℝ) + D * Real.sqrtTwoAddSeries 0 n) * D =
        (2 + Real.sqrtTwoAddSeries 0 n) * (D * D) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_mul_self hD'.le, mul_comm]
    rw [e]
    obtain ⟨l1, _⟩ := sqrtBr_sound (2 * D) ((2 * D + (twoAddBr D n).1) * D)
    obtain ⟨_, u2⟩ := sqrtBr_sound (2 * D) ((2 * D + (twoAddBr D n).2) * D)
    push_cast at l1 u2
    constructor
    · exact l1.trans (Real.sqrt_le_sqrt (by gcongr))
    · exact (Real.sqrt_le_sqrt (by gcongr)).trans u2

/-- `‖x + yi - (C + Si)/D‖ ≤ (eC + eS)/D` from `|Dx - C| ≤ eC`, `|Dy - S| ≤ eS`. -/
theorem norm_sub_gauss_le {D : ℕ} (hD : 0 < D) (x y : ℝ) (C S : ℤ) (eC eS : ℕ)
    (hx : |(D : ℝ) * x - C| ≤ eC) (hy : |(D : ℝ) * y - S| ≤ eS) :
    ‖(x : ℂ) + y * I - gauss D (C, S)‖ ≤ ((eC + eS : ℕ) : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : ((x : ℂ) + y * I - gauss D (C, S)).re = x - C / D := by
    simp [gauss, Complex.div_natCast_re]
  have him : ((x : ℂ) + y * I - gauss D (C, S)).im = y - S / D := by
    simp [gauss, Complex.div_natCast_im]
  rw [hre, him]
  have e1 : x - C / D = ((D : ℝ) * x - C) / D := by field_simp
  have e2 : y - S / D = ((D : ℝ) * y - S) / D := by field_simp
  rw [e1, e2, abs_div, abs_div, Nat.abs_cast, ← add_div]
  push_cast
  exact div_le_div_of_nonneg_right (add_le_add hx hy) hD'.le

/-- The real and imaginary parts of the grid exponential. -/
theorem gexp_eq (L t : ℕ) :
    gexp L t = Real.cos (2 * Real.pi * t / L) + Real.sin (2 * Real.pi * t / L) * I := by
  unfold gexp
  rw [show 2 * (Real.pi : ℂ) * I * t / L = ((2 * Real.pi * t / L : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast; ring

/-- **Base enclosure** for `L = 2^(n+2)`: with `(lo, hi)` the brackets of
`D sqrtTwoAddSeries 0 n` and `(lo', hi')` those of `D sqrtTwoAddSeries 0 (n-1)` (for `n ≥ 1`),
the table entry `w₁ = (C, S)` is within `e₁/D` of `e^{2πi/L}` if
`|2C - lo|, |2C - hi| ≤ 2 eC` and the analogous condition holds for `S` against the brackets of
`D√(2 - s_{n-1})`. -/
theorem base_exp_approx (D n : ℕ) (hD : 0 < D) (C S : ℤ) (eC eS : ℕ)
    (hc : ∀ x : ℝ, ((twoAddBr D (n + 1)).1 : ℝ) ≤ x → x ≤ (twoAddBr D (n + 1)).2 →
      |x / 2 - C| ≤ eC)
    (hs : ∀ x : ℝ,
      ((sqrtBr (2 * D) ((2 * D - (twoAddBr D n).2) * D)).1 : ℝ) ≤ x →
      x ≤ (sqrtBr (2 * D) ((2 * D - (twoAddBr D n).1) * D)).2 → |x / 2 - S| ≤ eS)
    (hn : (twoAddBr D n).2 ≤ 2 * D) :
    ‖gexp (2 ^ (n + 3)) 1 - gauss D (C, S)‖ ≤ ((eC + eS : ℕ) : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hang : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((2 ^ (n + 3) : ℕ) : ℝ) = Real.pi / 2 ^ (n + 2) := by
    push_cast; rw [pow_succ]; field_simp
  rw [gexp_eq, hang]
  have hcos : Real.cos (Real.pi / 2 ^ (n + 1 + 1)) = Real.sqrtTwoAddSeries 0 (n + 1) / 2 :=
    Real.cos_pi_over_two_pow (n + 1)
  have hsin : Real.sin (Real.pi / 2 ^ (n + 2)) = Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 :=
    Real.sin_pi_over_two_pow_succ n
  rw [show n + 1 + 1 = n + 2 by ring] at hcos
  rw [hcos, hsin]
  obtain ⟨c1, c2⟩ := twoAddBr_sound D hD (n + 1)
  obtain ⟨s1, s2⟩ := twoAddBr_sound D hD n
  have hC := hc _ c1 c2
  -- the sine: D √(2 - s) = √((2D - D s) D)
  have es : (D : ℝ) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) =
      Real.sqrt ((2 * D - D * Real.sqrtTwoAddSeries 0 n) * D) := by
    rw [show (2 * (D : ℝ) - D * Real.sqrtTwoAddSeries 0 n) * D =
      (2 - Real.sqrtTwoAddSeries 0 n) * (D * D) by ring, Real.sqrt_mul' _ (by positivity),
      Real.sqrt_mul_self hD'.le, mul_comm]
  have hsl := (sqrtBr_sound (2 * D) ((2 * D - (twoAddBr D n).2) * D)).1
  have hsu := (sqrtBr_sound (2 * D) ((2 * D - (twoAddBr D n).1) * D)).2
  have hlo : ((2 * D - (twoAddBr D n).2 : ℕ) : ℝ) = 2 * D - (twoAddBr D n).2 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  have hle1 : (twoAddBr D n).1 ≤ 2 * D := by
    have : ((twoAddBr D n).1 : ℝ) ≤ 2 * D := by
      have := Real.sqrtTwoAddSeries_lt_two n; nlinarith
    exact_mod_cast this
  have hhi : ((2 * D - (twoAddBr D n).1 : ℕ) : ℝ) = 2 * D - (twoAddBr D n).1 := by
    rw [Nat.cast_sub hle1]; push_cast; ring
  push_cast [hlo, hhi] at hsl hsu
  have hS := hs (D * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))
    (by rw [es]; exact hsl.trans (Real.sqrt_le_sqrt (by gcongr)))
    (by rw [es]; exact (Real.sqrt_le_sqrt (by gcongr)).trans hsu)
  have h1 : |(D : ℝ) * (Real.sqrtTwoAddSeries 0 (n + 1) / 2) - C| ≤ eC := by
    rw [show (D : ℝ) * (Real.sqrtTwoAddSeries 0 (n + 1) / 2) =
      (D * Real.sqrtTwoAddSeries 0 (n + 1)) / 2 by ring]; exact hC
  have h2 : |(D : ℝ) * (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2) - S| ≤ eS := by
    rw [show (D : ℝ) * (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2) =
      (D * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n)) / 2 by ring]; exact hS
  exact norm_sub_gauss_le hD _ _ C S eC eS h1 h2

/-! ## The rotational transform -/

/-- **Enclosure of `ι_A`**: if `(562 I - 75 D)² ≤ 5 D² ≤ (562 (I+1) - 75 D)²` with
`562 I ≥ 75 D`, then `|ι_A - I/D| ≤ 1/D`. -/
theorem iota_approx {D : ℕ} (hD : 0 < D) {I : ℤ} (h0 : 75 * (D : ℤ) ≤ 562 * I)
    (h1 : (562 * I - 75 * D) ^ 2 ≤ 5 * (D : ℤ) ^ 2)
    (h2 : 5 * (D : ℤ) ^ 2 ≤ (562 * (I + 1) - 75 * D) ^ 2) :
    Approx D PlasmaLean.Theory.KAM.torusAIota (I, 1) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold Approx PlasmaLean.Theory.KAM.torusAIota
  have h0' : (75 : ℝ) * D ≤ 562 * I := by exact_mod_cast h0
  have h1' : ((562 : ℝ) * I - 75 * D) ^ 2 ≤ 5 * (D : ℝ) ^ 2 := by exact_mod_cast h1
  have h2' : 5 * (D : ℝ) ^ 2 ≤ (562 * ((I : ℝ) + 1) - 75 * D) ^ 2 := by exact_mod_cast h2
  have hs5 : Real.sqrt 5 * D = Real.sqrt (5 * (D : ℝ) ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hD'.le]
  have lo : (562 : ℝ) * I - 75 * D ≤ Real.sqrt 5 * D := by
    rw [hs5]; exact Real.le_sqrt_of_sq_le h1'
  have hpos : 0 ≤ (562 : ℝ) * ((I : ℝ) + 1) - 75 * D := by linarith
  have hi : Real.sqrt 5 * D ≤ 562 * ((I : ℝ) + 1) - 75 * D := by
    rw [hs5]; exact Real.sqrt_le_iff.2 ⟨hpos, h2'⟩
  have hl : (I : ℝ) / D ≤ (75 + Real.sqrt 5) / 562 := by
    rw [div_le_div_iff₀ hD' (by norm_num)]; nlinarith
  have hu : (75 + Real.sqrt 5) / 562 ≤ ((I : ℝ) + 1) / D := by
    rw [div_le_div_iff₀ (by norm_num) hD']; nlinarith
  have hu' : ((I : ℝ) + 1) / D = (I : ℝ) / D + 1 / D := by ring
  have h1D : 0 ≤ (1 : ℝ) / D := by positivity
  simp only [Nat.cast_one]
  rw [abs_le]
  constructor <;> linarith

/-! ## Sanity -/

/-- `1 · 1 = 1` at scale `4` (fixture for `apMul`). -/
theorem apMul_one : apMul 4 (4, 0) (4, 0) = (4, 1) := by decide +kernel

/-- Rejected fixture: `(0, 0)` does not approximate `1`. -/
theorem not_approx_fixture : ¬ Approx 1 1 (0, 0) := by
  simp [Approx]

end PlasmaLean.Design.CoilKam
