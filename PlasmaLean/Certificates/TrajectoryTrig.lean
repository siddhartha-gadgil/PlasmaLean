/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.TrajectoryTaylorModel
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Trigonometric Taylor models on a normalized physical clock

The clock is the real affine function `a + w s` on `|s| ≤ 1`. An exact
rational Taylor polynomial and an analytic remainder bound provide an
independent comparison for rounded angle-model coefficients.
-/

@[expose] public section
namespace PlasmaLean.Certificates.TrajectoryTrig

open Real Set QPoly TrajectoryTaylorModel

/-- Select sine or cosine of the physical angle. -/
noncomputable def wave : Bool → ℝ → ℝ
  | true => sin
  | false => cos

/-- Successive derivatives at zero of the two real trigonometric functions. -/
def originDerivative : ℕ → Bool → ℚ
  | 0, true => 0
  | 0, false => 1
  | n + 1, true => originDerivative n false
  | n + 1, false => -originDerivative n true

private theorem deriv_origin (n : ℕ) (sine : Bool) :
    iteratedDeriv n (wave sine) 0 = (originDerivative n sine : ℝ) := by
  induction n generalizing sine with
  | zero => cases sine <;> simp [wave, originDerivative]
  | succ n ih =>
    cases sine
    · simpa [wave, originDerivative, iteratedDeriv_add_one_cos] using congrArg Neg.neg (ih true)
    · simpa [wave, originDerivative, iteratedDeriv_add_one_sin] using ih false

private theorem abs_deriv (n : ℕ) (sine : Bool) (x : ℝ) :
    |iteratedDeriv n (wave sine) x| ≤ 1 := by
  induction n generalizing sine with
  | zero => cases sine <;> simp [wave, abs_cos_le_one, abs_sin_le_one]
  | succ n ih =>
    cases sine
    · simpa [wave, iteratedDeriv_add_one_cos] using ih true
    · simpa [wave, iteratedDeriv_add_one_sin] using ih false

/-- The ordinary Taylor polynomial about zero through degree `n`. -/
def poly (sine : Bool) : ℕ → List ℚ
  | 0 => [originDerivative 0 sine]
  | n + 1 => poly sine n ++ [originDerivative (n+1) sine / (n+1).factorial]

private theorem poly_length (sine : Bool) (n : ℕ) : (poly sine n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [poly, ih]

private theorem eval_append (p q : List ℚ) (x : ℝ) :
    eval (p ++ q) x = eval p x + x^p.length * eval q x := by
  induction p with
  | nil => simp
  | cons c p ih =>
    simp only [List.cons_append, eval_cons, ih, List.length_cons, pow_succ]
    ring

private theorem eval_at_zero (sine : Bool) (n : ℕ) :
    eval (poly sine n) 0 = wave sine 0 := by
  induction n with
  | zero => cases sine <;> simp [wave, poly, originDerivative]
  | succ n ih => simp [poly, eval_append, poly_length, ih]

/-- Uniform real Lagrange remainder, valid for every degree and either sign of input. -/
theorem taylor_error (sine : Bool) (n : ℕ) (x : ℝ) :
    |wave sine x - eval (poly sine n) x| ≤ |x|^(n+1) / (n+1).factorial := by
  by_cases hx : 0 = x
  · subst x
    simp [eval_at_zero]
  have smooth : ContDiff ℝ ⊤ (wave sine) := by
    cases sine <;> first | exact contDiff_sin | exact contDiff_cos
  have ders (i : ℕ) : iteratedDerivWithin i (wave sine) (uIcc 0 x) 0 =
      (originDerivative i sine : ℝ) :=
    (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
      (smooth.of_le (m := i) (by simp)).contDiffAt left_mem_uIcc).trans (deriv_origin i sine)
  have expansion (i : ℕ) :
      taylorWithinEval (wave sine) i (uIcc 0 x) 0 x = eval (poly sine i) x := by
    induction i with
    | zero =>
      rw [taylor_within_zero_eval]
      simpa [poly] using deriv_origin 0 sine
    | succ i ih =>
      rw [taylorWithinEval_succ, ih, poly, eval_append, poly_length, ders]
      simp only [eval_cons, eval_nil, mul_zero, add_zero, sub_zero, smul_eq_mul, Nat.factorial_succ]
      push_cast
      ring
  obtain ⟨y, _, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hx
    ((smooth.of_le (m := (n+1 : ℕ)) (by simp)).contDiffOn)
  rw [expansion] at h
  rw [h, abs_div, abs_mul, abs_pow, sub_zero,
    abs_of_nonneg (by positivity : 0 ≤ ((n+1).factorial : ℝ))]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) _) (abs_deriv _ _ _)) (by positivity)

/-- Substitute the rational affine clock into a polynomial in ascending coefficient order. -/
def affine (a w : ℚ) : List ℚ → List ℚ
  | [] => []
  | c :: p => add [c] (mul [a,w] (affine a w p))

private theorem eval_affine (a w : ℚ) (p : List ℚ) (s : ℝ) :
    eval (affine a w p) s = eval p ((a : ℝ) + w*s) := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [affine, ih, mul_comm]

/-- Exact polynomial and rational uniform remainder on the normalized slab. -/
def comparison (sine : Bool) (n : ℕ) (a w : ℚ) : Model :=
  ⟨affine a w (poly sine n), (|a| + |w|)^(n+1) / (n+1).factorial⟩

/-- The real trigonometric value satisfies the computed comparison model on the whole slab. -/
theorem comparison_mem (sine : Bool) (n : ℕ) (a w : ℚ) {s : ℝ} (hs : |s| ≤ 1) :
    (comparison sine n a w).Mem s (wave sine ((a : ℝ) + w*s)) := by
  unfold comparison Model.Mem
  simp only [eval_affine, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_abs, Rat.cast_natCast]
  apply (taylor_error sine n _).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (abs_nonneg _)
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hs)

/-- Exact rational arithmetic can transfer the comparison to any emitted model, including
polynomials of lower degree with rounded coefficients. -/
theorem fit (sine : Bool) (n : ℕ) (a w : ℚ) (m : Model)
    (checked : (comparison sine n a w).radius +
      magnitude (difference (comparison sine n a w).poly m.poly) ≤ m.radius)
    {s : ℝ} (hs : |s| ≤ 1) : m.Mem s (wave sine ((a : ℝ) + w*s)) :=
  enclose hs (comparison_mem sine n a w hs) checked

/-- Check a point value using scalar Horner evaluation of the Taylor polynomial. -/
theorem centre_error (sine : Bool) (n : ℕ) (a c r : ℚ)
    (checked : |a| ^ (n + 1) / (n + 1).factorial + |evalQ (poly sine n) a - c| ≤ r) :
    |wave sine (a : ℝ) - c| ≤ (r : ℝ) := by
  have h := (abs_sub_le (wave sine (a : ℝ)) (eval (poly sine n) a) (c : ℝ)).trans
    (add_le_add (taylor_error sine n a) le_rfl)
  rw [eval_cast] at h
  exact h.trans (by exact_mod_cast checked)

/-- An enclosure of an angle component independent of normalized slab time. -/
def constant (c r : ℚ) : Model := ⟨[c], r⟩

private theorem mem_const {c r : ℚ} {x : ℝ} (h : |x - c| ≤ r) (s : ℝ) :
    (constant c r).Mem s x := by simpa [Model.Mem, constant] using h

/-- Negate the polynomial centre of a model, retaining its error radius. -/
def negative (m : Model) : Model := ⟨scale (-1) m.poly, m.radius⟩

private theorem mem_neg {m : Model} {s x : ℝ} (hm : m.Mem s x) :
    (negative m).Mem s (-x) := by
  change |-x - eval (scale (-1) m.poly) s| ≤ _
  rw [eval_scale]
  simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_sub_neg]
  rw [abs_sub_comm]
  exact hm

/-- Compose an independently enclosed centre with a Taylor expansion on the short
increment. This keeps the expensive high-order Taylor check scalar at long times. -/
def rotated (sine : Bool) (c0 s0 : Model) (degree : ℕ) (w : ℚ) : Model :=
  let cd := comparison false degree 0 w
  let sd := comparison true degree 0 w
  if sine then addModel (mulModel s0 cd) (mulModel c0 sd)
  else addModel (mulModel c0 cd) (mulModel (negative s0) sd)

/-- The addition formulas propagate certified centre components along an entire slab. -/
theorem rotated_mem (sine : Bool) (degree : ℕ) {a s : ℝ} (w : ℚ) (hs : |s| ≤ 1)
    {c0 s0 : Model} (hc : c0.Mem s (cos a)) (hn : s0.Mem s (sin a)) :
    (rotated sine c0 s0 degree w).Mem s (wave sine (a + w*s)) := by
  have hx : (comparison false degree 0 w).Mem s (cos (w*s)) := by
    simpa [wave] using comparison_mem false degree 0 w hs
  have hy : (comparison true degree 0 w).Mem s (sin (w*s)) := by
    simpa [wave] using comparison_mem true degree 0 w hs
  cases sine
  · simpa only [rotated, Bool.false_eq_true, ite_false, wave, cos_add,
      sub_eq_add_neg, neg_mul] using
      mem_add (mem_mul hs hc hx) (mem_mul hs (mem_neg hn) hy)
  · simpa only [rotated, ite_true, wave, sin_add] using
      mem_add (mem_mul hs hn hx) (mem_mul hs hc hy)

/-- A single low-order polynomial on the increment proves the emitted enclosure
for any centre, once the two real trigonometric values there have been enclosed. -/
theorem fit_at_centre (sine : Bool) (degree : ℕ) {a : ℝ} (w : ℚ) {c r z v : ℚ}
    (hc : |cos a - c| ≤ r) (hz : |sin a - z| ≤ v) (m : Model)
    (checked : let ref := rotated sine (constant c r) (constant z v) degree w
      ref.radius + magnitude (difference ref.poly m.poly) ≤ m.radius)
    {s : ℝ} (hs : |s| ≤ 1) : m.Mem s (wave sine (a + w*s)) :=
  enclose hs (rotated_mem sine degree w hs (mem_const hc s) (mem_const hz s)) checked

/-- At the opposite Dommaschk section each harmonic has the sign used by the
shifted field tables. The trace parameter `t` is signed geometric azimuth. -/
theorem opposite_section (sine : Bool) (k : ℕ) (t : ℝ) :
    wave sine (2 * k * (π / 2 + t)) = (-1 : ℝ)^k * wave sine (2*k*t) := by
  rw [show 2 * (k : ℝ) * (π / 2 + t) = k*π + 2*k*t by ring]
  cases sine <;> simp [wave, sin_add, cos_add, sin_nat_mul_pi, cos_nat_mul_pi]

end PlasmaLean.Certificates.TrajectoryTrig
