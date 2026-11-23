/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Taylor enclosures of Fourier profiles on an interface arc

At fixed poloidal angle, each finite Fourier jet of the interface reduces to a
one-dimensional trigonometric polynomial. A fourth-degree expansion at its initial
angle uses just the first five signed moments and one absolute fifth moment.
The bound holds for positive and negative frequencies and arbitrary real phases.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Stability.InterfaceFourierTaylor

open Real Set

/-- The degree-four Taylor polynomial for `cos (a + t)` at `t = 0`. -/
def cosTaylorFour (a t : ℝ) : ℝ :=
  cos a * (1 - t^2/2 + t^4/24) - sin a * (t - t^3/6)

/-- Lagrange's remainder, uniformly in the phase and with signed frequencies allowed. -/
theorem cosTaylorFour_error (a t : ℝ) :
    |cos (a+t) - cosTaylorFour a t| ≤ |t|^5/120 := by
  by_cases h : t = 0
  · simp [h, cosTaylorFour]
  have hne : a ≠ a+t := by intro ha; apply h; linarith
  obtain ⟨y, _, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := cos) (n := 4)
    hne contDiff_cos.contDiffOn
  have hj (n : ℕ) : iteratedDerivWithin n cos (uIcc a (a+t)) a = iteratedDeriv n cos a :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne) contDiff_cos.contDiffAt
      left_mem_uIcc
  have hp : taylorWithinEval cos 4 (uIcc a (a+t)) a (a+t) = cosTaylorFour a t := by
    rw [taylorWithinEval_succ _ 3, taylorWithinEval_succ _ 2, taylorWithinEval_succ _ 1,
      taylorWithinEval_succ _ 0, taylor_within_zero_eval]
    simp only [hj, iteratedDeriv_add_one_cos, iteratedDeriv_add_one_sin]
    norm_num [cosTaylorFour, Nat.factorial]
    ring
  rw [hp] at he
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num [Nat.factorial]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (pow_nonneg (abs_nonneg t) 5) (abs_sin_le_one y)) (by norm_num)

/-- A finite Fourier profile on a real arc differs from its degree-four polynomial
by at most the absolute fifth frequency moment times `|x|^5/120`. -/
theorem sum_cosTaylorFour_error {ι : Type*} (s : Finset ι) (c w a : ι → ℝ) (x : ℝ) :
    |(∑ i ∈ s, c i * cos (a i + w i * x)) -
      ∑ i ∈ s, c i * cosTaylorFour (a i) (w i * x)| ≤
      (∑ i ∈ s, |c i| * |w i|^5) * (|x|^5/120) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_sub, abs_mul]
  have h := mul_le_mul_of_nonneg_left (cosTaylorFour_error (a i) (w i * x)) (abs_nonneg (c i))
  simpa only [abs_mul, mul_pow, div_eq_mul_inv, mul_assoc] using h

end PlasmaLean.Stability.InterfaceFourierTaylor
