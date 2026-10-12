/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Quantitative two-block and perturbation inequalities

Elementary square completion, corresponding to note 05, continuum stability
validation. These inequalities require supplied retained/tail/coupling bounds.
No MHD tail estimate, spectral realization, or physical stability is asserted.
-/
public section

namespace PlasmaLean.Stability

/-- Positive-semidefinite two-by-two algebra, including the singular first pivot. -/
theorem two_block_nonneg {a b g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hg : g ^ 2 ≤ a * b) (x y : ℝ) : 0 ≤ a * x ^ 2 - 2 * g * x * y + b * y ^ 2 := by
  rcases eq_or_lt_of_le ha with h | h
  · have hz : g = 0 := by nlinarith [sq_nonneg g]
    rw [← h, hz]
    nlinarith [mul_nonneg hb (sq_nonneg y)]
  · have hs := sq_nonneg (a * x - g * y)
    have hd := mul_nonneg (sub_nonneg.mpr hg) (sq_nonneg y)
    have he : 0 ≤ a * (a * x ^ 2 - 2 * g * x * y + b * y ^ 2) := by nlinarith
    exact nonneg_of_mul_nonneg_right he h

/-- A proposed margin is valid whenever both shifted diagonal blocks and determinant are. -/
theorem two_block_margin {a b g c : ℝ} (ha : c ≤ a) (hb : c ≤ b)
    (hg : g ^ 2 ≤ (a - c) * (b - c)) (x y : ℝ) :
    c * (x ^ 2 + y ^ 2) ≤ a * x ^ 2 - 2 * g * x * y + b * y ^ 2 := by
  have h := two_block_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb) hg x y
  nlinarith

/-- Exact synthetic example from note 05, with margin one. -/
theorem block_example (x y : ℝ) : x ^ 2 + y ^ 2 ≤ 5 * x ^ 2 - 4 * x * y + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (2 * x - y)]

/-- Transfer a reference lower bound through an error in the same squared gauge. -/
theorem perturbation_margin {q qref c ε s : ℝ}
    (href : c * s ≤ qref) (herr : |q - qref| ≤ ε * s) : (c - ε) * s ≤ q := by
  have h := (abs_le.mp herr).1
  nlinarith

/-- Separate coefficient and equilibrium errors must both be subtracted. -/
theorem combined_error_margin {q qmid qref c ε₁ ε₂ s : ℝ}
    (href : c * s ≤ qref) (h₁ : |qmid - qref| ≤ ε₁ * s)
    (h₂ : |q - qmid| ≤ ε₂ * s) : (c - ε₁ - ε₂) * s ≤ q := by
  exact perturbation_margin (perturbation_margin href h₁) h₂

/-- Positive retained-mode energy alone permits a negative omitted direction. -/
theorem omitted_mode_counterexample :
    (∀ x : ℝ, 0 ≤ x ^ 2 - (0 : ℝ) ^ 2) ∧ (0 : ℝ) ^ 2 - (1 : ℝ) ^ 2 < 0 := by
  constructor
  · intro x; nlinarith [sq_nonneg x]
  · norm_num

end PlasmaLean.Stability
