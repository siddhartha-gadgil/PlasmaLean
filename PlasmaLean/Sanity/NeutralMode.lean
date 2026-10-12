/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A neutral mode does not control displacement

The scalar equation x''=0 has x(t)=t, v(t)=1, constant kinetic energy, and
unbounded displacement for t≥0. Thus nonnegative potential energy alone cannot
imply a uniform displacement bound. This is a counterexample, not an instability
claim for a specified MHD equilibrium. Quotient-space dynamics remain separate.
-/
public section

namespace PlasmaLean.Sanity

/-- The free-particle curve satisfies the zero-acceleration equation for all time. -/
theorem neutral_solution (t : ℝ) :
    HasDerivAt (fun s : ℝ => s) 1 t ∧ HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t :=
  ⟨hasDerivAt_id t, hasDerivAt_const t 1⟩

/-- The potential form is nonnegative and the total energy constant, but the actual
zero-acceleration solution has no uniform displacement bound on the half-line. -/
theorem neutral_energy_does_not_control_displacement :
    (∀ x : ℝ, 0 ≤ 0 * x ^ 2) ∧
    (∀ t : ℝ, ((1 : ℝ) ^ 2 + 0 * t ^ 2) / 2 = 1 / 2) ∧
    ∀ R : ℝ, ∃ t : ℝ, 0 ≤ t ∧ R < |t| := by
  refine ⟨by intro x; simp, by intro t; ring, ?_⟩
  intro R
  refine ⟨|R| + 1, by linarith [abs_nonneg R], ?_⟩
  rw [abs_of_nonneg (by linarith [abs_nonneg R] : 0 ≤ |R| + 1)]
  linarith [le_abs_self R]

end PlasmaLean.Sanity
