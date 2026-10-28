/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Example
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Sanity example: the oscillator law is satisfiable, degenerates correctly, and excludes
non-solutions

Every kernel law needs sanity theorems of three kinds; this file supplies them for
`Kernel/Example`:

* **degenerate case**: with zero stiffness (`freeParams`) the law forces constant velocity
  (`free_velocity_const`), so the free particle is recovered;
* **concrete instance**: `cos`/`-sin` obeys the law for the unit oscillator
  (`instOscillatorLawCos`), with energy `1/2` (`cos_energy`). This shows that the law is
  satisfiable, so theorems about it are not vacuous;
* **counterexample**: the trajectory `x = v = exp`, a solution of the *wrong-sign* law
  `x'' = +x`, does not conserve energy (`exp_energy_not_conserved`) and therefore is not an
  instance of the law (`not_oscillatorLaw_exp`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Example

/-- The unit oscillator `m = k = 1`. -/
def unitParams : OscParams := ⟨1, 1, one_pos, zero_le_one⟩

/-- The free particle: `m = 1`, `k = 0`. -/
def freeParams : OscParams := ⟨1, 0, one_pos, le_rfl⟩

/-- **Degenerate case**: with zero stiffness the velocity is constant. -/
theorem free_velocity_const (x v : ℝ → ℝ) [h : OscillatorLaw freeParams x v] (t : ℝ) :
    v t = v 0 := by
  have hd : ∀ s, HasDerivAt v 0 s := fun s => by
    simpa [freeParams] using h.hasDerivAt_v s
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0

/-- **Concrete instance**: `x = cos`, `v = -sin` obeys the unit oscillator law. -/
instance instOscillatorLawCos : OscillatorLaw unitParams Real.cos (fun t => -Real.sin t) where
  hasDerivAt_x t := Real.hasDerivAt_cos t
  hasDerivAt_v t := by
    have h := (Real.hasDerivAt_sin t).neg
    simp only [unitParams, div_one, neg_mul, one_mul]
    exact h

/-- The energy of the concrete instance is `1/2` at every time. -/
theorem cos_energy (t : ℝ) : energy unitParams (Real.cos t) (-Real.sin t) = 1 / 2 := by
  rw [energy_conserved unitParams Real.cos (fun t => -Real.sin t) t]
  simp [energy, unitParams]

/-- The wrong-sign trajectory `x = v = exp` has energy `e^{2t}`, which is not constant. -/
theorem exp_energy_not_conserved :
    energy unitParams (Real.exp 1) (Real.exp 1) ≠ energy unitParams (Real.exp 0) (Real.exp 0) := by
  simp only [energy, unitParams, Real.exp_zero]
  have : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  nlinarith

/-- **Counterexample**: `x = v = exp` (a solution of `x'' = +x`) is not an instance of the
oscillator law, because it would conserve energy. -/
theorem not_oscillatorLaw_exp : ¬ OscillatorLaw unitParams Real.exp Real.exp := by
  intro h
  exact exp_energy_not_conserved (energy_conserved unitParams Real.exp Real.exp 1)

end LeanTheory.Example
