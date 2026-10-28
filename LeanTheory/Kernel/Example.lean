/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Kernel example: the one-dimensional harmonic oscillator

A worked example of a **kernel** file. A kernel file states the model *law* as a typeclass
(a hypothesis that a given object satisfies), never as an `axiom`. Theorems are then proved
for every object satisfying the law, and sanity files (`Sanity/Example`) check that the law is
satisfiable, has the expected degenerate cases, and excludes non-solutions.

* `OscParams`: mass `m > 0` and stiffness `k ≥ 0`;
* `energy p x v = m v² / 2 + k x² / 2`;
* `OscillatorLaw p x v`: the trajectory `t ↦ (x t, v t)` satisfies Newton's law
  `x' = v`, `m v' = -k x` for all times;
* `energy_conserved`: along every trajectory obeying the law, the energy is constant;
* `potential_le_energy`: the potential part is bounded by the (conserved) energy.

Scope: a model contract only. Nothing here asserts that any physical system obeys the law; such
claims belong to bridge files with explicit hypotheses.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Example

/-- Parameters of a one-dimensional harmonic oscillator: mass `m > 0`, stiffness `k ≥ 0`. -/
structure OscParams where
  /-- The mass. -/
  m : ℝ
  /-- The stiffness (spring constant). -/
  k : ℝ
  /-- The mass is positive. -/
  m_pos : 0 < m
  /-- The stiffness is nonnegative. -/
  k_nonneg : 0 ≤ k

/-- The total energy `m v² / 2 + k x² / 2` at position `x` and velocity `v`. -/
def energy (p : OscParams) (x v : ℝ) : ℝ := p.m / 2 * v ^ 2 + p.k / 2 * x ^ 2

/-- **Model law** (a typeclass, not an axiom): the trajectory `(x, v)` obeys Newton's law
`x' = v`, `m v' = -k x` at every time. -/
class OscillatorLaw (p : OscParams) (x v : ℝ → ℝ) : Prop where
  /-- The velocity is the derivative of the position. -/
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  /-- Newton's law: `v' = -(k / m) x`. -/
  hasDerivAt_v : ∀ t, HasDerivAt v (-(p.k / p.m) * x t) t

/-- The energy is nonnegative. -/
theorem energy_nonneg (p : OscParams) (x v : ℝ) : 0 ≤ energy p x v := by
  unfold energy
  have := p.m_pos.le
  have := p.k_nonneg
  positivity

/-- Along a trajectory obeying the law, the energy has derivative zero. -/
theorem hasDerivAt_energy (p : OscParams) (x v : ℝ → ℝ) [h : OscillatorLaw p x v] (t : ℝ) :
    HasDerivAt (fun s => energy p (x s) (v s)) 0 t := by
  have hd := (((h.hasDerivAt_v t).pow 2).const_mul (p.m / 2)).add
    (((h.hasDerivAt_x t).pow 2).const_mul (p.k / 2))
  have hm : p.m ≠ 0 := p.m_pos.ne'
  have h0 : p.m / 2 * ((2 : ℕ) * v t ^ (2 - 1) * (-(p.k / p.m) * x t)) +
      p.k / 2 * ((2 : ℕ) * x t ^ (2 - 1) * v t) = 0 := by
    field_simp
    ring
  rw [h0] at hd
  exact hd

/-- **Energy conservation**: along every trajectory obeying the law, the energy at time `t`
equals the initial energy. -/
theorem energy_conserved (p : OscParams) (x v : ℝ → ℝ) [OscillatorLaw p x v] (t : ℝ) :
    energy p (x t) (v t) = energy p (x 0) (v 0) :=
  is_const_of_deriv_eq_zero (fun s => (hasDerivAt_energy p x v s).differentiableAt)
    (fun s => (hasDerivAt_energy p x v s).deriv) t 0

/-- The potential energy `k x² / 2` is at most the total energy. -/
theorem potential_le_energy (p : OscParams) (x v : ℝ) : p.k / 2 * x ^ 2 ≤ energy p x v := by
  unfold energy
  have := p.m_pos.le
  have : 0 ≤ p.m / 2 * v ^ 2 := by positivity
  linarith

end LeanTheory.Example
