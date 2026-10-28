/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Example

/-!
# Bridge example: composing the oscillator law with other results

A **bridge** file connects kernel laws to each other and to theory or certificate results,
with every hypothesis explicit. For the oscillator of `Kernel/Example`:

* `OscillatorLaw.shift`: the law is invariant under time translation;
* `OscillatorLaw.add`, `OscillatorLaw.smul`: superposition, the law is linear;
* `energy_eq_of_law`: the energies at any two times agree (conservation composed with the time
  shift);
* **`amplitude_bound`**: conservation composed with `potential_le_energy`: if the initial energy
  is at most `E`, then `k x(t)² ≤ 2E` for all `t`. A certificate on the initial data (see
  `Certificates/Example`) then yields a concrete amplitude bound.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Example

/-- **Time translation**: a time-shifted solution is a solution. -/
theorem OscillatorLaw.shift {p : OscParams} {x v : ℝ → ℝ} (h : OscillatorLaw p x v) (s : ℝ) :
    OscillatorLaw p (fun t => x (t + s)) (fun t => v (t + s)) where
  hasDerivAt_x t := by
    have hc := (h.hasDerivAt_x (t + s)).comp t ((hasDerivAt_id t).add_const s)
    simpa [Function.comp_def] using hc
  hasDerivAt_v t := by
    have hc := (h.hasDerivAt_v (t + s)).comp t ((hasDerivAt_id t).add_const s)
    simpa [Function.comp_def] using hc

/-- **Superposition**: the sum of two solutions is a solution. -/
theorem OscillatorLaw.add {p : OscParams} {x₁ v₁ x₂ v₂ : ℝ → ℝ} (h₁ : OscillatorLaw p x₁ v₁)
    (h₂ : OscillatorLaw p x₂ v₂) :
    OscillatorLaw p (fun t => x₁ t + x₂ t) (fun t => v₁ t + v₂ t) where
  hasDerivAt_x t := (h₁.hasDerivAt_x t).add (h₂.hasDerivAt_x t)
  hasDerivAt_v t := by
    have := (h₁.hasDerivAt_v t).add (h₂.hasDerivAt_v t)
    rwa [← mul_add] at this

/-- **Scaling**: a constant multiple of a solution is a solution. -/
theorem OscillatorLaw.smul {p : OscParams} {x v : ℝ → ℝ} (h : OscillatorLaw p x v) (c : ℝ) :
    OscillatorLaw p (fun t => c * x t) (fun t => c * v t) where
  hasDerivAt_x t := (h.hasDerivAt_x t).const_mul c
  hasDerivAt_v t := by
    have := (h.hasDerivAt_v t).const_mul c
    rwa [mul_left_comm] at this

/-- The energies at any two times agree. -/
theorem energy_eq_of_law (p : OscParams) (x v : ℝ → ℝ) [OscillatorLaw p x v] (s t : ℝ) :
    energy p (x s) (v s) = energy p (x t) (v t) := by
  rw [energy_conserved p x v s, energy_conserved p x v t]

/-- **Amplitude bound** (composition of conservation and `potential_le_energy`): if the initial
energy is at most `E`, then `k x(t)² ≤ 2E` at every time. -/
theorem amplitude_bound (p : OscParams) (x v : ℝ → ℝ) [OscillatorLaw p x v] {E : ℝ}
    (hE : energy p (x 0) (v 0) ≤ E) (t : ℝ) : p.k * x t ^ 2 ≤ 2 * E := by
  have h1 := potential_le_energy p (x t) (v t)
  rw [energy_conserved p x v t] at h1
  linarith

end LeanTheory.Example
