/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Bridge.Example
public import LeanTheory.Certificates.KernelFact
public import Mathlib.Tactic.NormNum

/-!
# Certificate example: a verified amplitude bound for a family of oscillator states

A small end-to-end use of the certificate toolkit with the example of `Kernel/Example`:

1. **Exact data.** `initialStates` is a family of 21 initial states `(x₀, v₀) ∈ ℚ²` of the
   oscillator `m = 2`, `k = 3` (`params23`), and `energyQ` is the energy in exact rational
   arithmetic, with `energyQ_cast` relating it to the real `energy`.
2. **Certificate.** `initialStates_energy_le`: every state has `2 · energy ≤ 1`. It is proved by
   `kernel_fact` (`Certificates/KernelFact`), which expands the list quantifier into one
   kernel-checked rational comparison per state: an explicit proof term, no `decide`.
3. **Bridge.** `amplitude_bound` (`Bridge/Example`) turns the certificate into the semantic
   statement `amplitude_cert`: every trajectory obeying the law and starting at one of the states
   satisfies `3 x(t)² ≤ 1` for all time.

**Sanity.** `energyQ_zero` (the rest state has zero energy) and the rejected fixture
`initialStates_not_le_small`: the bound `2 · energy ≤ 1/2` fails for some state, so the
certificate is not vacuous.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Example

/-- The oscillator with mass `2` and stiffness `3`. -/
def params23 : OscParams := ⟨2, 3, by norm_num, by norm_num⟩

/-- The energy `m v² / 2 + k x² / 2` in exact rational arithmetic. -/
def energyQ (m k x v : ℚ) : ℚ := m / 2 * v ^ 2 + k / 2 * x ^ 2

/-- The rational energy agrees with the real energy of `params23`. -/
theorem energyQ_cast (x v : ℚ) :
    ((energyQ 2 3 x v : ℚ) : ℝ) = energy params23 (x : ℝ) (v : ℝ) := by
  simp [energyQ, energy, params23]

/-- A family of 21 initial states `(x₀, v₀)` on the segment from `(-1/4, 1/2)` to
`(1/4, 0)`. -/
def initialStates : List (ℚ × ℚ) :=
  (List.range 21).map fun i : ℕ => ((i : ℚ) / 40 - 1 / 4, 1 / 2 - (i : ℚ) / 40)

/-- **Certificate**: every initial state has `2 · energy ≤ 1` (an explicit proof term built by
`kernel_fact`, one rational comparison per state). -/
theorem initialStates_energy_le : ∀ s ∈ initialStates, 2 * energyQ 2 3 s.1 s.2 ≤ 1 := by
  kernel_fact

/-- **Verified amplitude bound**: every trajectory of the oscillator `params23` starting at one
of the certified initial states satisfies `3 x(t)² ≤ 1` for all time. -/
theorem amplitude_cert (x v : ℝ → ℝ) [OscillatorLaw params23 x v] {s : ℚ × ℚ}
    (hs : s ∈ initialStates) (hx : x 0 = s.1) (hv : v 0 = s.2) (t : ℝ) :
    3 * x t ^ 2 ≤ 1 := by
  have hE : energy params23 (x 0) (v 0) ≤ 1 / 2 := by
    have h := initialStates_energy_le s hs
    have h' : ((2 * energyQ 2 3 s.1 s.2 : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h
    rw [Rat.cast_mul, energyQ_cast] at h'
    rw [hx, hv]
    push_cast at h'
    linarith
  have := amplitude_bound params23 x v hE t
  simpa [params23] using this

/-- **Sanity** (degenerate case): the rest state has zero energy. -/
theorem energyQ_zero (m k : ℚ) : energyQ m k 0 0 = 0 := by
  simp [energyQ]

/-- **Sanity** (rejected fixture): the stronger bound `2 · energy ≤ 1/2` fails for the first
state `(-1/4, 1/2)`, so the certificate above is not vacuous. -/
theorem initialStates_not_le_small : ¬ ∀ s ∈ initialStates, 2 * energyQ 2 3 s.1 s.2 ≤ 1 / 2 := by
  intro h
  have hmem : ((-1 / 4 : ℚ), (1 / 2 : ℚ)) ∈ initialStates :=
    List.mem_map.2 ⟨0, List.mem_range.2 (by norm_num : 0 < 21), by norm_num⟩
  have := h _ hmem
  norm_num [energyQ] at this

end LeanTheory.Example
