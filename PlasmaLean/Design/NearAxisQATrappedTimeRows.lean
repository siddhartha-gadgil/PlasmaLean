/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedTimeCells

/-!
# Kernel checks of the bounce-time cell certificate

The `16` boxes `TPB j × TTB l` (`j, l < 4`) of the uniform `4 × 4` grid of the start window
`ψ₀ ∈ [4.75, 5.875]`, `B_t ∈ [5.4, 5.5]` pass `timeBoxOk … 83 58`: on each box the bounce time is
at most `83 μs` and the amplitude integral `J = ∫ A (2ψ/B₀) dt` at most `58`
(`Design/NearAxisQATrappedTimeCells`). Each box is checked by `decide +kernel` on the Boolean
checker (standard axioms only); `time_grid` assembles them.
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedCells
open Set

set_option maxRecDepth 100000 in
/-- Time box `TPB 0 × TTB 0` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_0_0 : timeBoxOk (TPB 0) (TTB 0) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 0 × TTB 1` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_0_1 : timeBoxOk (TPB 0) (TTB 1) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 0 × TTB 2` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_0_2 : timeBoxOk (TPB 0) (TTB 2) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 0 × TTB 3` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_0_3 : timeBoxOk (TPB 0) (TTB 3) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 1 × TTB 0` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_1_0 : timeBoxOk (TPB 1) (TTB 0) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 1 × TTB 1` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_1_1 : timeBoxOk (TPB 1) (TTB 1) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 1 × TTB 2` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_1_2 : timeBoxOk (TPB 1) (TTB 2) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 1 × TTB 3` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_1_3 : timeBoxOk (TPB 1) (TTB 3) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 2 × TTB 0` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_2_0 : timeBoxOk (TPB 2) (TTB 0) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 2 × TTB 1` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_2_1 : timeBoxOk (TPB 2) (TTB 1) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 2 × TTB 2` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_2_2 : timeBoxOk (TPB 2) (TTB 2) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 2 × TTB 3` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_2_3 : timeBoxOk (TPB 2) (TTB 3) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 3 × TTB 0` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_3_0 : timeBoxOk (TPB 3) (TTB 0) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 3 × TTB 1` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_3_1 : timeBoxOk (TPB 3) (TTB 1) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 3 × TTB 2` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_3_2 : timeBoxOk (TPB 3) (TTB 2) 83 58 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Time box `TPB 3 × TTB 3` passes with targets `83 μs`, `J ≤ 58`. -/
theorem timeLeaf_3_3 : timeBoxOk (TPB 3) (TTB 3) 83 58 = true := by decide +kernel

/-- **The time grid**: all `16` boxes pass. -/
theorem time_grid : ∀ j < 4, ∀ l < 4, timeBoxOk (TPB j) (TTB l) 83 58 = true := by
  intro j hj l hl
  interval_cases j <;> interval_cases l
  exacts [timeLeaf_0_0, timeLeaf_0_1, timeLeaf_0_2, timeLeaf_0_3, timeLeaf_1_0, timeLeaf_1_1,
    timeLeaf_1_2, timeLeaf_1_3, timeLeaf_2_0, timeLeaf_2_1, timeLeaf_2_2, timeLeaf_2_3,
    timeLeaf_3_0, timeLeaf_3_1, timeLeaf_3_2, timeLeaf_3_3]

/-- **The bounce-time certificate on the start window**: every `ψ₀ ∈ [4.75, 5.875]`,
`B_t ∈ [5.4, 5.5]` carries time bounds with bounce time `≤ 83 μs` and `J ≤ 58`. -/
theorem time_cert {ψ₀ Bt : ℝ} (hψ : ψ₀ ∈ Icc (19 / 4 : ℝ) (47 / 8))
    (hB : Bt ∈ Icc (27 / 5 : ℝ) (11 / 2)) : TimeBounds 83 58 ψ₀ Bt := by
  have := time_cert_of_grid time_grid hψ hB
  exact_mod_cast this

end PlasmaLean.Design.NearAxisQATrappedCells
