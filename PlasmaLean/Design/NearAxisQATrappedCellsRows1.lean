/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedCells

/-!
# Kernel checks of the precession cell certificate, flux rows 0–2

Part 1 of 3 of the kernel-evaluated certificate of `Design/NearAxisQATrappedCells`: the boxes
`(PB j, TB l)` for `j ∈ {0, 1, 2}` (flux `ψ₀ ∈ [(38 + j)/8, (39 + j)/8]`) and
`l < 16` (tip field `B_t ∈ [(864 + l)/160, (865 + l)/160]`), each with 100 `x`-cells per leg.
Every box is checked by `decide +kernel` on the Boolean checker `boxOk` (standard axioms only;
one declaration per box keeps the kernel cache small). The rows are split over three files so
that they build in parallel.
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Box `(0, 0)` passes. -/
theorem box_0_0 : boxOk (PB 0) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 1)` passes. -/
theorem box_0_1 : boxOk (PB 0) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 2)` passes. -/
theorem box_0_2 : boxOk (PB 0) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 3)` passes. -/
theorem box_0_3 : boxOk (PB 0) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 4)` passes. -/
theorem box_0_4 : boxOk (PB 0) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 5)` passes. -/
theorem box_0_5 : boxOk (PB 0) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 6)` passes. -/
theorem box_0_6 : boxOk (PB 0) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 7)` passes. -/
theorem box_0_7 : boxOk (PB 0) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 8)` passes. -/
theorem box_0_8 : boxOk (PB 0) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 9)` passes. -/
theorem box_0_9 : boxOk (PB 0) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 10)` passes. -/
theorem box_0_10 : boxOk (PB 0) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 11)` passes. -/
theorem box_0_11 : boxOk (PB 0) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 12)` passes. -/
theorem box_0_12 : boxOk (PB 0) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 13)` passes. -/
theorem box_0_13 : boxOk (PB 0) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 14)` passes. -/
theorem box_0_14 : boxOk (PB 0) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(0, 15)` passes. -/
theorem box_0_15 : boxOk (PB 0) (TB 15) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 0)` passes. -/
theorem box_1_0 : boxOk (PB 1) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 1)` passes. -/
theorem box_1_1 : boxOk (PB 1) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 2)` passes. -/
theorem box_1_2 : boxOk (PB 1) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 3)` passes. -/
theorem box_1_3 : boxOk (PB 1) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 4)` passes. -/
theorem box_1_4 : boxOk (PB 1) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 5)` passes. -/
theorem box_1_5 : boxOk (PB 1) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 6)` passes. -/
theorem box_1_6 : boxOk (PB 1) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 7)` passes. -/
theorem box_1_7 : boxOk (PB 1) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 8)` passes. -/
theorem box_1_8 : boxOk (PB 1) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 9)` passes. -/
theorem box_1_9 : boxOk (PB 1) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 10)` passes. -/
theorem box_1_10 : boxOk (PB 1) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 11)` passes. -/
theorem box_1_11 : boxOk (PB 1) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 12)` passes. -/
theorem box_1_12 : boxOk (PB 1) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 13)` passes. -/
theorem box_1_13 : boxOk (PB 1) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 14)` passes. -/
theorem box_1_14 : boxOk (PB 1) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(1, 15)` passes. -/
theorem box_1_15 : boxOk (PB 1) (TB 15) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 0)` passes. -/
theorem box_2_0 : boxOk (PB 2) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 1)` passes. -/
theorem box_2_1 : boxOk (PB 2) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 2)` passes. -/
theorem box_2_2 : boxOk (PB 2) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 3)` passes. -/
theorem box_2_3 : boxOk (PB 2) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 4)` passes. -/
theorem box_2_4 : boxOk (PB 2) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 5)` passes. -/
theorem box_2_5 : boxOk (PB 2) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 6)` passes. -/
theorem box_2_6 : boxOk (PB 2) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 7)` passes. -/
theorem box_2_7 : boxOk (PB 2) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 8)` passes. -/
theorem box_2_8 : boxOk (PB 2) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 9)` passes. -/
theorem box_2_9 : boxOk (PB 2) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 10)` passes. -/
theorem box_2_10 : boxOk (PB 2) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 11)` passes. -/
theorem box_2_11 : boxOk (PB 2) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 12)` passes. -/
theorem box_2_12 : boxOk (PB 2) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 13)` passes. -/
theorem box_2_13 : boxOk (PB 2) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 14)` passes. -/
theorem box_2_14 : boxOk (PB 2) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(2, 15)` passes. -/
theorem box_2_15 : boxOk (PB 2) (TB 15) = true := by decide +kernel

end PlasmaLean.Design.NearAxisQATrappedCells
