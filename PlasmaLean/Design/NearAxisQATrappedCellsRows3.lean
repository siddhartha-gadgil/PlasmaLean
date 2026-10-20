/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedCells

/-!
# Kernel checks of the precession cell certificate, flux rows 6–8

Part 3 of 3 of the kernel-evaluated certificate of `Design/NearAxisQATrappedCells`: the boxes
`(PB j, TB l)` for `j ∈ {6, 7, 8}` (flux `ψ₀ ∈ [(38 + j)/8, (39 + j)/8]`) and
`l < 16` (tip field `B_t ∈ [(864 + l)/160, (865 + l)/160]`), each with 100 `x`-cells per leg.
Every box is checked by `decide +kernel` on the Boolean checker `boxOk` (standard axioms only;
one declaration per box keeps the kernel cache small). The rows are split over three files so
that they build in parallel.
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Box `(6, 0)` passes. -/
theorem box_6_0 : boxOk (PB 6) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 1)` passes. -/
theorem box_6_1 : boxOk (PB 6) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 2)` passes. -/
theorem box_6_2 : boxOk (PB 6) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 3)` passes. -/
theorem box_6_3 : boxOk (PB 6) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 4)` passes. -/
theorem box_6_4 : boxOk (PB 6) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 5)` passes. -/
theorem box_6_5 : boxOk (PB 6) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 6)` passes. -/
theorem box_6_6 : boxOk (PB 6) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 7)` passes. -/
theorem box_6_7 : boxOk (PB 6) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 8)` passes. -/
theorem box_6_8 : boxOk (PB 6) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 9)` passes. -/
theorem box_6_9 : boxOk (PB 6) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 10)` passes. -/
theorem box_6_10 : boxOk (PB 6) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 11)` passes. -/
theorem box_6_11 : boxOk (PB 6) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 12)` passes. -/
theorem box_6_12 : boxOk (PB 6) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 13)` passes. -/
theorem box_6_13 : boxOk (PB 6) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 14)` passes. -/
theorem box_6_14 : boxOk (PB 6) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(6, 15)` passes. -/
theorem box_6_15 : boxOk (PB 6) (TB 15) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 0)` passes. -/
theorem box_7_0 : boxOk (PB 7) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 1)` passes. -/
theorem box_7_1 : boxOk (PB 7) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 2)` passes. -/
theorem box_7_2 : boxOk (PB 7) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 3)` passes. -/
theorem box_7_3 : boxOk (PB 7) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 4)` passes. -/
theorem box_7_4 : boxOk (PB 7) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 5)` passes. -/
theorem box_7_5 : boxOk (PB 7) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 6)` passes. -/
theorem box_7_6 : boxOk (PB 7) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 7)` passes. -/
theorem box_7_7 : boxOk (PB 7) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 8)` passes. -/
theorem box_7_8 : boxOk (PB 7) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 9)` passes. -/
theorem box_7_9 : boxOk (PB 7) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 10)` passes. -/
theorem box_7_10 : boxOk (PB 7) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 11)` passes. -/
theorem box_7_11 : boxOk (PB 7) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 12)` passes. -/
theorem box_7_12 : boxOk (PB 7) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 13)` passes. -/
theorem box_7_13 : boxOk (PB 7) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 14)` passes. -/
theorem box_7_14 : boxOk (PB 7) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(7, 15)` passes. -/
theorem box_7_15 : boxOk (PB 7) (TB 15) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 0)` passes. -/
theorem box_8_0 : boxOk (PB 8) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 1)` passes. -/
theorem box_8_1 : boxOk (PB 8) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 2)` passes. -/
theorem box_8_2 : boxOk (PB 8) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 3)` passes. -/
theorem box_8_3 : boxOk (PB 8) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 4)` passes. -/
theorem box_8_4 : boxOk (PB 8) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 5)` passes. -/
theorem box_8_5 : boxOk (PB 8) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 6)` passes. -/
theorem box_8_6 : boxOk (PB 8) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 7)` passes. -/
theorem box_8_7 : boxOk (PB 8) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 8)` passes. -/
theorem box_8_8 : boxOk (PB 8) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 9)` passes. -/
theorem box_8_9 : boxOk (PB 8) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 10)` passes. -/
theorem box_8_10 : boxOk (PB 8) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 11)` passes. -/
theorem box_8_11 : boxOk (PB 8) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 12)` passes. -/
theorem box_8_12 : boxOk (PB 8) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 13)` passes. -/
theorem box_8_13 : boxOk (PB 8) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 14)` passes. -/
theorem box_8_14 : boxOk (PB 8) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(8, 15)` passes. -/
theorem box_8_15 : boxOk (PB 8) (TB 15) = true := by decide +kernel

end PlasmaLean.Design.NearAxisQATrappedCells
