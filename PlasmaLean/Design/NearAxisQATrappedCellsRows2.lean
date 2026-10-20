/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedCells

/-!
# Kernel checks of the precession cell certificate, flux rows 3–5

Part 2 of 3 of the kernel-evaluated certificate of `Design/NearAxisQATrappedCells`: the boxes
`(PB j, TB l)` for `j ∈ {3, 4, 5}` (flux `ψ₀ ∈ [(38 + j)/8, (39 + j)/8]`) and
`l < 16` (tip field `B_t ∈ [(864 + l)/160, (865 + l)/160]`), each with 100 `x`-cells per leg.
Every box is checked by `decide +kernel` on the Boolean checker `boxOk` (standard axioms only;
one declaration per box keeps the kernel cache small). The rows are split over three files so
that they build in parallel.
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Box `(3, 0)` passes. -/
theorem box_3_0 : boxOk (PB 3) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 1)` passes. -/
theorem box_3_1 : boxOk (PB 3) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 2)` passes. -/
theorem box_3_2 : boxOk (PB 3) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 3)` passes. -/
theorem box_3_3 : boxOk (PB 3) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 4)` passes. -/
theorem box_3_4 : boxOk (PB 3) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 5)` passes. -/
theorem box_3_5 : boxOk (PB 3) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 6)` passes. -/
theorem box_3_6 : boxOk (PB 3) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 7)` passes. -/
theorem box_3_7 : boxOk (PB 3) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 8)` passes. -/
theorem box_3_8 : boxOk (PB 3) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 9)` passes. -/
theorem box_3_9 : boxOk (PB 3) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 10)` passes. -/
theorem box_3_10 : boxOk (PB 3) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 11)` passes. -/
theorem box_3_11 : boxOk (PB 3) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 12)` passes. -/
theorem box_3_12 : boxOk (PB 3) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 13)` passes. -/
theorem box_3_13 : boxOk (PB 3) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 14)` passes. -/
theorem box_3_14 : boxOk (PB 3) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(3, 15)` passes. -/
theorem box_3_15 : boxOk (PB 3) (TB 15) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 0)` passes. -/
theorem box_4_0 : boxOk (PB 4) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 1)` passes. -/
theorem box_4_1 : boxOk (PB 4) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 2)` passes. -/
theorem box_4_2 : boxOk (PB 4) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 3)` passes. -/
theorem box_4_3 : boxOk (PB 4) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 4)` passes. -/
theorem box_4_4 : boxOk (PB 4) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 5)` passes. -/
theorem box_4_5 : boxOk (PB 4) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 6)` passes. -/
theorem box_4_6 : boxOk (PB 4) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 7)` passes. -/
theorem box_4_7 : boxOk (PB 4) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 8)` passes. -/
theorem box_4_8 : boxOk (PB 4) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 9)` passes. -/
theorem box_4_9 : boxOk (PB 4) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 10)` passes. -/
theorem box_4_10 : boxOk (PB 4) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 11)` passes. -/
theorem box_4_11 : boxOk (PB 4) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 12)` passes. -/
theorem box_4_12 : boxOk (PB 4) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 13)` passes. -/
theorem box_4_13 : boxOk (PB 4) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 14)` passes. -/
theorem box_4_14 : boxOk (PB 4) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(4, 15)` passes. -/
theorem box_4_15 : boxOk (PB 4) (TB 15) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 0)` passes. -/
theorem box_5_0 : boxOk (PB 5) (TB 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 1)` passes. -/
theorem box_5_1 : boxOk (PB 5) (TB 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 2)` passes. -/
theorem box_5_2 : boxOk (PB 5) (TB 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 3)` passes. -/
theorem box_5_3 : boxOk (PB 5) (TB 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 4)` passes. -/
theorem box_5_4 : boxOk (PB 5) (TB 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 5)` passes. -/
theorem box_5_5 : boxOk (PB 5) (TB 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 6)` passes. -/
theorem box_5_6 : boxOk (PB 5) (TB 6) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 7)` passes. -/
theorem box_5_7 : boxOk (PB 5) (TB 7) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 8)` passes. -/
theorem box_5_8 : boxOk (PB 5) (TB 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 9)` passes. -/
theorem box_5_9 : boxOk (PB 5) (TB 9) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 10)` passes. -/
theorem box_5_10 : boxOk (PB 5) (TB 10) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 11)` passes. -/
theorem box_5_11 : boxOk (PB 5) (TB 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 12)` passes. -/
theorem box_5_12 : boxOk (PB 5) (TB 12) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 13)` passes. -/
theorem box_5_13 : boxOk (PB 5) (TB 13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 14)` passes. -/
theorem box_5_14 : boxOk (PB 5) (TB 14) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Box `(5, 15)` passes. -/
theorem box_5_15 : boxOk (PB 5) (TB 15) = true := by decide +kernel

end PlasmaLean.Design.NearAxisQATrappedCells
