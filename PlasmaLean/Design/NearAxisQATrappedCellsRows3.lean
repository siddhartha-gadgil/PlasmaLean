/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedCells

/-!
# Kernel checks of the precession cell certificate, leaves 17–24

Part 3 of 3 of the kernel-evaluated certificate of `Design/NearAxisQATrappedCells`: leaves
17–24 (in plan order) of the adaptive cover `BoxCover 0 128 0 128` of the start window
(assembled by `box_cover` in `Design/NearAxisQATrappedResonance`). Leaf `boxLeaf_a_b_c_d` is the
index box `[a, b] × [c, d]`, i.e. `ψ₀ ∈ [(4864 + 9a)/1024, (4864 + 9b)/1024]` and
`B_t ∈ [(6912 + c)/1280, (6912 + d)/1280]`, each with 100 `x`-cells per leg. Every leaf is checked
by `decide +kernel` on the Boolean checker `boxOkI` (standard axioms only; one declaration per
leaf keeps the kernel cache small). The leaves are split over three files so that they build in
parallel.
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Leaf box `[32, 64] × [96, 128]` (ψ₀ ∈ [161/32, 85/16], B_t ∈ [219/40, 11/2]) passes. -/
theorem boxLeaf_32_64_96_128 : boxOkI 32 64 96 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Leaf box `[64, 96] × [0, 32]` (ψ₀ ∈ [85/16, 179/32], B_t ∈ [27/5, 217/40]) passes. -/
theorem boxLeaf_64_96_0_32 : boxOkI 64 96 0 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Leaf box `[64, 96] × [32, 64]` (ψ₀ ∈ [85/16, 179/32], B_t ∈ [217/40, 109/20]) passes. -/
theorem boxLeaf_64_96_32_64 : boxOkI 64 96 32 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Leaf box `[96, 128] × [0, 32]` (ψ₀ ∈ [179/32, 47/8], B_t ∈ [27/5, 217/40]) passes. -/
theorem boxLeaf_96_128_0_32 : boxOkI 96 128 0 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Leaf box `[96, 128] × [32, 64]` (ψ₀ ∈ [179/32, 47/8], B_t ∈ [217/40, 109/20]) passes. -/
theorem boxLeaf_96_128_32_64 : boxOkI 96 128 32 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Leaf box `[64, 128] × [64, 96]` (ψ₀ ∈ [85/16, 47/8], B_t ∈ [109/20, 219/40]) passes. -/
theorem boxLeaf_64_128_64_96 : boxOkI 64 128 64 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Leaf box `[64, 96] × [96, 128]` (ψ₀ ∈ [85/16, 179/32], B_t ∈ [219/40, 11/2]) passes. -/
theorem boxLeaf_64_96_96_128 : boxOkI 64 96 96 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Leaf box `[96, 128] × [96, 128]` (ψ₀ ∈ [179/32, 47/8], B_t ∈ [219/40, 11/2]) passes. -/
theorem boxLeaf_96_128_96_128 : boxOkI 96 128 96 128 = true := by decide +kernel

end PlasmaLean.Design.NearAxisQATrappedCells
