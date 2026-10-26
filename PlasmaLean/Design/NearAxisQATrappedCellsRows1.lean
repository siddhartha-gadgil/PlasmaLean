/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the precession cell certificate, leaves 1–8

Part 1 of 3 of the kernel-evaluated certificate of `Design/NearAxisQATrappedCells`: leaves
1–8 (in plan order) of the adaptive cover `BoxCover 0 128 0 128` of the start window
(assembled by `box_cover` in `Design/NearAxisQATrappedResonance`). Leaf `boxLeaf_a_b_c_d` is the
index box `[a, b] × [c, d]`, i.e. `ψ₀ ∈ [(4864 + 9a)/1024, (4864 + 9b)/1024]` and
`B_t ∈ [(6912 + c)/1280, (6912 + d)/1280]`, each with 100 `x`-cells per leg. Every leaf is checked
by an explicit evaluation certificate of the Boolean checker `boxOkI` (`fiv_cert`,
`Certificates/EvalCert`: one kernel leaf per interval operation; standard axioms only; one
declaration per leaf keeps the kernel cache small). The leaves are split over three files so that
they build in parallel.
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Leaf box `[0, 8] × [0, 16]` (ψ₀ ∈ [19/4, 617/128], B_t ∈ [27/5, 433/80]) passes. -/
theorem boxLeaf_0_8_0_16 : boxOkI 0 8 0 16 = true := by fiv_cert

set_option maxRecDepth 100000 in
/-- Leaf box `[8, 16] × [0, 16]` (ψ₀ ∈ [617/128, 313/64], B_t ∈ [27/5, 433/80]) passes. -/
theorem boxLeaf_8_16_0_16 : boxOkI 8 16 0 16 = true := by fiv_cert

set_option maxRecDepth 100000 in
/-- Leaf box `[0, 16] × [16, 32]` (ψ₀ ∈ [19/4, 313/64], B_t ∈ [433/80, 217/40]) passes. -/
theorem boxLeaf_0_16_16_32 : boxOkI 0 16 16 32 = true := by fiv_cert

set_option maxRecDepth 100000 in
/-- Leaf box `[16, 32] × [0, 16]` (ψ₀ ∈ [313/64, 161/32], B_t ∈ [27/5, 433/80]) passes. -/
theorem boxLeaf_16_32_0_16 : boxOkI 16 32 0 16 = true := by fiv_cert

set_option maxRecDepth 100000 in
/-- Leaf box `[16, 32] × [16, 32]` (ψ₀ ∈ [313/64, 161/32], B_t ∈ [433/80, 217/40]) passes. -/
theorem boxLeaf_16_32_16_32 : boxOkI 16 32 16 32 = true := by fiv_cert

set_option maxRecDepth 100000 in
/-- Leaf box `[0, 16] × [32, 48]` (ψ₀ ∈ [19/4, 313/64], B_t ∈ [217/40, 87/16]) passes. -/
theorem boxLeaf_0_16_32_48 : boxOkI 0 16 32 48 = true := by fiv_cert

set_option maxRecDepth 100000 in
/-- Leaf box `[16, 32] × [32, 48]` (ψ₀ ∈ [313/64, 161/32], B_t ∈ [217/40, 87/16]) passes. -/
theorem boxLeaf_16_32_32_48 : boxOkI 16 32 32 48 = true := by fiv_cert

set_option maxRecDepth 100000 in
/-- Leaf box `[0, 32] × [48, 64]` (ψ₀ ∈ [19/4, 161/32], B_t ∈ [87/16, 109/20]) passes. -/
theorem boxLeaf_0_32_48_64 : boxOkI 0 32 48 64 = true := by fiv_cert

end PlasmaLean.Design.NearAxisQATrappedCells
