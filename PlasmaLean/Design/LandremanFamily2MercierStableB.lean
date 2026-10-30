/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2MercierStableA

/-!
# Rejected fixture of the family-2 Mercier checker: an outer cell at `λ = 15`

Non-vacuity of `PlasmaLean.Design.LandremanFamily2Quad.cellCheck`: the checker rejects the
outer cell `k ∈ [85/100, 86/100]` at the paper-scale `λ = 15` (on-axis `β ≈ 5%`; numerically
those surfaces are Mercier unstable). As in `LandremanFamily2MercierStableA`, the check is split
into separate declarations to bound kernel memory: the one-dimensional quadratures
(`oned_cert`), the four outer-arc contributions (`f2_arc_cert`) and the final combination
(`fiv_cert`), against literal enclosures produced by `#eval` (untrusted; the kernel re-checks
them). Re-exported by `PlasmaLean.Design.LandremanFamily2MercierStable`.
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` of the `λ = 15` cell. -/
@[expose] def Dl15 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4615507970, 4840667288, true⟩, ⟨6436049126, 7650600409, true⟩, ⟨50395316713, 52248045536,
  true⟩, ⟨150175331250, 167654266602, true⟩, ⟨36057265580, 36934979538, true⟩, ⟨46080868668,
  51492735259, true⟩)

/-- One-dimensional piece of the `λ = 15` cell. -/
theorem l15_oneD : oneD 128 (Ecell (85/100) (86/100)) = Dl15 := eq6_sound (by oned_cert)

/-- Outer-arc enclosures `0` of the `λ = 15` cell. -/
@[expose] def Ol15_0 : FIv × FIv × FIv :=
  (⟨172123897257, 4084577831592, true⟩, ⟨-3855917374651, 593705603351, true⟩,
  ⟨-1705977942527, 5542978026436, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `0` of the `λ = 15` cell. -/
theorem l15_arc0 : outerArc (lamC 15) (Ecell (85/100) (86/100)) (Ecell (85/100) (86/100)).sq
    (dIof 15 Dl15.1 Dl15.2.2.2.2.1) 8 8 4 0 = Ol15_0 := by
  f2_arc_cert

/-- Outer-arc enclosures `1` of the `λ = 15` cell. -/
@[expose] def Ol15_1 : FIv × FIv × FIv :=
  (⟨163713882204, 4039220234232, true⟩, ⟨-3726455547047, 722778296439, true⟩,
  ⟨-1982296648114, 5388614743926, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `1` of the `λ = 15` cell. -/
theorem l15_arc1 : outerArc (lamC 15) (Ecell (85/100) (86/100)) (Ecell (85/100) (86/100)).sq
    (dIof 15 Dl15.1 Dl15.2.2.2.2.1) 8 8 4 1 = Ol15_1 := by
  f2_arc_cert

/-- Outer-arc enclosures `2` of the `λ = 15` cell. -/
@[expose] def Ol15_2 : FIv × FIv × FIv :=
  (⟨159520474165, 4826322411822, true⟩, ⟨-4660517106201, 837585123702, true⟩,
  ⟨-2234397187054, 6607730823704, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `2` of the `λ = 15` cell. -/
theorem l15_arc2 : outerArc (lamC 15) (Ecell (85/100) (86/100)) (Ecell (85/100) (86/100)).sq
    (dIof 15 Dl15.1 Dl15.2.2.2.2.1) 8 8 4 2 = Ol15_2 := by
  f2_arc_cert

/-- Outer-arc enclosures `3` of the `λ = 15` cell. -/
@[expose] def Ol15_3 : FIv × FIv × FIv :=
  (⟨159520474165, 4826322411822, true⟩, ⟨-4660517106201, 837585123702, true⟩,
  ⟨-2234397187054, 6607730823704, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `3` of the `λ = 15` cell. -/
theorem l15_arc3 : outerArc (lamC 15) (Ecell (85/100) (86/100)) (Ecell (85/100) (86/100)).sq
    (dIof 15 Dl15.1 Dl15.2.2.2.2.1) 8 8 4 3 = Ol15_3 := by
  f2_arc_cert

/-- Final combination of the `λ = 15` cell: the checker rejects. -/
theorem l15_final : cellCheckOf 15 128 8 8 4 (85/100) (86/100) Dl15
    (add3 (add3 Ol15_0 Ol15_1) (add3 Ol15_2 Ol15_3)) = false := by fiv_cert

/-- Rejected fixture: at the paper-scale `λ = 15` (on-axis `β ≈ 5%`) an outer cell
`k ∈ [0.85, 0.86]` is not accepted (numerically those surfaces are Mercier unstable). -/
theorem cellCheck_rejects_lam15 : cellCheck 15 128 8 8 4 (85/100) (86/100) = false :=
  (cellCheck_eq_of_pieces l15_oneD l15_arc0 l15_arc1 l15_arc2 l15_arc3).trans l15_final

end PlasmaLean.Design.LandremanFamily2Cert
