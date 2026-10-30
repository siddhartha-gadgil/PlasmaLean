/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2ArcCert

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 6, second part

Kernel-checked runs of the validated checker
`PlasmaLean.Design.LandremanFamily2Quad.cellCheck` (`λ = 200`, one-dimensional grid
`N₁ = 128`, grids `(ntip, nside, N₂)` per cell) on the `k`-cells below. Each cell is checked in
pieces to bound kernel memory (`cellCheck_of_pieces`): the one-dimensional quadratures
(`oneD`), the four outer-arc surface-integral contributions (`outerArc`) and the final
combination (`cellCheckOf`) are separate checks (the evaluation certificate `oned_cert` for the
one-dimensional quadratures, the evaluation certificate `f2_arc_cert`
(`PlasmaLean.Design.LandremanFamily2ArcCert`) for the outer arcs, an evaluation certificate
`fiv_cert` for the final combination) against literal enclosures
(`Dc…`, `Oc…`), which were produced by `#eval` of the same functions (untrusted; the kernel
re-checks them). Each accepted cell proves `(2π)⁶ D_Merc > 0` for both signs `s_G = ±1` on the
whole cell (`cellCheck_sound`).

The first cells of group 6 are in `PlasmaLean.Design.LandremanFamily2Cert6`, which imports
this module (split so that each process stays within the laptop memory budget).
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-! ### Cell `[139/160, 7/8]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[139/160, 7/8]`. -/
@[expose] def Dc29 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4760068858, 4948321781, true⟩, ⟨7556389426, 8680520076, true⟩, ⟨53508723768, 54985981190,
  true⟩, ⟨183743119417, 198839068192, true⟩, ⟨36989633638, 37758969732, true⟩, ⟨53716610488,
  58648416952, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[139/160, 7/8]`. -/
@[expose] def Oc29_0 : FIv × FIv × FIv :=
  (⟨53059702647655, 157958012683433, true⟩, ⟨-4689990416037, 1226981293336, true⟩, ⟨-270161405404,
  561966967230, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[139/160, 7/8]`. -/
@[expose] def Oc29_1 : FIv × FIv × FIv :=
  (⟨51258846849757, 153840593248577, true⟩, ⟨-4518892561053, 1301014002656, true⟩, ⟨-281155518903,
  544299067965, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[139/160, 7/8]`. -/
@[expose] def Oc29_2 : FIv × FIv × FIv :=
  (⟨46905142923932, 172085277185493, true⟩, ⟨-5379619957788, 1627705972854, true⟩, ⟨-359225878902,
  669638508338, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[139/160, 7/8]`. -/
@[expose] def Oc29_3 : FIv × FIv × FIv :=
  (⟨46905142923932, 172085277185493, true⟩, ⟨-5379619957788, 1627705972854, true⟩, ⟨-359225878902,
  669638508338, true⟩)

/-- One-dimensional piece of cell `[139/160, 7/8]`. -/
theorem c29_oneD : oneD 128 (Ecell (139/160) (7/8)) = Dc29 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[139/160, 7/8]`. -/
theorem c29_arc0 : outerArc (lamC 200) (Ecell (139/160) (7/8)) (Ecell (139/160) (7/8)).sq
    (dIof 200 Dc29.1 Dc29.2.2.2.2.1) 12 12 6 0 = Oc29_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[139/160, 7/8]`. -/
theorem c29_arc1 : outerArc (lamC 200) (Ecell (139/160) (7/8)) (Ecell (139/160) (7/8)).sq
    (dIof 200 Dc29.1 Dc29.2.2.2.2.1) 12 12 6 1 = Oc29_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[139/160, 7/8]`. -/
theorem c29_arc2 : outerArc (lamC 200) (Ecell (139/160) (7/8)) (Ecell (139/160) (7/8)).sq
    (dIof 200 Dc29.1 Dc29.2.2.2.2.1) 12 12 6 2 = Oc29_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[139/160, 7/8]`. -/
theorem c29_arc3 : outerArc (lamC 200) (Ecell (139/160) (7/8)) (Ecell (139/160) (7/8)).sq
    (dIof 200 Dc29.1 Dc29.2.2.2.2.1) 12 12 6 3 = Oc29_3 := by
  f2_arc_cert

/-- Final combination of cell `[139/160, 7/8]`. -/
theorem c29_final : cellCheckOf 200 128 12 12 6 (139/160) (7/8) Dc29
    (add3 (add3 Oc29_0 Oc29_1) (add3 Oc29_2 Oc29_3)) = true := by fiv_cert

/-- **Certificate for the cell `[139/160, 7/8]`.** -/
theorem cell29 : cellCheck 200 128 12 12 6 (139/160) (7/8) = true :=
  cellCheck_of_pieces c29_oneD c29_arc0 c29_arc1 c29_arc2 c29_arc3 c29_final

/-! ### Cell `[7/8, 141/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[7/8, 141/160]`. -/
@[expose] def Dc30 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4808216116, 5004653769, true⟩, ⟨7985977342, 9215606243, true⟩, ⟨54699894728, 56277291909,
  true⟩, ⟨197708078742, 214710424471, true⟩, ⟨37334775087, 38136351431, true⟩, ⟨56779180782,
  62175235979, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[7/8, 141/160]`. -/
@[expose] def Oc30_0 : FIv × FIv × FIv :=
  (⟨54140831434784, 170229430694201, true⟩, ⟨-5368603000710, 1394966645503, true⟩, ⟨-304773782950,
  639662559946, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[7/8, 141/160]`. -/
@[expose] def Oc30_1 : FIv × FIv × FIv :=
  (⟨52292867825735, 165889703685952, true⟩, ⟨-5175869330359, 1486522590261, true⟩, ⟨-318295644477,
  620161312475, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[7/8, 141/160]`. -/
@[expose] def Oc30_2 : FIv × FIv × FIv :=
  (⟨47582809081393, 187582499865735, true⟩, ⟨-6268158189298, 1872303103628, true⟩, ⟨-407816761646,
  772129437702, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[7/8, 141/160]`. -/
@[expose] def Oc30_3 : FIv × FIv × FIv :=
  (⟨47582809081393, 187582499865735, true⟩, ⟨-6268158189298, 1872303103628, true⟩, ⟨-407816761646,
  772129437702, true⟩)

/-- One-dimensional piece of cell `[7/8, 141/160]`. -/
theorem c30_oneD : oneD 128 (Ecell (7/8) (141/160)) = Dc30 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[7/8, 141/160]`. -/
theorem c30_arc0 : outerArc (lamC 200) (Ecell (7/8) (141/160)) (Ecell (7/8) (141/160)).sq
    (dIof 200 Dc30.1 Dc30.2.2.2.2.1) 12 12 6 0 = Oc30_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[7/8, 141/160]`. -/
theorem c30_arc1 : outerArc (lamC 200) (Ecell (7/8) (141/160)) (Ecell (7/8) (141/160)).sq
    (dIof 200 Dc30.1 Dc30.2.2.2.2.1) 12 12 6 1 = Oc30_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[7/8, 141/160]`. -/
theorem c30_arc2 : outerArc (lamC 200) (Ecell (7/8) (141/160)) (Ecell (7/8) (141/160)).sq
    (dIof 200 Dc30.1 Dc30.2.2.2.2.1) 12 12 6 2 = Oc30_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[7/8, 141/160]`. -/
theorem c30_arc3 : outerArc (lamC 200) (Ecell (7/8) (141/160)) (Ecell (7/8) (141/160)).sq
    (dIof 200 Dc30.1 Dc30.2.2.2.2.1) 12 12 6 3 = Oc30_3 := by
  f2_arc_cert

/-- Final combination of cell `[7/8, 141/160]`. -/
theorem c30_final : cellCheckOf 200 128 12 12 6 (7/8) (141/160) Dc30
    (add3 (add3 Oc30_0 Oc30_1) (add3 Oc30_2 Oc30_3)) = true := by fiv_cert

/-- **Certificate for the cell `[7/8, 141/160]`.** -/
theorem cell30 : cellCheck 200 128 12 12 6 (7/8) (141/160) = true :=
  cellCheck_of_pieces c30_oneD c30_arc0 c30_arc1 c30_arc2 c30_arc3 c30_final

end PlasmaLean.Design.LandremanFamily2Cert
