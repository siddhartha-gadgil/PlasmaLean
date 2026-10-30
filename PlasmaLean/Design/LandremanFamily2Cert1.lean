/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2ArcCert

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 1

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
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-! ### Cell `[7/10, 45/64]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[7/10, 45/64]`. -/
@[expose] def Dc0 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4012145355, 4077699655, true⟩, ⟨2774625942, 2952969032, true⟩, ⟨37406920797, 37757933089,
  true⟩, ⟨50568181485, 51720342672, true⟩, ⟨31582844562, 31898535175, true⟩, ⟨19673687325,
  20491996687, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[7/10, 45/64]`. -/
@[expose] def Oc0_0 : FIv × FIv × FIv :=
  (⟨44844500881639, 76156000963395, true⟩, ⟨-852372067559, 193406948572, true⟩, ⟨-48028089111,
  104773031170, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[7/10, 45/64]`. -/
@[expose] def Oc0_1 : FIv × FIv × FIv :=
  (⟨43464888655915, 73965918051615, true⟩, ⟨-817354828560, 200211846408, true⟩, ⟨-48773356607,
  101038317449, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[7/10, 45/64]`. -/
@[expose] def Oc0_2 : FIv × FIv × FIv :=
  (⟨42362341961042, 77751927977134, true⟩, ⟨-925742145560, 285114134274, true⟩, ⟨-65239514818,
  120480395117, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[7/10, 45/64]`. -/
@[expose] def Oc0_3 : FIv × FIv × FIv :=
  (⟨42362341961042, 77751927977134, true⟩, ⟨-925742145560, 285114134274, true⟩, ⟨-65239514818,
  120480395117, true⟩)

/-- One-dimensional piece of cell `[7/10, 45/64]`. -/
theorem c0_oneD : oneD 128 (Ecell (7/10) (45/64)) = Dc0 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[7/10, 45/64]`. -/
theorem c0_arc0 : outerArc (lamC 200) (Ecell (7/10) (45/64)) (Ecell (7/10) (45/64)).sq
    (dIof 200 Dc0.1 Dc0.2.2.2.2.1) 12 12 6 0 = Oc0_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[7/10, 45/64]`. -/
theorem c0_arc1 : outerArc (lamC 200) (Ecell (7/10) (45/64)) (Ecell (7/10) (45/64)).sq
    (dIof 200 Dc0.1 Dc0.2.2.2.2.1) 12 12 6 1 = Oc0_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[7/10, 45/64]`. -/
theorem c0_arc2 : outerArc (lamC 200) (Ecell (7/10) (45/64)) (Ecell (7/10) (45/64)).sq
    (dIof 200 Dc0.1 Dc0.2.2.2.2.1) 12 12 6 2 = Oc0_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[7/10, 45/64]`. -/
theorem c0_arc3 : outerArc (lamC 200) (Ecell (7/10) (45/64)) (Ecell (7/10) (45/64)).sq
    (dIof 200 Dc0.1 Dc0.2.2.2.2.1) 12 12 6 3 = Oc0_3 := by
  f2_arc_cert

/-- Final combination of cell `[7/10, 45/64]`. -/
theorem c0_final : cellCheckOf 200 128 12 12 6 (7/10) (45/64) Dc0
    (add3 (add3 Oc0_0 Oc0_1) (add3 Oc0_2 Oc0_3)) = true := by fiv_cert

/-- **Certificate for the cell `[7/10, 45/64]`.** -/
theorem cell0 : cellCheck 200 128 12 12 6 (7/10) (45/64) = true :=
  cellCheck_of_pieces c0_oneD c0_arc0 c0_arc1 c0_arc2 c0_arc3 c0_final

/-! ### Cell `[45/64, 113/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[45/64, 113/160]`. -/
@[expose] def Dc1 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4020843126, 4087028114, true⟩, ⟨2813667438, 2995418611, true⟩, ⟨37566312223, 37920968371,
  true⟩, ⟨51446079845, 52626149911, true⟩, ⟨31644753030, 31963023665, true⟩, ⟨19948698247,
  20781669054, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[45/64, 113/160]`. -/
@[expose] def Oc1_0 : FIv × FIv × FIv :=
  (⟨44808553930626, 76359436688283, true⟩, ⟨-864660587694, 195814978775, true⟩, ⟨-48601045244,
  106211414238, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[45/64, 113/160]`. -/
@[expose] def Oc1_1 : FIv × FIv × FIv :=
  (⟨43428366927408, 74163135527805, true⟩, ⟨-829136808100, 202734382312, true⟩, ⟨-49372051509,
  102421943901, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[45/64, 113/160]`. -/
@[expose] def Oc1_2 : FIv × FIv × FIv :=
  (⟨42306821954579, 77987008129008, true⟩, ⟨-938936774364, 288623411249, true⟩, ⟨-66020885522,
  122101911113, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[45/64, 113/160]`. -/
@[expose] def Oc1_3 : FIv × FIv × FIv :=
  (⟨42306821954579, 77987008129008, true⟩, ⟨-938936774364, 288623411249, true⟩, ⟨-66020885522,
  122101911113, true⟩)

/-- One-dimensional piece of cell `[45/64, 113/160]`. -/
theorem c1_oneD : oneD 128 (Ecell (45/64) (113/160)) = Dc1 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[45/64, 113/160]`. -/
theorem c1_arc0 : outerArc (lamC 200) (Ecell (45/64) (113/160)) (Ecell (45/64) (113/160)).sq
    (dIof 200 Dc1.1 Dc1.2.2.2.2.1) 12 12 6 0 = Oc1_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[45/64, 113/160]`. -/
theorem c1_arc1 : outerArc (lamC 200) (Ecell (45/64) (113/160)) (Ecell (45/64) (113/160)).sq
    (dIof 200 Dc1.1 Dc1.2.2.2.2.1) 12 12 6 1 = Oc1_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[45/64, 113/160]`. -/
theorem c1_arc2 : outerArc (lamC 200) (Ecell (45/64) (113/160)) (Ecell (45/64) (113/160)).sq
    (dIof 200 Dc1.1 Dc1.2.2.2.2.1) 12 12 6 2 = Oc1_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[45/64, 113/160]`. -/
theorem c1_arc3 : outerArc (lamC 200) (Ecell (45/64) (113/160)) (Ecell (45/64) (113/160)).sq
    (dIof 200 Dc1.1 Dc1.2.2.2.2.1) 12 12 6 3 = Oc1_3 := by
  f2_arc_cert

/-- Final combination of cell `[45/64, 113/160]`. -/
theorem c1_final : cellCheckOf 200 128 12 12 6 (45/64) (113/160) Dc1
    (add3 (add3 Oc1_0 Oc1_1) (add3 Oc1_2 Oc1_3)) = true := by fiv_cert

/-- **Certificate for the cell `[45/64, 113/160]`.** -/
theorem cell1 : cellCheck 200 128 12 12 6 (45/64) (113/160) = true :=
  cellCheck_of_pieces c1_oneD c1_arc0 c1_arc1 c1_arc2 c1_arc3 c1_final

/-! ### Cell `[113/160, 227/320]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[113/160, 227/320]`. -/
@[expose] def Dc2 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4029663699, 4096491210, true⟩, ⟨2853548411, 3038807510, true⟩, ⟨37728482692, 38086871474,
  true⟩, ⟨52346927632, 53555902780, true⟩, ⟨31707530068, 32028427184, true⟩, ⟨20229609534,
  21077652821, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[113/160, 227/320]`. -/
@[expose] def Oc2_0 : FIv × FIv × FIv :=
  (⟨44778693721718, 76579336352118, true⟩, ⟨-877370943897, 198327535104, true⟩, ⟨-49197547283,
  107701020021, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[113/160, 227/320]`. -/
@[expose] def Oc2_1 : FIv × FIv × FIv :=
  (⟨43397740503236, 74376350961243, true⟩, ⟨-841323986620, 205363023977, true⟩, ⟨-49995448522,
  103854905246, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[113/160, 227/320]`. -/
@[expose] def Oc2_2 : FIv × FIv × FIv :=
  (⟨42256573382440, 78239708005517, true⟩, ⟨-952591726043, 292277331594, true⟩, ⟨-66834636079,
  123782516576, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[113/160, 227/320]`. -/
@[expose] def Oc2_3 : FIv × FIv × FIv :=
  (⟨42256573382440, 78239708005517, true⟩, ⟨-952591726043, 292277331594, true⟩, ⟨-66834636079,
  123782516576, true⟩)

/-- One-dimensional piece of cell `[113/160, 227/320]`. -/
theorem c2_oneD : oneD 128 (Ecell (113/160) (227/320)) = Dc2 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[113/160, 227/320]`. -/
theorem c2_arc0 : outerArc (lamC 200) (Ecell (113/160) (227/320)) (Ecell (113/160) (227/320)).sq
    (dIof 200 Dc2.1 Dc2.2.2.2.2.1) 12 12 6 0 = Oc2_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[113/160, 227/320]`. -/
theorem c2_arc1 : outerArc (lamC 200) (Ecell (113/160) (227/320)) (Ecell (113/160) (227/320)).sq
    (dIof 200 Dc2.1 Dc2.2.2.2.2.1) 12 12 6 1 = Oc2_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[113/160, 227/320]`. -/
theorem c2_arc2 : outerArc (lamC 200) (Ecell (113/160) (227/320)) (Ecell (113/160) (227/320)).sq
    (dIof 200 Dc2.1 Dc2.2.2.2.2.1) 12 12 6 2 = Oc2_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[113/160, 227/320]`. -/
theorem c2_arc3 : outerArc (lamC 200) (Ecell (113/160) (227/320)) (Ecell (113/160) (227/320)).sq
    (dIof 200 Dc2.1 Dc2.2.2.2.2.1) 12 12 6 3 = Oc2_3 := by
  f2_arc_cert

/-- Final combination of cell `[113/160, 227/320]`. -/
theorem c2_final : cellCheckOf 200 128 12 12 6 (113/160) (227/320) Dc2
    (add3 (add3 Oc2_0 Oc2_1) (add3 Oc2_2 Oc2_3)) = true := by fiv_cert

/-- **Certificate for the cell `[113/160, 227/320]`.** -/
theorem cell2 : cellCheck 200 128 12 12 6 (113/160) (227/320) = true :=
  cellCheck_of_pieces c2_oneD c2_arc0 c2_arc1 c2_arc2 c2_arc3 c2_final

/-! ### Cell `[227/320, 57/80]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[227/320, 57/80]`. -/
@[expose] def Dc3 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4038609729, 4106091945, true⟩, ⟨2894296487, 3083167386, true⟩, ⟨37893505311, 38255718655,
  true⟩, ⟨53271585217, 54510508512, true⟩, ⟨31771194435, 32094765790, true⟩, ⟨20516615696,
  21380158852, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[227/320, 57/80]`. -/
@[expose] def Oc3_0 : FIv × FIv × FIv :=
  (⟨38393414522074, 90440331454550, true⟩, ⟨-1373202816664, 428792869432, true⟩, ⟨-94839398870,
  178042327148, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[227/320, 57/80]`. -/
@[expose] def Oc3_1 : FIv × FIv × FIv :=
  (⟨37215821817309, 87909339781339, true⟩, ⟨-1316435137414, 439774226495, true⟩, ⟨-96553019286,
  171454742178, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[227/320, 57/80]`. -/
@[expose] def Oc3_2 : FIv × FIv × FIv :=
  (⟨36074599840332, 92839410555450, true⟩, ⟨-1467600839487, 538343800528, true⟩, ⟨-120025901032,
  201202202818, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[227/320, 57/80]`. -/
@[expose] def Oc3_3 : FIv × FIv × FIv :=
  (⟨36074599840332, 92839410555450, true⟩, ⟨-1467600839487, 538343800528, true⟩, ⟨-120025901032,
  201202202818, true⟩)

/-- One-dimensional piece of cell `[227/320, 57/80]`. -/
theorem c3_oneD : oneD 128 (Ecell (227/320) (57/80)) = Dc3 := eq6_sound (by oned_cert)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[227/320, 57/80]`. -/
theorem c3_arc0 : outerArc (lamC 200) (Ecell (227/320) (57/80)) (Ecell (227/320) (57/80)).sq
    (dIof 200 Dc3.1 Dc3.2.2.2.2.1) 8 8 4 0 = Oc3_0 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[227/320, 57/80]`. -/
theorem c3_arc1 : outerArc (lamC 200) (Ecell (227/320) (57/80)) (Ecell (227/320) (57/80)).sq
    (dIof 200 Dc3.1 Dc3.2.2.2.2.1) 8 8 4 1 = Oc3_1 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[227/320, 57/80]`. -/
theorem c3_arc2 : outerArc (lamC 200) (Ecell (227/320) (57/80)) (Ecell (227/320) (57/80)).sq
    (dIof 200 Dc3.1 Dc3.2.2.2.2.1) 8 8 4 2 = Oc3_2 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[227/320, 57/80]`. -/
theorem c3_arc3 : outerArc (lamC 200) (Ecell (227/320) (57/80)) (Ecell (227/320) (57/80)).sq
    (dIof 200 Dc3.1 Dc3.2.2.2.2.1) 8 8 4 3 = Oc3_3 := by
  f2_arc_cert

/-- Final combination of cell `[227/320, 57/80]`. -/
theorem c3_final : cellCheckOf 200 128 8 8 4 (227/320) (57/80) Dc3
    (add3 (add3 Oc3_0 Oc3_1) (add3 Oc3_2 Oc3_3)) = true := by fiv_cert

/-- **Certificate for the cell `[227/320, 57/80]`.** -/
theorem cell3 : cellCheck 200 128 8 8 4 (227/320) (57/80) = true :=
  cellCheck_of_pieces c3_oneD c3_arc0 c3_arc1 c3_arc2 c3_arc3 c3_final

/-! ### Cell `[57/80, 23/32]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[57/80, 23/32]`. -/
@[expose] def Dc4 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4040301255, 4133184101, true⟩, ⟨2922397704, 3188976850, true⟩, ⟨38061455845, 38602564800,
  true⟩, ⟨54220954261, 56498132029, true⟩, ⟨31835765479, 32230331843, true⟩, ⟨20809919638,
  22005628360, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[57/80, 23/32]`. -/
@[expose] def Oc4_0 : FIv × FIv × FIv :=
  (⟨43683174443197, 79129021116822, true⟩, ⟨-1029289353047, 296332935960, true⟩, ⟨-66866776957,
  129321780277, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[57/80, 23/32]`. -/
@[expose] def Oc4_1 : FIv × FIv × FIv :=
  (⟨42330732834339, 76855299646116, true⟩, ⟨-988115055841, 301383869936, true⟩, ⟨-67448567415,
  124811078005, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[57/80, 23/32]`. -/
@[expose] def Oc4_2 : FIv × FIv × FIv :=
  (⟨41148060561537, 80959844456932, true⟩, ⟨-1107899796763, 391043671967, true⟩, ⟨-85695229178,
  146569750687, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[57/80, 23/32]`. -/
@[expose] def Oc4_3 : FIv × FIv × FIv :=
  (⟨41148060561537, 80959844456932, true⟩, ⟨-1107899796763, 391043671967, true⟩, ⟨-85695229178,
  146569750687, true⟩)

/-- One-dimensional piece of cell `[57/80, 23/32]`. -/
theorem c4_oneD : oneD 128 (Ecell (57/80) (23/32)) = Dc4 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[57/80, 23/32]`. -/
theorem c4_arc0 : outerArc (lamC 200) (Ecell (57/80) (23/32)) (Ecell (57/80) (23/32)).sq
    (dIof 200 Dc4.1 Dc4.2.2.2.2.1) 12 12 6 0 = Oc4_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[57/80, 23/32]`. -/
theorem c4_arc1 : outerArc (lamC 200) (Ecell (57/80) (23/32)) (Ecell (57/80) (23/32)).sq
    (dIof 200 Dc4.1 Dc4.2.2.2.2.1) 12 12 6 1 = Oc4_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[57/80, 23/32]`. -/
theorem c4_arc2 : outerArc (lamC 200) (Ecell (57/80) (23/32)) (Ecell (57/80) (23/32)).sq
    (dIof 200 Dc4.1 Dc4.2.2.2.2.1) 12 12 6 2 = Oc4_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[57/80, 23/32]`. -/
theorem c4_arc3 : outerArc (lamC 200) (Ecell (57/80) (23/32)) (Ecell (57/80) (23/32)).sq
    (dIof 200 Dc4.1 Dc4.2.2.2.2.1) 12 12 6 3 = Oc4_3 := by
  f2_arc_cert

/-- Final combination of cell `[57/80, 23/32]`. -/
theorem c4_final : cellCheckOf 200 128 12 12 6 (57/80) (23/32) Dc4
    (add3 (add3 Oc4_0 Oc4_1) (add3 Oc4_2 Oc4_3)) = true := by fiv_cert

/-- **Certificate for the cell `[57/80, 23/32]`.** -/
theorem cell4 : cellCheck 200 128 12 12 6 (57/80) (23/32) = true :=
  cellCheck_of_pieces c4_oneD c4_arc0 c4_arc1 c4_arc2 c4_arc3 c4_final

end PlasmaLean.Design.LandremanFamily2Cert
