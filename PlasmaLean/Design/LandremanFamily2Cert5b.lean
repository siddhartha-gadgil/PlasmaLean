/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2ArcCert

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 5, second part

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

The first cells of group 5 are in `PlasmaLean.Design.LandremanFamily2Cert5`, which imports
this module (split so that each process stays within the laptop memory budget).
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-! ### Cell `[133/160, 67/80]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[133/160, 67/80]`. -/
@[expose] def Dc23 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4517291476, 4668239087, true⟩, ⟨5651633855, 6360735777, true⟩, ⟨47822082280, 48881166918,
  true⟩, ⟨125488221111, 133685033284, true⟩, ⟨35250916677, 35873453561, true⟩, ⟨40165579621,
  43281465834, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[133/160, 67/80]`. -/
@[expose] def Oc23_0 : FIv × FIv × FIv :=
  (⟨39511934026266, 150625906512468, true⟩, ⟨-4428575196427, 1329235684116, true⟩, ⟨-287298233895,
  556420295874, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[133/160, 67/80]`. -/
@[expose] def Oc23_1 : FIv × FIv × FIv :=
  (⟨38220632521001, 146766707217174, true⟩, ⟨-4262814674503, 1398463071316, true⟩, ⟨-297716173035,
  538333536539, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[133/160, 67/80]`. -/
@[expose] def Oc23_2 : FIv × FIv × FIv :=
  (⟨35630243113320, 161615306949037, true⟩, ⟨-4929111102822, 1688652733669, true⟩, ⟨-363716683989,
  644669681280, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[133/160, 67/80]`. -/
@[expose] def Oc23_3 : FIv × FIv × FIv :=
  (⟨35630243113320, 161615306949037, true⟩, ⟨-4929111102822, 1688652733669, true⟩, ⟨-363716683989,
  644669681280, true⟩)

/-- One-dimensional piece of cell `[133/160, 67/80]`. -/
theorem c23_oneD : oneD 128 (Ecell (133/160) (67/80)) = Dc23 := eq6_sound (by oned_cert)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[133/160, 67/80]`. -/
theorem c23_arc0 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 0 = Oc23_0 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[133/160, 67/80]`. -/
theorem c23_arc1 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 1 = Oc23_1 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[133/160, 67/80]`. -/
theorem c23_arc2 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 2 = Oc23_2 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[133/160, 67/80]`. -/
theorem c23_arc3 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 3 = Oc23_3 := by
  f2_arc_cert

/-- Final combination of cell `[133/160, 67/80]`. -/
theorem c23_final : cellCheckOf 200 128 8 8 4 (133/160) (67/80) Dc23
    (add3 (add3 Oc23_0 Oc23_1) (add3 Oc23_2 Oc23_3)) = true := by fiv_cert

/-- **Certificate for the cell `[133/160, 67/80]`.** -/
theorem cell23 : cellCheck 200 128 8 8 4 (133/160) (67/80) = true :=
  cellCheck_of_pieces c23_oneD c23_arc0 c23_arc1 c23_arc2 c23_arc3 c23_final

/-! ### Cell `[67/80, 27/32]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[67/80, 27/32]`. -/
@[expose] def Dc24 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4553143385, 4709215380, true⟩, ⟨5907477886, 6667316106, true⟩, ⟨48629327491, 49742042966,
  true⟩, ⟨132945112472, 141927212595, true⟩, ⟨35507559105, 36150248654, true⟩, ⟨41983236105,
  45320194956, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[67/80, 27/32]`. -/
@[expose] def Oc24_0 : FIv × FIv × FIv :=
  (⟨39895724930563, 158800803220341, true⟩, ⟨-4880146499303, 1450596295279, true⟩, ⟨-311775698510,
  609724708256, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[67/80, 27/32]`. -/
@[expose] def Oc24_1 : FIv × FIv × FIv :=
  (⟨38586306705523, 154793171323078, true⟩, ⟨-4698979316831, 1530371918543, true⟩, ⟨-323879733513,
  590221943062, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[67/80, 27/32]`. -/
@[expose] def Oc24_2 : FIv × FIv × FIv :=
  (⟨35843648590690, 171546185203146, true⟩, ⟨-5493142782601, 1857883637538, true⟩, ⟨-396784894643,
  711959334978, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[67/80, 27/32]`. -/
@[expose] def Oc24_3 : FIv × FIv × FIv :=
  (⟨35843648590690, 171546185203146, true⟩, ⟨-5493142782601, 1857883637538, true⟩, ⟨-396784894643,
  711959334978, true⟩)

/-- One-dimensional piece of cell `[67/80, 27/32]`. -/
theorem c24_oneD : oneD 128 (Ecell (67/80) (27/32)) = Dc24 := eq6_sound (by oned_cert)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[67/80, 27/32]`. -/
theorem c24_arc0 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 0 = Oc24_0 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[67/80, 27/32]`. -/
theorem c24_arc1 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 1 = Oc24_1 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[67/80, 27/32]`. -/
theorem c24_arc2 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 2 = Oc24_2 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[67/80, 27/32]`. -/
theorem c24_arc3 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 3 = Oc24_3 := by
  f2_arc_cert

/-- Final combination of cell `[67/80, 27/32]`. -/
theorem c24_final : cellCheckOf 200 128 8 8 4 (67/80) (27/32) Dc24
    (add3 (add3 Oc24_0 Oc24_1) (add3 Oc24_2 Oc24_3)) = true := by fiv_cert

/-- **Certificate for the cell `[67/80, 27/32]`.** -/
theorem cell24 : cellCheck 200 128 8 8 4 (67/80) (27/32) = true :=
  cellCheck_of_pieces c24_oneD c24_arc0 c24_arc1 c24_arc2 c24_arc3 c24_final

/-! ### Cell `[27/32, 17/20]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[27/32, 17/20]`. -/
@[expose] def Dc25 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4590641025, 4752207769, true⟩, ⟨6184021857, 7000452740, true⟩, ⟨49485430007, 50657022818,
  true⟩, ⟨141138766036, 151017626562, true⟩, ⟨35776015052, 36440317659, true⟩, ⟨43948778085,
  47532633436, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[27/32, 17/20]`. -/
@[expose] def Oc25_0 : FIv × FIv × FIv :=
  (⟨40317906483611, 168388909605734, true⟩, ⟨-5428124750063, 1595378438439, true⟩, ⟨-340666536195,
  673672713407, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[27/32, 17/20]`. -/
@[expose] def Oc25_1 : FIv × FIv × FIv :=
  (⟨38988771865177, 164216280698501, true⟩, ⟨-5228635355227, 1688419733223, true⟩, ⟨-354891701427,
  652545795981, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[27/32, 17/20]`. -/
@[expose] def Oc25_2 : FIv × FIv × FIv :=
  (⟨36077993819612, 183475885118007, true⟩, ⟨-6197060128073, 2064087909367, true⟩, ⟨-436547345864,
  794769343256, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[27/32, 17/20]`. -/
@[expose] def Oc25_3 : FIv × FIv × FIv :=
  (⟨36077993819612, 183475885118007, true⟩, ⟨-6197060128073, 2064087909367, true⟩, ⟨-436547345864,
  794769343256, true⟩)

/-- One-dimensional piece of cell `[27/32, 17/20]`. -/
theorem c25_oneD : oneD 128 (Ecell (27/32) (17/20)) = Dc25 := eq6_sound (by oned_cert)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[27/32, 17/20]`. -/
theorem c25_arc0 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 0 = Oc25_0 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[27/32, 17/20]`. -/
theorem c25_arc1 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 1 = Oc25_1 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[27/32, 17/20]`. -/
theorem c25_arc2 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 2 = Oc25_2 := by
  f2_arc_cert

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[27/32, 17/20]`. -/
theorem c25_arc3 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 3 = Oc25_3 := by
  f2_arc_cert

/-- Final combination of cell `[27/32, 17/20]`. -/
theorem c25_final : cellCheckOf 200 128 8 8 4 (27/32) (17/20) Dc25
    (add3 (add3 Oc25_0 Oc25_1) (add3 Oc25_2 Oc25_3)) = true := by fiv_cert

/-- **Certificate for the cell `[27/32, 17/20]`.** -/
theorem cell25 : cellCheck 200 128 8 8 4 (27/32) (17/20) = true :=
  cellCheck_of_pieces c25_oneD c25_arc0 c25_arc1 c25_arc2 c25_arc3 c25_final

/-! ### Cell `[17/20, 137/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[17/20, 137/160]`. -/
@[expose] def Dc26 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4629919559, 4797395474, true⟩, ⟨6483857517, 7363699585, true⟩, ⟨50395316713, 51631794315,
  true⟩, ⟨150175331250, 161083761849, true⟩, ⟨36057265580, 36744816045, true⟩, ⟨46080868668,
  49941752748, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[17/20, 137/160]`. -/
@[expose] def Oc26_0 : FIv × FIv × FIv :=
  (⟨50323562697109, 132148643718135, true⟩, ⟨-3374227841750, 899478784537, true⟩, ⟨-200424680871,
  409499221162, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[17/20, 137/160]`. -/
@[expose] def Oc26_1 : FIv × FIv × FIv :=
  (⟨48641832951874, 128555342470232, true⟩, ⟨-3247071076926, 942108216998, true⟩, ⟨-206959815823,
  395981003229, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[17/20, 137/160]`. -/
@[expose] def Oc26_2 : FIv × FIv × FIv :=
  (⟨45137949989573, 140841432742031, true⟩, ⟨-3742355418900, 1175548896140, true⟩, ⟨-262605768073,
  475464372875, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[17/20, 137/160]`. -/
@[expose] def Oc26_3 : FIv × FIv × FIv :=
  (⟨45137949989573, 140841432742031, true⟩, ⟨-3742355418900, 1175548896140, true⟩, ⟨-262605768073,
  475464372875, true⟩)

/-- One-dimensional piece of cell `[17/20, 137/160]`. -/
theorem c26_oneD : oneD 128 (Ecell (17/20) (137/160)) = Dc26 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[17/20, 137/160]`. -/
theorem c26_arc0 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 0 = Oc26_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[17/20, 137/160]`. -/
theorem c26_arc1 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 1 = Oc26_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[17/20, 137/160]`. -/
theorem c26_arc2 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 2 = Oc26_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[17/20, 137/160]`. -/
theorem c26_arc3 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 3 = Oc26_3 := by
  f2_arc_cert

/-- Final combination of cell `[17/20, 137/160]`. -/
theorem c26_final : cellCheckOf 200 128 12 12 6 (17/20) (137/160) Dc26
    (add3 (add3 Oc26_0 Oc26_1) (add3 Oc26_2 Oc26_3)) = true := by fiv_cert

/-- **Certificate for the cell `[17/20, 137/160]`.** -/
theorem cell26 : cellCheck 200 128 12 12 6 (17/20) (137/160) = true :=
  cellCheck_of_pieces c26_oneD c26_arc0 c26_arc1 c26_arc2 c26_arc3 c26_final

end PlasmaLean.Design.LandremanFamily2Cert
