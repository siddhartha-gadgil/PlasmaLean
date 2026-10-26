/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Quad
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 5

Kernel-checked runs of the validated checker
`PlasmaLean.Design.LandremanFamily2Quad.cellCheck` (`λ = 200`, one-dimensional grid
`N₁ = 128`, grids `(ntip, nside, N₂)` per cell) on the `k`-cells below. Each cell is checked in
pieces to bound kernel memory (`cellCheck_of_pieces`): the one-dimensional quadratures
(`oneD`), the four outer-arc surface-integral contributions (`outerArc`) and the final
combination (`cellCheckOf`) are separate checks (the evaluation certificate `oned_cert` for the
one-dimensional quadratures, `decide +kernel` for the outer arcs, an
evaluation certificate `fiv_cert` for the final combination) against literal enclosures
(`Dc…`, `Oc…`), which were produced by `#eval` of the same functions (untrusted; the kernel
re-checks them). Each accepted cell proves `(2π)⁶ D_Merc > 0` for both signs `s_G = ±1` on the
whole cell (`cellCheck_sound`).
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-! ### Cell `[129/160, 13/16]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[129/160, 13/16]`. -/
@[expose] def Dc19 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4388111976, 4521578876, true⟩, ⟨4795085818, 5345723948, true⟩, ⟨45002629130, 45888201362,
  true⟩, ⟨101425628881, 107294091415, true⟩, ⟨34326339078, 34880155202, true⟩, ⟨34085119905,
  36512100172, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[129/160, 13/16]`. -/
@[expose] def Oc19_0 : FIv × FIv × FIv :=
  (⟨38318637233026, 127267400660435, true⟩, ⟨-3212152689043, 997359771651, true⟩, ⟨-218192013241,
  410357938306, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[129/160, 13/16]`. -/
@[expose] def Oc19_1 : FIv × FIv × FIv :=
  (⟨37085771091669, 123873423125420, true⟩, ⟨-3088069106633, 1038688890062, true⟩, ⟨-224430834366,
  396426261411, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[129/160, 13/16]`. -/
@[expose] def Oc19_2 : FIv × FIv × FIv :=
  (⟨34981664668205, 134063601464946, true⟩, ⟨-3468346673284, 1227835097385, true⟩, ⟨-271684040712,
  464960226366, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[129/160, 13/16]`. -/
@[expose] def Oc19_3 : FIv × FIv × FIv :=
  (⟨34981664668205, 134063601464946, true⟩, ⟨-3468346673284, 1227835097385, true⟩, ⟨-271684040712,
  464960226366, true⟩)

/-- One-dimensional piece of cell `[129/160, 13/16]`. -/
theorem c19_oneD : oneD 128 (Ecell (129/160) (13/16)) = Dc19 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[129/160, 13/16]`. -/
theorem c19_arc0 : outerArc (lamC 200) (Ecell (129/160) (13/16)) (Ecell (129/160) (13/16)).sq
    (dIof 200 Dc19.1 Dc19.2.2.2.2.1) 8 8 4 0 = Oc19_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[129/160, 13/16]`. -/
theorem c19_arc1 : outerArc (lamC 200) (Ecell (129/160) (13/16)) (Ecell (129/160) (13/16)).sq
    (dIof 200 Dc19.1 Dc19.2.2.2.2.1) 8 8 4 1 = Oc19_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[129/160, 13/16]`. -/
theorem c19_arc2 : outerArc (lamC 200) (Ecell (129/160) (13/16)) (Ecell (129/160) (13/16)).sq
    (dIof 200 Dc19.1 Dc19.2.2.2.2.1) 8 8 4 2 = Oc19_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[129/160, 13/16]`. -/
theorem c19_arc3 : outerArc (lamC 200) (Ecell (129/160) (13/16)) (Ecell (129/160) (13/16)).sq
    (dIof 200 Dc19.1 Dc19.2.2.2.2.1) 8 8 4 3 = Oc19_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[129/160, 13/16]`. -/
theorem c19_final : cellCheckOf 200 128 8 8 4 (129/160) (13/16) Dc19
    (add3 (add3 Oc19_0 Oc19_1) (add3 Oc19_2 Oc19_3)) = true := by fiv_cert

/-- **Certificate for the cell `[129/160, 13/16]`.** -/
theorem cell19 : cellCheck 200 128 8 8 4 (129/160) (13/16) = true :=
  cellCheck_of_pieces c19_oneD c19_arc0 c19_arc1 c19_arc2 c19_arc3 c19_final

/-! ### Cell `[13/16, 131/160]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[13/16, 131/160]`. -/
@[expose] def Dc20 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4418467175, 4555909249, true⟩, ⟨4987547967, 5572256680, true⟩, ⟨45652824016, 46576557200,
  true⟩, ⟨106707576364, 113059719980, true⟩, ⟨34543591252, 35113031093, true⟩, ⟨35450748337,
  38025658637, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[13/16, 131/160]`. -/
@[expose] def Oc20_0 : FIv × FIv × FIv :=
  (⟨38569404799410, 132035792692131, true⟩, ⟨-3451979412138, 1061863924867, true⟩, ⟨-232201656849,
  439437709103, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[13/16, 131/160]`. -/
@[expose] def Oc20_1 : FIv × FIv × FIv :=
  (⟨37323851357843, 128541756584662, true⟩, ⟨-3319492076111, 1108425621830, true⟩, ⟨-239216791052,
  424650577283, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[13/16, 131/160]`. -/
@[expose] def Oc20_2 : FIv × FIv × FIv :=
  (⟨35113634305287, 139608259112811, true⟩, ⟨-3748654141318, 1319612304897, true⟩, ⟨-290252349265,
  500347681119, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[13/16, 131/160]`. -/
@[expose] def Oc20_3 : FIv × FIv × FIv :=
  (⟨35113634305287, 139608259112811, true⟩, ⟨-3748654141318, 1319612304897, true⟩, ⟨-290252349265,
  500347681119, true⟩)

/-- One-dimensional piece of cell `[13/16, 131/160]`. -/
theorem c20_oneD : oneD 128 (Ecell (13/16) (131/160)) = Dc20 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[13/16, 131/160]`. -/
theorem c20_arc0 : outerArc (lamC 200) (Ecell (13/16) (131/160)) (Ecell (13/16) (131/160)).sq
    (dIof 200 Dc20.1 Dc20.2.2.2.2.1) 8 8 4 0 = Oc20_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[13/16, 131/160]`. -/
theorem c20_arc1 : outerArc (lamC 200) (Ecell (13/16) (131/160)) (Ecell (13/16) (131/160)).sq
    (dIof 200 Dc20.1 Dc20.2.2.2.2.1) 8 8 4 1 = Oc20_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[13/16, 131/160]`. -/
theorem c20_arc2 : outerArc (lamC 200) (Ecell (13/16) (131/160)) (Ecell (13/16) (131/160)).sq
    (dIof 200 Dc20.1 Dc20.2.2.2.2.1) 8 8 4 2 = Oc20_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[13/16, 131/160]`. -/
theorem c20_arc3 : outerArc (lamC 200) (Ecell (13/16) (131/160)) (Ecell (13/16) (131/160)).sq
    (dIof 200 Dc20.1 Dc20.2.2.2.2.1) 8 8 4 3 = Oc20_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[13/16, 131/160]`. -/
theorem c20_final : cellCheckOf 200 128 8 8 4 (13/16) (131/160) Dc20
    (add3 (add3 Oc20_0 Oc20_1) (add3 Oc20_2 Oc20_3)) = true := by fiv_cert

/-- **Certificate for the cell `[13/16, 131/160]`.** -/
theorem cell20 : cellCheck 200 128 8 8 4 (13/16) (131/160) = true :=
  cellCheck_of_pieces c20_oneD c20_arc0 c20_arc1 c20_arc2 c20_arc3 c20_final

/-! ### Cell `[131/160, 33/40]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[131/160, 33/40]`. -/
@[expose] def Dc21 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4450055691, 4591719031, true⟩, ⟨5193459444, 5815606572, true⟩, ⟨46337411697, 47302508289,
  true⟩, ⟨112439953144, 119334644216, true⟩, ⟨34769672946, 35355706148, true⟩, ⟨36912187482,
  39649768087, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[131/160, 33/40]`. -/
@[expose] def Oc21_0 : FIv × FIv × FIv :=
  (⟨38850745660234, 137430174220235, true⟩, ⟨-3728411238924, 1137456508983, true⟩, ⟨-248107531879,
  472783158575, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[131/160, 33/40]`. -/
@[expose] def Oc21_1 : FIv × FIv × FIv :=
  (⟨37591256326439, 133826091291739, true⟩, ⟨-3586356628761, 1191167252908, true⟩, ⟨-256048184897,
  457026998606, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[131/160, 33/40]`. -/
@[expose] def Oc21_2 : FIv × FIv × FIv :=
  (⟨35265447314191, 145932147571267, true⟩, ⟨-4078034569563, 1425035925053, true⟩, ⟨-311422049828,
  541216583661, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[131/160, 33/40]`. -/
@[expose] def Oc21_3 : FIv × FIv × FIv :=
  (⟨35265447314191, 145932147571267, true⟩, ⟨-4078034569563, 1425035925053, true⟩, ⟨-311422049828,
  541216583661, true⟩)

/-- One-dimensional piece of cell `[131/160, 33/40]`. -/
theorem c21_oneD : oneD 128 (Ecell (131/160) (33/40)) = Dc21 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[131/160, 33/40]`. -/
theorem c21_arc0 : outerArc (lamC 200) (Ecell (131/160) (33/40)) (Ecell (131/160) (33/40)).sq
    (dIof 200 Dc21.1 Dc21.2.2.2.2.1) 8 8 4 0 = Oc21_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[131/160, 33/40]`. -/
theorem c21_arc1 : outerArc (lamC 200) (Ecell (131/160) (33/40)) (Ecell (131/160) (33/40)).sq
    (dIof 200 Dc21.1 Dc21.2.2.2.2.1) 8 8 4 1 = Oc21_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[131/160, 33/40]`. -/
theorem c21_arc2 : outerArc (lamC 200) (Ecell (131/160) (33/40)) (Ecell (131/160) (33/40)).sq
    (dIof 200 Dc21.1 Dc21.2.2.2.2.1) 8 8 4 2 = Oc21_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[131/160, 33/40]`. -/
theorem c21_arc3 : outerArc (lamC 200) (Ecell (131/160) (33/40)) (Ecell (131/160) (33/40)).sq
    (dIof 200 Dc21.1 Dc21.2.2.2.2.1) 8 8 4 3 = Oc21_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[131/160, 33/40]`. -/
theorem c21_final : cellCheckOf 200 128 8 8 4 (131/160) (33/40) Dc21
    (add3 (add3 Oc21_0 Oc21_1) (add3 Oc21_2 Oc21_3)) = true := by fiv_cert

/-- **Certificate for the cell `[131/160, 33/40]`.** -/
theorem cell21 : cellCheck 200 128 8 8 4 (131/160) (33/40) = true :=
  cellCheck_of_pieces c21_oneD c21_arc0 c21_arc1 c21_arc2 c21_arc3 c21_final

/-! ### Cell `[33/40, 133/160]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[33/40, 133/160]`. -/
@[expose] def Dc22 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4482964846, 4629120507, true⟩, ⟨5414266807, 6077692520, true⟩, ⟨47059377347, 48069436684,
  true⟩, ⟨118678519420, 126184231551, true⟩, ⟨35005214724, 35608909356, true⟩, ⟨38479821377,
  41396901096, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[33/40, 133/160]`. -/
@[expose] def Oc22_0 : FIv × FIv × FIv :=
  (⟨39164294205064, 143573467842765, true⟩, ⟨-4050091401484, 1226104465889, true⟩, ⟨-266303037872,
  511349452944, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[33/40, 133/160]`. -/
@[expose] def Oc22_1 : FIv × FIv × FIv :=
  (⟨37889589323536, 139848152423878, true⟩, ⟨-3897054609415, 1286805792079, true⟩, ⟨-275359024894,
  494503047107, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[33/40, 133/160]`. -/
@[expose] def Oc22_2 : FIv × FIv × FIv :=
  (⟨35437553587651, 153206704315637, true⟩, ⟨-4467595925257, 1547280063677, true⟩, ⟨-335759667747,
  588915025628, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[33/40, 133/160]`. -/
@[expose] def Oc22_3 : FIv × FIv × FIv :=
  (⟨35437553587651, 153206704315637, true⟩, ⟨-4467595925257, 1547280063677, true⟩, ⟨-335759667747,
  588915025628, true⟩)

/-- One-dimensional piece of cell `[33/40, 133/160]`. -/
theorem c22_oneD : oneD 128 (Ecell (33/40) (133/160)) = Dc22 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[33/40, 133/160]`. -/
theorem c22_arc0 : outerArc (lamC 200) (Ecell (33/40) (133/160)) (Ecell (33/40) (133/160)).sq
    (dIof 200 Dc22.1 Dc22.2.2.2.2.1) 8 8 4 0 = Oc22_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[33/40, 133/160]`. -/
theorem c22_arc1 : outerArc (lamC 200) (Ecell (33/40) (133/160)) (Ecell (33/40) (133/160)).sq
    (dIof 200 Dc22.1 Dc22.2.2.2.2.1) 8 8 4 1 = Oc22_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[33/40, 133/160]`. -/
theorem c22_arc2 : outerArc (lamC 200) (Ecell (33/40) (133/160)) (Ecell (33/40) (133/160)).sq
    (dIof 200 Dc22.1 Dc22.2.2.2.2.1) 8 8 4 2 = Oc22_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[33/40, 133/160]`. -/
theorem c22_arc3 : outerArc (lamC 200) (Ecell (33/40) (133/160)) (Ecell (33/40) (133/160)).sq
    (dIof 200 Dc22.1 Dc22.2.2.2.2.1) 8 8 4 3 = Oc22_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[33/40, 133/160]`. -/
theorem c22_final : cellCheckOf 200 128 8 8 4 (33/40) (133/160) Dc22
    (add3 (add3 Oc22_0 Oc22_1) (add3 Oc22_2 Oc22_3)) = true := by fiv_cert

/-- **Certificate for the cell `[33/40, 133/160]`.** -/
theorem cell22 : cellCheck 200 128 8 8 4 (33/40) (133/160) = true :=
  cellCheck_of_pieces c22_oneD c22_arc0 c22_arc1 c22_arc2 c22_arc3 c22_final

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

/-- Outer-arc piece 0 of cell `[133/160, 67/80]`. -/
theorem c23_arc0 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 0 = Oc23_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[133/160, 67/80]`. -/
theorem c23_arc1 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 1 = Oc23_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[133/160, 67/80]`. -/
theorem c23_arc2 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 2 = Oc23_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[133/160, 67/80]`. -/
theorem c23_arc3 : outerArc (lamC 200) (Ecell (133/160) (67/80)) (Ecell (133/160) (67/80)).sq
    (dIof 200 Dc23.1 Dc23.2.2.2.2.1) 8 8 4 3 = Oc23_3 := eq3_sound (by decide +kernel)

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

/-- Outer-arc piece 0 of cell `[67/80, 27/32]`. -/
theorem c24_arc0 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 0 = Oc24_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[67/80, 27/32]`. -/
theorem c24_arc1 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 1 = Oc24_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[67/80, 27/32]`. -/
theorem c24_arc2 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 2 = Oc24_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[67/80, 27/32]`. -/
theorem c24_arc3 : outerArc (lamC 200) (Ecell (67/80) (27/32)) (Ecell (67/80) (27/32)).sq
    (dIof 200 Dc24.1 Dc24.2.2.2.2.1) 8 8 4 3 = Oc24_3 := eq3_sound (by decide +kernel)

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

/-- Outer-arc piece 0 of cell `[27/32, 17/20]`. -/
theorem c25_arc0 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 0 = Oc25_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[27/32, 17/20]`. -/
theorem c25_arc1 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 1 = Oc25_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[27/32, 17/20]`. -/
theorem c25_arc2 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 2 = Oc25_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[27/32, 17/20]`. -/
theorem c25_arc3 : outerArc (lamC 200) (Ecell (27/32) (17/20)) (Ecell (27/32) (17/20)).sq
    (dIof 200 Dc25.1 Dc25.2.2.2.2.1) 8 8 4 3 = Oc25_3 := eq3_sound (by decide +kernel)

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

/-- Outer-arc piece 0 of cell `[17/20, 137/160]`. -/
theorem c26_arc0 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 0 = Oc26_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[17/20, 137/160]`. -/
theorem c26_arc1 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 1 = Oc26_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[17/20, 137/160]`. -/
theorem c26_arc2 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 2 = Oc26_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[17/20, 137/160]`. -/
theorem c26_arc3 : outerArc (lamC 200) (Ecell (17/20) (137/160)) (Ecell (17/20) (137/160)).sq
    (dIof 200 Dc26.1 Dc26.2.2.2.2.1) 12 12 6 3 = Oc26_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[17/20, 137/160]`. -/
theorem c26_final : cellCheckOf 200 128 12 12 6 (17/20) (137/160) Dc26
    (add3 (add3 Oc26_0 Oc26_1) (add3 Oc26_2 Oc26_3)) = true := by fiv_cert

/-- **Certificate for the cell `[17/20, 137/160]`.** -/
theorem cell26 : cellCheck 200 128 12 12 6 (17/20) (137/160) = true :=
  cellCheck_of_pieces c26_oneD c26_arc0 c26_arc1 c26_arc2 c26_arc3 c26_final

end PlasmaLean.Design.LandremanFamily2Cert
