/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Quad

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 4

Kernel-checked runs of the validated checker
`PlasmaLean.Design.LandremanFamily2Quad.cellCheck` (`λ = 200`, one-dimensional grid
`N₁ = 128`, grids `(ntip, nside, N₂)` per cell) on the `k`-cells below. Each cell is checked in
pieces to bound kernel memory (`cellCheck_of_pieces`): the one-dimensional quadratures
(`oneD`), the four outer-arc surface-integral contributions (`outerArc`) and the final
combination (`cellCheckOf`) are separate `decide +kernel` checks against literal enclosures
(`Dc…`, `Oc…`), which were produced by `#eval` of the same functions (untrusted; the kernel
re-checks them). Each accepted cell proves `(2π)⁶ D_Merc > 0` for both signs `s_G = ±1` on the
whole cell (`cellCheck_sound`).
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-! ### Cell `[123/160, 31/40]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[123/160, 31/40]`. -/
@[expose] def Dc13 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4227923074, 4341639524, true⟩, ⟨3861354525, 4259471168, true⟩, ⟨41692383888, 42399916367,
  true⟩, ⟨76895163273, 80727862103, true⟩, ⟨33179727838, 33655962394, true⟩, ⟨27463908618,
  29229662394, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[123/160, 31/40]`. -/
@[expose] def Oc13_0 : FIv × FIv × FIv :=
  (⟨44359560166458, 88334307790706, true⟩, ⟨-1443159225337, 400968729708, true⟩, ⟨-90558222133,
  179316805663, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[123/160, 31/40]`. -/
@[expose] def Oc13_1 : FIv × FIv × FIv :=
  (⟨42950516895383, 85803426397398, true⟩, ⟨-1385792518963, 409756802689, true⟩, ⟨-91969177039,
  173009807216, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[123/160, 31/40]`. -/
@[expose] def Oc13_2 : FIv × FIv × FIv :=
  (⟨41248905240285, 91188762155719, true⟩, ⟨-1553219259224, 527278103251, true⟩, ⟨-116454909678,
  203051110742, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[123/160, 31/40]`. -/
@[expose] def Oc13_3 : FIv × FIv × FIv :=
  (⟨41248905240285, 91188762155719, true⟩, ⟨-1553219259224, 527278103251, true⟩, ⟨-116454909678,
  203051110742, true⟩)

/-- One-dimensional piece of cell `[123/160, 31/40]`. -/
theorem c13_oneD : oneD 128 (Ecell (123/160) (31/40)) = Dc13 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[123/160, 31/40]`. -/
theorem c13_arc0 : outerArc (lamC 200) (Ecell (123/160) (31/40)) (Ecell (123/160) (31/40)).sq
    (dIof 200 Dc13.1 Dc13.2.2.2.2.1) 12 12 6 0 = Oc13_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[123/160, 31/40]`. -/
theorem c13_arc1 : outerArc (lamC 200) (Ecell (123/160) (31/40)) (Ecell (123/160) (31/40)).sq
    (dIof 200 Dc13.1 Dc13.2.2.2.2.1) 12 12 6 1 = Oc13_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[123/160, 31/40]`. -/
theorem c13_arc2 : outerArc (lamC 200) (Ecell (123/160) (31/40)) (Ecell (123/160) (31/40)).sq
    (dIof 200 Dc13.1 Dc13.2.2.2.2.1) 12 12 6 2 = Oc13_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[123/160, 31/40]`. -/
theorem c13_arc3 : outerArc (lamC 200) (Ecell (123/160) (31/40)) (Ecell (123/160) (31/40)).sq
    (dIof 200 Dc13.1 Dc13.2.2.2.2.1) 12 12 6 3 = Oc13_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[123/160, 31/40]`. -/
theorem c13_final : cellCheckOf 200 128 12 12 6 (123/160) (31/40) Dc13
    (add3 (add3 Oc13_0 Oc13_1) (add3 Oc13_2 Oc13_3)) = true := by decide +kernel

/-- **Certificate for the cell `[123/160, 31/40]`.** -/
theorem cell13 : cellCheck 200 128 12 12 6 (123/160) (31/40) = true :=
  cellCheck_of_pieces c13_oneD c13_arc0 c13_arc1 c13_arc2 c13_arc3 c13_final

/-! ### Cell `[31/40, 25/32]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[31/40, 25/32]`. -/
@[expose] def Dc14 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4252309394, 4368906720, true⟩, ⟨3995078650, 4413727813, true⟩, ⟨42183476357, 42915765201,
  true⟩, ⟨80292555428, 84385993868, true⟩, ⟨33354311975, 33841856865, true⟩, ⟨28411806859,
  30266507358, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[31/40, 25/32]`. -/
@[expose] def Oc14_0 : FIv × FIv × FIv :=
  (⟨44575219038292, 89980485750561, true⟩, ⟨-1511845515333, 418651351757, true⟩, ⟨-94558819307,
  187632987748, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[31/40, 25/32]`. -/
@[expose] def Oc14_1 : FIv × FIv × FIv :=
  (⟨43154753840628, 87405380448003, true⟩, ⟨-1451854982821, 428353868275, true⟩, ⟨-96121450015,
  181036942798, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[31/40, 25/32]`. -/
@[expose] def Oc14_2 : FIv × FIv × FIv :=
  (⟨41373724511147, 93006379545015, true⟩, ⟨-1627537582567, 550035910559, true⟩, ⟨-121652632499,
  212496732531, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[31/40, 25/32]`. -/
@[expose] def Oc14_3 : FIv × FIv × FIv :=
  (⟨41373724511147, 93006379545015, true⟩, ⟨-1627537582567, 550035910559, true⟩, ⟨-121652632499,
  212496732531, true⟩)

/-- One-dimensional piece of cell `[31/40, 25/32]`. -/
theorem c14_oneD : oneD 128 (Ecell (31/40) (25/32)) = Dc14 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[31/40, 25/32]`. -/
theorem c14_arc0 : outerArc (lamC 200) (Ecell (31/40) (25/32)) (Ecell (31/40) (25/32)).sq
    (dIof 200 Dc14.1 Dc14.2.2.2.2.1) 12 12 6 0 = Oc14_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[31/40, 25/32]`. -/
theorem c14_arc1 : outerArc (lamC 200) (Ecell (31/40) (25/32)) (Ecell (31/40) (25/32)).sq
    (dIof 200 Dc14.1 Dc14.2.2.2.2.1) 12 12 6 1 = Oc14_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[31/40, 25/32]`. -/
theorem c14_arc2 : outerArc (lamC 200) (Ecell (31/40) (25/32)) (Ecell (31/40) (25/32)).sq
    (dIof 200 Dc14.1 Dc14.2.2.2.2.1) 12 12 6 2 = Oc14_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[31/40, 25/32]`. -/
theorem c14_arc3 : outerArc (lamC 200) (Ecell (31/40) (25/32)) (Ecell (31/40) (25/32)).sq
    (dIof 200 Dc14.1 Dc14.2.2.2.2.1) 12 12 6 3 = Oc14_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[31/40, 25/32]`. -/
theorem c14_final : cellCheckOf 200 128 12 12 6 (31/40) (25/32) Dc14
    (add3 (add3 Oc14_0 Oc14_1) (add3 Oc14_2 Oc14_3)) = true := by decide +kernel

/-- **Certificate for the cell `[31/40, 25/32]`.** -/
theorem cell14 : cellCheck 200 128 12 12 6 (31/40) (25/32) = true :=
  cellCheck_of_pieces c14_oneD c14_arc0 c14_arc1 c14_arc2 c14_arc3 c14_final

/-! ### Cell `[25/32, 63/80]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[25/32, 63/80]`. -/
@[expose] def Dc15 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4277549053, 4397173839, true⟩, ⟨4136552308, 4577404113, true⟩, ⟨42696540906, 43455295726,
  true⟩, ⟨83930068062, 88310372129, true⟩, ⟨33534990071, 34034423469, true⟩, ⟨29414749727,
  31365647224, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[25/32, 63/80]`. -/
@[expose] def Oc15_0 : FIv × FIv × FIv :=
  (⟨37568865860949, 112732739314070, true⟩, ⟨-2496962501036, 799977159969, true⟩, ⟨-175184259209,
  322498487474, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[25/32, 63/80]`. -/
@[expose] def Oc15_1 : FIv × FIv × FIv :=
  (⟨36376772134571, 109657281020384, true⟩, ⟨-2398244625859, 827254130983, true⟩, ⟨-179248129024,
  311165388867, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[25/32, 63/80]`. -/
@[expose] def Oc15_2 : FIv × FIv × FIv :=
  (⟨34642342463024, 117536807695010, true⟩, ⟨-2667113889040, 962577593840, true⟩, ⟨-216514027761,
  362241892663, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[25/32, 63/80]`. -/
@[expose] def Oc15_3 : FIv × FIv × FIv :=
  (⟨34642342463024, 117536807695010, true⟩, ⟨-2667113889040, 962577593840, true⟩, ⟨-216514027761,
  362241892663, true⟩)

/-- One-dimensional piece of cell `[25/32, 63/80]`. -/
theorem c15_oneD : oneD 128 (Ecell (25/32) (63/80)) = Dc15 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[25/32, 63/80]`. -/
theorem c15_arc0 : outerArc (lamC 200) (Ecell (25/32) (63/80)) (Ecell (25/32) (63/80)).sq
    (dIof 200 Dc15.1 Dc15.2.2.2.2.1) 8 8 4 0 = Oc15_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[25/32, 63/80]`. -/
theorem c15_arc1 : outerArc (lamC 200) (Ecell (25/32) (63/80)) (Ecell (25/32) (63/80)).sq
    (dIof 200 Dc15.1 Dc15.2.2.2.2.1) 8 8 4 1 = Oc15_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[25/32, 63/80]`. -/
theorem c15_arc2 : outerArc (lamC 200) (Ecell (25/32) (63/80)) (Ecell (25/32) (63/80)).sq
    (dIof 200 Dc15.1 Dc15.2.2.2.2.1) 8 8 4 2 = Oc15_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[25/32, 63/80]`. -/
theorem c15_arc3 : outerArc (lamC 200) (Ecell (25/32) (63/80)) (Ecell (25/32) (63/80)).sq
    (dIof 200 Dc15.1 Dc15.2.2.2.2.1) 8 8 4 3 = Oc15_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[25/32, 63/80]`. -/
theorem c15_final : cellCheckOf 200 128 8 8 4 (25/32) (63/80) Dc15
    (add3 (add3 Oc15_0 Oc15_1) (add3 Oc15_2 Oc15_3)) = true := by decide +kernel

/-- **Certificate for the cell `[25/32, 63/80]`.** -/
theorem cell15 : cellCheck 200 128 8 8 4 (25/32) (63/80) = true :=
  cellCheck_of_pieces c15_oneD c15_arc0 c15_arc1 c15_arc2 c15_arc3 c15_final

/-! ### Cell `[63/80, 127/160]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[63/80, 127/160]`. -/
@[expose] def Dc16 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4303692046, 4426503065, true⟩, ⟨4286465851, 4751381154, true⟩, ⟨43233153377, 44020257702,
  true⟩, ⟨87832252740, 92529039787, true⟩, ⟨33722121248, 34234069202, true⟩, ⟨30477664890,
  32532846995, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[63/80, 127/160]`. -/
@[expose] def Oc16_0 : FIv × FIv × FIv :=
  (⟨37716047107190, 115814650479811, true⟩, ⟨-2646908927862, 841971714987, true⟩, ⟨-184376599524,
  341080582137, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[63/80, 127/160]`. -/
@[expose] def Oc16_1 : FIv × FIv × FIv :=
  (⟨36515289261430, 112669870271897, true⟩, ⟨-2542831588745, 872245781526, true⟩, ⟨-188879858334,
  329197623943, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[63/80, 127/160]`. -/
@[expose] def Oc16_2 : FIv × FIv × FIv :=
  (⟨34699847497470, 120977729649608, true⟩, ⟨-2829670230997, 1015183895705, true⟩, ⟨-227945964591,
  383241508901, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[63/80, 127/160]`. -/
@[expose] def Oc16_3 : FIv × FIv × FIv :=
  (⟨34699847497470, 120977729649608, true⟩, ⟨-2829670230997, 1015183895705, true⟩, ⟨-227945964591,
  383241508901, true⟩)

/-- One-dimensional piece of cell `[63/80, 127/160]`. -/
theorem c16_oneD : oneD 128 (Ecell (63/80) (127/160)) = Dc16 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[63/80, 127/160]`. -/
theorem c16_arc0 : outerArc (lamC 200) (Ecell (63/80) (127/160)) (Ecell (63/80) (127/160)).sq
    (dIof 200 Dc16.1 Dc16.2.2.2.2.1) 8 8 4 0 = Oc16_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[63/80, 127/160]`. -/
theorem c16_arc1 : outerArc (lamC 200) (Ecell (63/80) (127/160)) (Ecell (63/80) (127/160)).sq
    (dIof 200 Dc16.1 Dc16.2.2.2.2.1) 8 8 4 1 = Oc16_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[63/80, 127/160]`. -/
theorem c16_arc2 : outerArc (lamC 200) (Ecell (63/80) (127/160)) (Ecell (63/80) (127/160)).sq
    (dIof 200 Dc16.1 Dc16.2.2.2.2.1) 8 8 4 2 = Oc16_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[63/80, 127/160]`. -/
theorem c16_arc3 : outerArc (lamC 200) (Ecell (63/80) (127/160)) (Ecell (63/80) (127/160)).sq
    (dIof 200 Dc16.1 Dc16.2.2.2.2.1) 8 8 4 3 = Oc16_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[63/80, 127/160]`. -/
theorem c16_final : cellCheckOf 200 128 8 8 4 (63/80) (127/160) Dc16
    (add3 (add3 Oc16_0 Oc16_1) (add3 Oc16_2 Oc16_3)) = true := by decide +kernel

/-- **Certificate for the cell `[63/80, 127/160]`.** -/
theorem cell16 : cellCheck 200 128 8 8 4 (63/80) (127/160) = true :=
  cellCheck_of_pieces c16_oneD c16_arc0 c16_arc1 c16_arc2 c16_arc3 c16_final

/-! ### Cell `[127/160, 4/5]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[127/160, 4/5]`. -/
@[expose] def Dc17 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4330792881, 4456962508, true⟩, ⟨4445593363, 4936652185, true⟩, ⟨43795053253, 44612588067,
  true⟩, ⟨92026979322, 97073947502, true⟩, ⟨33916097292, 34441239314, true⟩, ⟨31606081147,
  33774599130, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[127/160, 4/5]`. -/
@[expose] def Oc17_0 : FIv × FIv × FIv :=
  (⟨37889545564326, 119231704844101, true⟩, ⟨-2814106973475, 888466193220, true⟩, ⟨-194517664945,
  361701157451, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[127/160, 4/5]`. -/
@[expose] def Oc17_1 : FIv × FIv × FIv :=
  (⟨36679131438382, 116011261671291, true⟩, ⟨-2704082318033, 921997592036, true⟩, ⟨-199520671268,
  349208033135, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[127/160, 4/5]`. -/
@[expose] def Oc17_2 : FIv × FIv × FIv :=
  (⟨34775323677016, 124828886137554, true⟩, ⟨-3014009801367, 1076631169409, true⟩, ⟨-240763820103,
  406955223485, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[127/160, 4/5]`. -/
@[expose] def Oc17_3 : FIv × FIv × FIv :=
  (⟨34775323677016, 124828886137554, true⟩, ⟨-3014009801367, 1076631169409, true⟩, ⟨-240763820103,
  406955223485, true⟩)

/-- One-dimensional piece of cell `[127/160, 4/5]`. -/
theorem c17_oneD : oneD 128 (Ecell (127/160) (4/5)) = Dc17 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[127/160, 4/5]`. -/
theorem c17_arc0 : outerArc (lamC 200) (Ecell (127/160) (4/5)) (Ecell (127/160) (4/5)).sq
    (dIof 200 Dc17.1 Dc17.2.2.2.2.1) 8 8 4 0 = Oc17_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[127/160, 4/5]`. -/
theorem c17_arc1 : outerArc (lamC 200) (Ecell (127/160) (4/5)) (Ecell (127/160) (4/5)).sq
    (dIof 200 Dc17.1 Dc17.2.2.2.2.1) 8 8 4 1 = Oc17_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[127/160, 4/5]`. -/
theorem c17_arc2 : outerArc (lamC 200) (Ecell (127/160) (4/5)) (Ecell (127/160) (4/5)).sq
    (dIof 200 Dc17.1 Dc17.2.2.2.2.1) 8 8 4 2 = Oc17_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[127/160, 4/5]`. -/
theorem c17_arc3 : outerArc (lamC 200) (Ecell (127/160) (4/5)) (Ecell (127/160) (4/5)).sq
    (dIof 200 Dc17.1 Dc17.2.2.2.2.1) 8 8 4 3 = Oc17_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[127/160, 4/5]`. -/
theorem c17_final : cellCheckOf 200 128 8 8 4 (127/160) (4/5) Dc17
    (add3 (add3 Oc17_0 Oc17_1) (add3 Oc17_2 Oc17_3)) = true := by decide +kernel

/-- **Certificate for the cell `[127/160, 4/5]`.** -/
theorem cell17 : cellCheck 200 128 8 8 4 (127/160) (4/5) = true :=
  cellCheck_of_pieces c17_oneD c17_arc0 c17_arc1 c17_arc2 c17_arc3 c17_final

/-! ### Cell `[4/5, 129/160]`, grids `(8, 8, 4)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[4/5, 129/160]`. -/
@[expose] def Dc18 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4358911107, 4488626980, true⟩, ⟨4614805642, 5134341004, true⟩, ⟨44384165913, 45234437472,
  true⟩, ⟨96545999296, 101981640565, true⟩, ⟨34117346632, 34656422228, true⟩, ⟨32806222280,
  35098241761, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[4/5, 129/160]`. -/
@[expose] def Oc18_0 : FIv × FIv × FIv :=
  (⟨38090610004109, 123032561014804, true⟩, ⟨-3001637877671, 940182953785, true⟩, ⟨-205754781311,
  384703023563, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[4/5, 129/160]`. -/
@[expose] def Oc18_1 : FIv × FIv × FIv :=
  (⟨36869509944132, 119729359963363, true⟩, ⟨-2884978817723, 977322121834, true⟩, ⟨-211331255427,
  371532323664, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[4/5, 129/160]`. -/
@[expose] def Oc18_2 : FIv × FIv × FIv :=
  (⟨34869114797469, 129161160421603, true⟩, ⟨-3224872397251, 1147046810507, true⟩, ⟨-255232747318,
  433953406507, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[4/5, 129/160]`. -/
@[expose] def Oc18_3 : FIv × FIv × FIv :=
  (⟨34869114797469, 129161160421603, true⟩, ⟨-3224872397251, 1147046810507, true⟩, ⟨-255232747318,
  433953406507, true⟩)

/-- One-dimensional piece of cell `[4/5, 129/160]`. -/
theorem c18_oneD : oneD 128 (Ecell (4/5) (129/160)) = Dc18 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[4/5, 129/160]`. -/
theorem c18_arc0 : outerArc (lamC 200) (Ecell (4/5) (129/160)) (Ecell (4/5) (129/160)).sq
    (dIof 200 Dc18.1 Dc18.2.2.2.2.1) 8 8 4 0 = Oc18_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[4/5, 129/160]`. -/
theorem c18_arc1 : outerArc (lamC 200) (Ecell (4/5) (129/160)) (Ecell (4/5) (129/160)).sq
    (dIof 200 Dc18.1 Dc18.2.2.2.2.1) 8 8 4 1 = Oc18_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[4/5, 129/160]`. -/
theorem c18_arc2 : outerArc (lamC 200) (Ecell (4/5) (129/160)) (Ecell (4/5) (129/160)).sq
    (dIof 200 Dc18.1 Dc18.2.2.2.2.1) 8 8 4 2 = Oc18_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[4/5, 129/160]`. -/
theorem c18_arc3 : outerArc (lamC 200) (Ecell (4/5) (129/160)) (Ecell (4/5) (129/160)).sq
    (dIof 200 Dc18.1 Dc18.2.2.2.2.1) 8 8 4 3 = Oc18_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[4/5, 129/160]`. -/
theorem c18_final : cellCheckOf 200 128 8 8 4 (4/5) (129/160) Dc18
    (add3 (add3 Oc18_0 Oc18_1) (add3 Oc18_2 Oc18_3)) = true := by decide +kernel

/-- **Certificate for the cell `[4/5, 129/160]`.** -/
theorem cell18 : cellCheck 200 128 8 8 4 (4/5) (129/160) = true :=
  cellCheck_of_pieces c18_oneD c18_arc0 c18_arc1 c18_arc2 c18_arc3 c18_final

end PlasmaLean.Design.LandremanFamily2Cert
