/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Quad
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 3

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

/-! ### Cell `[119/160, 3/4]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[119/160, 3/4]`. -/
@[expose] def Dc9 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4138043663, 4241498937, true⟩, ⟨3392505121, 3722150497, true⟩, ⟨39920936894, 40543713587,
  true⟩, ⟨65307592245, 68304392662, true⟩, ⟨32536106379, 32972082656, true⟩, ⟨24141123772,
  25610269887, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[119/160, 3/4]`. -/
@[expose] def Oc9_0 : FIv × FIv × FIv :=
  (⟨43794881376797, 83163679228063, true⟩, ⟨-1221934839603, 344447131108, true⟩, ⟨-77753926479,
  152540697887, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[119/160, 3/4]`. -/
@[expose] def Oc9_1 : FIv × FIv × FIv :=
  (⟨42420499850709, 80774756018718, true⟩, ⟨-1173136795421, 350922931459, true⟩, ⟨-78700800105,
  147183192038, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[119/160, 3/4]`. -/
@[expose] def Oc9_2 : FIv × FIv × FIv :=
  (⟨40985493659111, 85473223747525, true⟩, ⟨-1314849106177, 454204460955, true⟩, ⟨-99848588757,
  172757069896, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[119/160, 3/4]`. -/
@[expose] def Oc9_3 : FIv × FIv × FIv :=
  (⟨40985493659111, 85473223747525, true⟩, ⟨-1314849106177, 454204460955, true⟩, ⟨-99848588757,
  172757069896, true⟩)

/-- One-dimensional piece of cell `[119/160, 3/4]`. -/
theorem c9_oneD : oneD 128 (Ecell (119/160) (3/4)) = Dc9 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[119/160, 3/4]`. -/
theorem c9_arc0 : outerArc (lamC 200) (Ecell (119/160) (3/4)) (Ecell (119/160) (3/4)).sq
    (dIof 200 Dc9.1 Dc9.2.2.2.2.1) 12 12 6 0 = Oc9_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[119/160, 3/4]`. -/
theorem c9_arc1 : outerArc (lamC 200) (Ecell (119/160) (3/4)) (Ecell (119/160) (3/4)).sq
    (dIof 200 Dc9.1 Dc9.2.2.2.2.1) 12 12 6 1 = Oc9_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[119/160, 3/4]`. -/
theorem c9_arc2 : outerArc (lamC 200) (Ecell (119/160) (3/4)) (Ecell (119/160) (3/4)).sq
    (dIof 200 Dc9.1 Dc9.2.2.2.2.1) 12 12 6 2 = Oc9_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[119/160, 3/4]`. -/
theorem c9_arc3 : outerArc (lamC 200) (Ecell (119/160) (3/4)) (Ecell (119/160) (3/4)).sq
    (dIof 200 Dc9.1 Dc9.2.2.2.2.1) 12 12 6 3 = Oc9_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[119/160, 3/4]`. -/
theorem c9_final : cellCheckOf 200 128 12 12 6 (119/160) (3/4) Dc9
    (add3 (add3 Oc9_0 Oc9_1) (add3 Oc9_2 Oc9_3)) = true := by fiv_cert

/-- **Certificate for the cell `[119/160, 3/4]`.** -/
theorem cell9 : cellCheck 200 128 12 12 6 (119/160) (3/4) = true :=
  cellCheck_of_pieces c9_oneD c9_arc0 c9_arc1 c9_arc2 c9_arc3 c9_final

/-! ### Cell `[3/4, 121/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[3/4, 121/160]`. -/
@[expose] def Dc10 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4159442079, 4265291186, true⟩, ⟨3500811971, 3845784986, true⟩, ⟨40337248125, 40979316874,
  true⟩, ⟨67938606592, 71117837583, true⟩, ⟨32689366869, 33134730436, true⟩, ⟨24908636130,
  26444187940, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[3/4, 121/160]`. -/
@[expose] def Oc10_0 : FIv × FIv × FIv :=
  (⟨43894561037177, 84267000194088, true⟩, ⟨-1270357618910, 356736414141, true⟩, ⟨-80536968836,
  158395435251, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[3/4, 121/160]`. -/
@[expose] def Oc10_1 : FIv × FIv × FIv :=
  (⟨42513044492036, 81847326593794, true⟩, ⟨-1219667214119, 363603878819, true⟩, ⟨-81581280015,
  152828026450, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[3/4, 121/160]`. -/
@[expose] def Oc10_2 : FIv × FIv × FIv :=
  (⟨41017196517941, 86696547969809, true⟩, ⟨-1366937165302, 470168973821, true⟩, ⟨-103460854504,
  179371413275, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[3/4, 121/160]`. -/
@[expose] def Oc10_3 : FIv × FIv × FIv :=
  (⟨41017196517941, 86696547969809, true⟩, ⟨-1366937165302, 470168973821, true⟩, ⟨-103460854504,
  179371413275, true⟩)

/-- One-dimensional piece of cell `[3/4, 121/160]`. -/
theorem c10_oneD : oneD 128 (Ecell (3/4) (121/160)) = Dc10 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[3/4, 121/160]`. -/
theorem c10_arc0 : outerArc (lamC 200) (Ecell (3/4) (121/160)) (Ecell (3/4) (121/160)).sq
    (dIof 200 Dc10.1 Dc10.2.2.2.2.1) 12 12 6 0 = Oc10_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[3/4, 121/160]`. -/
theorem c10_arc1 : outerArc (lamC 200) (Ecell (3/4) (121/160)) (Ecell (3/4) (121/160)).sq
    (dIof 200 Dc10.1 Dc10.2.2.2.2.1) 12 12 6 1 = Oc10_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[3/4, 121/160]`. -/
theorem c10_arc2 : outerArc (lamC 200) (Ecell (3/4) (121/160)) (Ecell (3/4) (121/160)).sq
    (dIof 200 Dc10.1 Dc10.2.2.2.2.1) 12 12 6 2 = Oc10_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[3/4, 121/160]`. -/
theorem c10_arc3 : outerArc (lamC 200) (Ecell (3/4) (121/160)) (Ecell (3/4) (121/160)).sq
    (dIof 200 Dc10.1 Dc10.2.2.2.2.1) 12 12 6 3 = Oc10_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[3/4, 121/160]`. -/
theorem c10_final : cellCheckOf 200 128 12 12 6 (3/4) (121/160) Dc10
    (add3 (add3 Oc10_0 Oc10_1) (add3 Oc10_2 Oc10_3)) = true := by fiv_cert

/-- **Certificate for the cell `[3/4, 121/160]`.** -/
theorem cell10 : cellCheck 200 128 12 12 6 (3/4) (121/160) = true :=
  cellCheck_of_pieces c10_oneD c10_arc0 c10_arc1 c10_arc2 c10_arc3 c10_final

/-! ### Cell `[121/160, 61/80]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[121/160, 61/80]`. -/
@[expose] def Dc11 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4181530163, 4289881890, true⟩, ⟨3614747681, 3976163596, true⟩, ⟨40770516766, 41433067912,
  true⟩, ⟨70736377299, 74114387057, true⟩, ⟨32847547490, 33302728216, true⟩, ⟨25716076077,
  27322856284, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[121/160, 61/80]`. -/
@[expose] def Oc11_0 : FIv × FIv × FIv :=
  (⟨44020440001078, 85490702516712, true⟩, ⟨-1323067548260, 370213052447, true⟩, ⟨-83585388702,
  164775666141, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[121/160, 61/80]`. -/
@[expose] def Oc11_1 : FIv × FIv × FIv :=
  (⟨42630816595481, 83037270952670, true⟩, ⟨-1270329510317, 377573540510, true⟩, ⟨-84738388456,
  158981600537, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[121/160, 61/80]`. -/
@[expose] def Oc11_2 : FIv × FIv × FIv :=
  (⟨41071279691825, 88048577051811, true⟩, ⟨-1423624342683, 487546999472, true⟩, ⟨-107405742267,
  186575417001, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[121/160, 61/80]`. -/
@[expose] def Oc11_3 : FIv × FIv × FIv :=
  (⟨41071279691825, 88048577051811, true⟩, ⟨-1423624342683, 487546999472, true⟩, ⟨-107405742267,
  186575417001, true⟩)

/-- One-dimensional piece of cell `[121/160, 61/80]`. -/
theorem c11_oneD : oneD 128 (Ecell (121/160) (61/80)) = Dc11 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[121/160, 61/80]`. -/
theorem c11_arc0 : outerArc (lamC 200) (Ecell (121/160) (61/80)) (Ecell (121/160) (61/80)).sq
    (dIof 200 Dc11.1 Dc11.2.2.2.2.1) 12 12 6 0 = Oc11_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[121/160, 61/80]`. -/
theorem c11_arc1 : outerArc (lamC 200) (Ecell (121/160) (61/80)) (Ecell (121/160) (61/80)).sq
    (dIof 200 Dc11.1 Dc11.2.2.2.2.1) 12 12 6 1 = Oc11_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[121/160, 61/80]`. -/
theorem c11_arc2 : outerArc (lamC 200) (Ecell (121/160) (61/80)) (Ecell (121/160) (61/80)).sq
    (dIof 200 Dc11.1 Dc11.2.2.2.2.1) 12 12 6 2 = Oc11_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[121/160, 61/80]`. -/
theorem c11_arc3 : outerArc (lamC 200) (Ecell (121/160) (61/80)) (Ecell (121/160) (61/80)).sq
    (dIof 200 Dc11.1 Dc11.2.2.2.2.1) 12 12 6 3 = Oc11_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[121/160, 61/80]`. -/
theorem c11_final : cellCheckOf 200 128 12 12 6 (121/160) (61/80) Dc11
    (add3 (add3 Oc11_0 Oc11_1) (add3 Oc11_2 Oc11_3)) = true := by fiv_cert

/-- **Certificate for the cell `[121/160, 61/80]`.** -/
theorem cell11 : cellCheck 200 128 12 12 6 (121/160) (61/80) = true :=
  cellCheck_of_pieces c11_oneD c11_arc0 c11_arc1 c11_arc2 c11_arc3 c11_final

/-! ### Cell `[61/80, 123/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[61/80, 123/160]`. -/
@[expose] def Dc12 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4204344121, 4315315321, true⟩, ⟨3734762289, 4113849871, true⟩, ⟨41221831958, 41906163916,
  true⟩, ⟨73716187376, 77311272378, true⟩, ⟨33010907655, 33476367046, true⟩, ⟨26566648911,
  28249975705, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[61/80, 123/160]`. -/
@[expose] def Oc12_0 : FIv × FIv × FIv :=
  (⟨44175064225113, 86842188121375, true⟩, ⟨-1380447416855, 384887461713, true⟩, ⟨-86912534038,
  171721927802, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[61/80, 123/160]`. -/
@[expose] def Oc12_1 : FIv × FIv × FIv :=
  (⟨42776297297875, 84351753992647, true⟩, ⟨-1325489963895, 392857992362, true⟩, ⟨-88186848248,
  165681997014, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[61/80, 123/160]`. -/
@[expose] def Oc12_2 : FIv × FIv × FIv :=
  (⟨41148340345882, 89541100205475, true⟩, ⟨-1485478101596, 506507610493, true⟩, ⟨-111719659890,
  194437238076, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[61/80, 123/160]`. -/
@[expose] def Oc12_3 : FIv × FIv × FIv :=
  (⟨41148340345882, 89541100205475, true⟩, ⟨-1485478101596, 506507610493, true⟩, ⟨-111719659890,
  194437238076, true⟩)

/-- One-dimensional piece of cell `[61/80, 123/160]`. -/
theorem c12_oneD : oneD 128 (Ecell (61/80) (123/160)) = Dc12 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[61/80, 123/160]`. -/
theorem c12_arc0 : outerArc (lamC 200) (Ecell (61/80) (123/160)) (Ecell (61/80) (123/160)).sq
    (dIof 200 Dc12.1 Dc12.2.2.2.2.1) 12 12 6 0 = Oc12_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[61/80, 123/160]`. -/
theorem c12_arc1 : outerArc (lamC 200) (Ecell (61/80) (123/160)) (Ecell (61/80) (123/160)).sq
    (dIof 200 Dc12.1 Dc12.2.2.2.2.1) 12 12 6 1 = Oc12_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[61/80, 123/160]`. -/
theorem c12_arc2 : outerArc (lamC 200) (Ecell (61/80) (123/160)) (Ecell (61/80) (123/160)).sq
    (dIof 200 Dc12.1 Dc12.2.2.2.2.1) 12 12 6 2 = Oc12_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[61/80, 123/160]`. -/
theorem c12_arc3 : outerArc (lamC 200) (Ecell (61/80) (123/160)) (Ecell (61/80) (123/160)).sq
    (dIof 200 Dc12.1 Dc12.2.2.2.2.1) 12 12 6 3 = Oc12_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[61/80, 123/160]`. -/
theorem c12_final : cellCheckOf 200 128 12 12 6 (61/80) (123/160) Dc12
    (add3 (add3 Oc12_0 Oc12_1) (add3 Oc12_2 Oc12_3)) = true := by fiv_cert

/-- **Certificate for the cell `[61/80, 123/160]`.** -/
theorem cell12 : cellCheck 200 128 12 12 6 (61/80) (123/160) = true :=
  cellCheck_of_pieces c12_oneD c12_arc0 c12_arc1 c12_arc2 c12_arc3 c12_final

end PlasmaLean.Design.LandremanFamily2Cert
