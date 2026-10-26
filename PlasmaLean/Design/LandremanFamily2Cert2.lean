/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Quad
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 2

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

/-! ### Cell `[23/32, 29/40]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[23/32, 29/40]`. -/
@[expose] def Dc5 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4058710050, 4153540662, true⟩, ⟨3007968753, 3285604352, true⟩, ⟨38406458498, 38962177453,
  true⟩, ⟨56197657922, 58597217312, true⟩, ⟨31967708328, 32369896263, true⟩, ⟨21416278181,
  22659961386, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[23/32, 29/40]`. -/
@[expose] def Oc5_0 : FIv × FIv × FIv :=
  (⟨43655635275563, 79761939537474, true⟩, ⟨-1062336271435, 304484579432, true⟩, ⟨-68709052104,
  133294929818, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[23/32, 29/40]`. -/
@[expose] def Oc5_1 : FIv × FIv × FIv :=
  (⟨42300559165905, 77469743717852, true⟩, ⟨-1019842917651, 309782179890, true⟩, ⟨-69351187986,
  128637864286, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[23/32, 29/40]`. -/
@[expose] def Oc5_2 : FIv × FIv × FIv :=
  (⟨41073899393372, 81673916430836, true⟩, ⟨-1143308211150, 401770946156, true⟩, ⟨-88084886404,
  151034436847, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[23/32, 29/40]`. -/
@[expose] def Oc5_3 : FIv × FIv × FIv :=
  (⟨41073899393372, 81673916430836, true⟩, ⟨-1143308211150, 401770946156, true⟩, ⟨-88084886404,
  151034436847, true⟩)

/-- One-dimensional piece of cell `[23/32, 29/40]`. -/
theorem c5_oneD : oneD 128 (Ecell (23/32) (29/40)) = Dc5 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[23/32, 29/40]`. -/
theorem c5_arc0 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 0 = Oc5_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[23/32, 29/40]`. -/
theorem c5_arc1 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 1 = Oc5_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[23/32, 29/40]`. -/
theorem c5_arc2 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 2 = Oc5_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[23/32, 29/40]`. -/
theorem c5_arc3 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 3 = Oc5_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[23/32, 29/40]`. -/
theorem c5_final : cellCheckOf 200 128 12 12 6 (23/32) (29/40) Dc5
    (add3 (add3 Oc5_0 Oc5_1) (add3 Oc5_2 Oc5_3)) = true := by fiv_cert

/-- **Certificate for the cell `[23/32, 29/40]`.** -/
theorem cell5 : cellCheck 200 128 12 12 6 (23/32) (29/40) = true :=
  cellCheck_of_pieces c5_oneD c5_arc0 c5_arc1 c5_arc2 c5_arc3 c5_final

/-! ### Cell `[29/40, 117/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[29/40, 117/160]`. -/
@[expose] def Dc6 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4077662553, 4174518951, true⟩, ⟨3097472421, 3386875338, true⟩, ⟨38764157401, 39335281029,
  true⟩, ⟨58285186714, 60816813198, true⟩, ⟨32103526991, 32513645778, true⟩, ⟨22050497813,
  23345218722, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[29/40, 117/160]`. -/
@[expose] def Oc6_0 : FIv × FIv × FIv :=
  (⟨43652509110882, 80475773259002, true⟩, ⟨-1097829799127, 313295339037, true⟩, ⟨-70700663899,
  137566816508, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[29/40, 117/160]`. -/
@[expose] def Oc6_1 : FIv × FIv × FIv :=
  (⟨42293955080101, 78162949558722, true⟩, ⟨-1053924425206, 318857157048, true⟩, ⟨-71408403754,
  132752743513, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[29/40, 117/160]`. -/
@[expose] def Oc6_2 : FIv × FIv × FIv :=
  (⟨41020293746579, 82475629547912, true⟩, ⟨-1181403102580, 413363298579, true⟩, ⟨-90673507737,
  155846679665, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[29/40, 117/160]`. -/
@[expose] def Oc6_3 : FIv × FIv × FIv :=
  (⟨41020293746579, 82475629547912, true⟩, ⟨-1181403102580, 413363298579, true⟩, ⟨-90673507737,
  155846679665, true⟩)

/-- One-dimensional piece of cell `[29/40, 117/160]`. -/
theorem c6_oneD : oneD 128 (Ecell (29/40) (117/160)) = Dc6 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[29/40, 117/160]`. -/
theorem c6_arc0 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 0 = Oc6_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[29/40, 117/160]`. -/
theorem c6_arc1 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 1 = Oc6_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[29/40, 117/160]`. -/
theorem c6_arc2 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 2 = Oc6_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[29/40, 117/160]`. -/
theorem c6_arc3 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 3 = Oc6_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[29/40, 117/160]`. -/
theorem c6_final : cellCheckOf 200 128 12 12 6 (29/40) (117/160) Dc6
    (add3 (add3 Oc6_0 Oc6_1) (add3 Oc6_2 Oc6_3)) = true := by fiv_cert

/-- **Certificate for the cell `[29/40, 117/160]`.** -/
theorem cell6 : cellCheck 200 128 12 12 6 (29/40) (117/160) = true :=
  cellCheck_of_pieces c6_oneD c6_arc0 c6_arc1 c6_arc2 c6_arc3 c6_final

/-! ### Cell `[117/160, 59/80]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[117/160, 59/80]`. -/
@[expose] def Dc7 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4097183981, 4196149285, true⟩, ⟨3191187661, 3493132473, true⟩, ⟨39135272881, 39722659465,
  true⟩, ⟨60492536147, 63166931797, true⟩, ⟨32243401709, 32661780613, true⟩, ⟨22714561159,
  24063659518, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[117/160, 59/80]`. -/
@[expose] def Oc7_0 : FIv × FIv × FIv :=
  (⟨43674234810706, 81276382291915, true⟩, ⟨-1136057524847, 322839003352, true⟩, ⟨-72860130310,
  142174010536, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[117/160, 59/80]`. -/
@[expose] def Oc7_1 : FIv × FIv × FIv :=
  (⟨42311321699598, 78940645048287, true⟩, ⟨-1090637385675, 328691413404, true⟩, ⟨-73639794739,
  137191425413, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[117/160, 59/80]`. -/
@[expose] def Oc7_2 : FIv × FIv × FIv :=
  (⟨40987450093058, 83371393451127, true⟩, ⟨-1222483007940, 425908860535, true⟩, ⟨-93483094950,
  161045545616, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[117/160, 59/80]`. -/
@[expose] def Oc7_3 : FIv × FIv × FIv :=
  (⟨40987450093058, 83371393451127, true⟩, ⟨-1222483007940, 425908860535, true⟩, ⟨-93483094950,
  161045545616, true⟩)

/-- One-dimensional piece of cell `[117/160, 59/80]`. -/
theorem c7_oneD : oneD 128 (Ecell (117/160) (59/80)) = Dc7 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[117/160, 59/80]`. -/
theorem c7_arc0 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 0 = Oc7_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[117/160, 59/80]`. -/
theorem c7_arc1 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 1 = Oc7_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[117/160, 59/80]`. -/
theorem c7_arc2 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 2 = Oc7_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[117/160, 59/80]`. -/
theorem c7_arc3 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 3 = Oc7_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[117/160, 59/80]`. -/
theorem c7_final : cellCheckOf 200 128 12 12 6 (117/160) (59/80) Dc7
    (add3 (add3 Oc7_0 Oc7_1) (add3 Oc7_2 Oc7_3)) = true := by fiv_cert

/-- **Certificate for the cell `[117/160, 59/80]`.** -/
theorem cell7 : cellCheck 200 128 12 12 6 (117/160) (59/80) = true :=
  cellCheck_of_pieces c7_oneD c7_arc0 c7_arc1 c7_arc2 c7_arc3 c7_final

/-! ### Cell `[59/80, 119/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[59/80, 119/160]`. -/
@[expose] def Dc8 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4117301352, 4218464252, true⟩, ⟨3289420059, 3604752493, true⟩, ⟨39520584381, 40125162639,
  true⟩, ⟨62829658810, 65658676933, true⟩, ⟨32387525688, 32814515805, true⟩, ⟨23410641012,
  24817765704, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[59/80, 119/160]`. -/
@[expose] def Oc8_0 : FIv × FIv × FIv :=
  (⟨43721467460582, 82169949300247, true⟩, ⟨-1177310757259, 333193968976, true⟩, ⟨-75204286316,
  147150911998, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[59/80, 119/160]`. -/
@[expose] def Oc8_1 : FIv × FIv × FIv :=
  (⟨42353297861795, 79808885664208, true⟩, ⟨-1130263119595, 339351630207, true⟩, ⟨-76063278633,
  141987884013, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[59/80, 119/160]`. -/
@[expose] def Oc8_2 : FIv × FIv × FIv :=
  (⟨40975711037493, 84367980077606, true⟩, ⟨-1266847753143, 439494442789, true⟩, ⟨-96533542858,
  166667895709, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[59/80, 119/160]`. -/
@[expose] def Oc8_3 : FIv × FIv × FIv :=
  (⟨40975711037493, 84367980077606, true⟩, ⟨-1266847753143, 439494442789, true⟩, ⟨-96533542858,
  166667895709, true⟩)

/-- One-dimensional piece of cell `[59/80, 119/160]`. -/
theorem c8_oneD : oneD 128 (Ecell (59/80) (119/160)) = Dc8 := eq6_sound (by oned_cert)

/-- Outer-arc piece 0 of cell `[59/80, 119/160]`. -/
theorem c8_arc0 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 0 = Oc8_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[59/80, 119/160]`. -/
theorem c8_arc1 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 1 = Oc8_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[59/80, 119/160]`. -/
theorem c8_arc2 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 2 = Oc8_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[59/80, 119/160]`. -/
theorem c8_arc3 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 3 = Oc8_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[59/80, 119/160]`. -/
theorem c8_final : cellCheckOf 200 128 12 12 6 (59/80) (119/160) Dc8
    (add3 (add3 Oc8_0 Oc8_1) (add3 Oc8_2 Oc8_3)) = true := by fiv_cert

/-- **Certificate for the cell `[59/80, 119/160]`.** -/
theorem cell8 : cellCheck 200 128 12 12 6 (59/80) (119/160) = true :=
  cellCheck_of_pieces c8_oneD c8_arc0 c8_arc1 c8_arc2 c8_arc3 c8_final

end PlasmaLean.Design.LandremanFamily2Cert
