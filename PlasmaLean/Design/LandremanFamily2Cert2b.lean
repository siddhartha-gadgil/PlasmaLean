/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2ArcCert

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 2, second part

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

The first cells of group 2 are in `PlasmaLean.Design.LandremanFamily2Cert2`, which imports
this module (split so that each process stays within the laptop memory budget).
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

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

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[117/160, 59/80]`. -/
theorem c7_arc0 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 0 = Oc7_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[117/160, 59/80]`. -/
theorem c7_arc1 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 1 = Oc7_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[117/160, 59/80]`. -/
theorem c7_arc2 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 2 = Oc7_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[117/160, 59/80]`. -/
theorem c7_arc3 : outerArc (lamC 200) (Ecell (117/160) (59/80)) (Ecell (117/160) (59/80)).sq
    (dIof 200 Dc7.1 Dc7.2.2.2.2.1) 12 12 6 3 = Oc7_3 := by
  f2_arc_cert

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

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[59/80, 119/160]`. -/
theorem c8_arc0 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 0 = Oc8_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[59/80, 119/160]`. -/
theorem c8_arc1 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 1 = Oc8_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[59/80, 119/160]`. -/
theorem c8_arc2 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 2 = Oc8_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[59/80, 119/160]`. -/
theorem c8_arc3 : outerArc (lamC 200) (Ecell (59/80) (119/160)) (Ecell (59/80) (119/160)).sq
    (dIof 200 Dc8.1 Dc8.2.2.2.2.1) 12 12 6 3 = Oc8_3 := by
  f2_arc_cert

/-- Final combination of cell `[59/80, 119/160]`. -/
theorem c8_final : cellCheckOf 200 128 12 12 6 (59/80) (119/160) Dc8
    (add3 (add3 Oc8_0 Oc8_1) (add3 Oc8_2 Oc8_3)) = true := by fiv_cert

/-- **Certificate for the cell `[59/80, 119/160]`.** -/
theorem cell8 : cellCheck 200 128 12 12 6 (59/80) (119/160) = true :=
  cellCheck_of_pieces c8_oneD c8_arc0 c8_arc1 c8_arc2 c8_arc3 c8_final

end PlasmaLean.Design.LandremanFamily2Cert
