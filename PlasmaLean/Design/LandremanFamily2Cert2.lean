/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Cert2b

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 2

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

The remaining cells of group 2 are in `PlasmaLean.Design.LandremanFamily2Cert2b` (imported here;
split so that each process stays within the laptop memory budget).
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

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[23/32, 29/40]`. -/
theorem c5_arc0 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 0 = Oc5_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[23/32, 29/40]`. -/
theorem c5_arc1 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 1 = Oc5_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[23/32, 29/40]`. -/
theorem c5_arc2 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 2 = Oc5_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[23/32, 29/40]`. -/
theorem c5_arc3 : outerArc (lamC 200) (Ecell (23/32) (29/40)) (Ecell (23/32) (29/40)).sq
    (dIof 200 Dc5.1 Dc5.2.2.2.2.1) 12 12 6 3 = Oc5_3 := by
  f2_arc_cert

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

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[29/40, 117/160]`. -/
theorem c6_arc0 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 0 = Oc6_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[29/40, 117/160]`. -/
theorem c6_arc1 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 1 = Oc6_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[29/40, 117/160]`. -/
theorem c6_arc2 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 2 = Oc6_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[29/40, 117/160]`. -/
theorem c6_arc3 : outerArc (lamC 200) (Ecell (29/40) (117/160)) (Ecell (29/40) (117/160)).sq
    (dIof 200 Dc6.1 Dc6.2.2.2.2.1) 12 12 6 3 = Oc6_3 := by
  f2_arc_cert

/-- Final combination of cell `[29/40, 117/160]`. -/
theorem c6_final : cellCheckOf 200 128 12 12 6 (29/40) (117/160) Dc6
    (add3 (add3 Oc6_0 Oc6_1) (add3 Oc6_2 Oc6_3)) = true := by fiv_cert

/-- **Certificate for the cell `[29/40, 117/160]`.** -/
theorem cell6 : cellCheck 200 128 12 12 6 (29/40) (117/160) = true :=
  cellCheck_of_pieces c6_oneD c6_arc0 c6_arc1 c6_arc2 c6_arc3 c6_final

end PlasmaLean.Design.LandremanFamily2Cert
