/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Cert6b

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 6

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

The remaining cells of group 6 are in `PlasmaLean.Design.LandremanFamily2Cert6b` (imported here;
split so that each process stays within the laptop memory budget).
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-! ### Cell `[137/160, 69/80]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[137/160, 69/80]`. -/
@[expose] def Dc27 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4671131346, 4844982364, true⟩, ⟨6810022017, 7761268604, true⟩, ⟨51364639763, 52672919521,
  true⟩, ⟨160181445011, 172278822570, true⟩, ⟨36352418277, 37065055582, true⟩, ⟨48401429999,
  52574734639, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[137/160, 69/80]`. -/
@[expose] def Oc27_0 : FIv × FIv × FIv :=
  (⟨51158013288015, 139378425733777, true⟩, ⟨-3727524513159, 988276276918, true⟩, ⟨-219529801060,
  450710799022, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[137/160, 69/80]`. -/
@[expose] def Oc27_1 : FIv × FIv × FIv :=
  (⟨49439928192518, 135630513603534, true⟩, ⟨-3588274967198, 1038500290246, true⟩, ⟨-227197255381,
  436011465619, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[137/160, 69/80]`. -/
@[expose] def Oc27_2 : FIv × FIv × FIv :=
  (⟨45683062427925, 149413663220519, true⟩, ⟨-4169895562321, 1294424374941, true⟩, ⟨-288827623455,
  526897408847, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[137/160, 69/80]`. -/
@[expose] def Oc27_3 : FIv × FIv × FIv :=
  (⟨45683062427925, 149413663220519, true⟩, ⟨-4169895562321, 1294424374941, true⟩, ⟨-288827623455,
  526897408847, true⟩)

/-- One-dimensional piece of cell `[137/160, 69/80]`. -/
theorem c27_oneD : oneD 128 (Ecell (137/160) (69/80)) = Dc27 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[137/160, 69/80]`. -/
theorem c27_arc0 : outerArc (lamC 200) (Ecell (137/160) (69/80)) (Ecell (137/160) (69/80)).sq
    (dIof 200 Dc27.1 Dc27.2.2.2.2.1) 12 12 6 0 = Oc27_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[137/160, 69/80]`. -/
theorem c27_arc1 : outerArc (lamC 200) (Ecell (137/160) (69/80)) (Ecell (137/160) (69/80)).sq
    (dIof 200 Dc27.1 Dc27.2.2.2.2.1) 12 12 6 1 = Oc27_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[137/160, 69/80]`. -/
theorem c27_arc2 : outerArc (lamC 200) (Ecell (137/160) (69/80)) (Ecell (137/160) (69/80)).sq
    (dIof 200 Dc27.1 Dc27.2.2.2.2.1) 12 12 6 2 = Oc27_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[137/160, 69/80]`. -/
theorem c27_arc3 : outerArc (lamC 200) (Ecell (137/160) (69/80)) (Ecell (137/160) (69/80)).sq
    (dIof 200 Dc27.1 Dc27.2.2.2.2.1) 12 12 6 3 = Oc27_3 := by
  f2_arc_cert

/-- Final combination of cell `[137/160, 69/80]`. -/
theorem c27_final : cellCheckOf 200 128 12 12 6 (137/160) (69/80) Dc27
    (add3 (add3 Oc27_0 Oc27_1) (add3 Oc27_2 Oc27_3)) = true := by fiv_cert

/-- **Certificate for the cell `[137/160, 69/80]`.** -/
theorem cell27 : cellCheck 200 128 12 12 6 (137/160) (69/80) = true :=
  cellCheck_of_pieces c27_oneD c27_arc0 c27_arc1 c27_arc2 c27_arc3 c27_final

/-! ### Cell `[69/80, 139/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[69/80, 139/160]`. -/
@[expose] def Dc28 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4714448945, 4895201661, true⟩, ⟨7166109143, 8198191026, true⟩, ⟨52399919462, 53788015264,
  true⟩, ⟨171309276974, 184788367414, true⟩, ⟨36662729762, 37402533657, true⟩, ⟨50936384638,
  55463979390, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[69/80, 139/160]`. -/
@[expose] def Oc28_0 : FIv × FIv × FIv :=
  (⟨52067893119813, 147858080970259, true⟩, ⟨-4157020195070, 1094947916044, true⟩, ⟨-242367376703,
  500531198564, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[69/80, 139/160]`. -/
@[expose] def Oc28_1 : FIv × FIv × FIv :=
  (⟨50310211784075, 143936516740686, true⟩, ⟨-4003357822210, 1155587693905, true⟩, ⟨-251477774978,
  484455344471, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[69/80, 139/160]`. -/
@[expose] def Oc28_2 : FIv × FIv × FIv :=
  (⟨46271487712190, 159668752361427, true⟩, ⟨-4704170065032, 1441567714676, true⟩, ⟨-320603971202,
  590468486871, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[69/80, 139/160]`. -/
@[expose] def Oc28_3 : FIv × FIv × FIv :=
  (⟨46271487712190, 159668752361427, true⟩, ⟨-4704170065032, 1441567714676, true⟩, ⟨-320603971202,
  590468486871, true⟩)

/-- One-dimensional piece of cell `[69/80, 139/160]`. -/
theorem c28_oneD : oneD 128 (Ecell (69/80) (139/160)) = Dc28 := eq6_sound (by oned_cert)

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 0 of cell `[69/80, 139/160]`. -/
theorem c28_arc0 : outerArc (lamC 200) (Ecell (69/80) (139/160)) (Ecell (69/80) (139/160)).sq
    (dIof 200 Dc28.1 Dc28.2.2.2.2.1) 12 12 6 0 = Oc28_0 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 1 of cell `[69/80, 139/160]`. -/
theorem c28_arc1 : outerArc (lamC 200) (Ecell (69/80) (139/160)) (Ecell (69/80) (139/160)).sq
    (dIof 200 Dc28.1 Dc28.2.2.2.2.1) 12 12 6 1 = Oc28_1 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 2 of cell `[69/80, 139/160]`. -/
theorem c28_arc2 : outerArc (lamC 200) (Ecell (69/80) (139/160)) (Ecell (69/80) (139/160)).sq
    (dIof 200 Dc28.1 Dc28.2.2.2.2.1) 12 12 6 2 = Oc28_2 := by
  f2_arc_cert

set_option maxHeartbeats 10000000 in
-- the `eval_cert` builder evaluates ≈ 7·10⁴ interval operations in `meta` code
/-- Outer-arc piece 3 of cell `[69/80, 139/160]`. -/
theorem c28_arc3 : outerArc (lamC 200) (Ecell (69/80) (139/160)) (Ecell (69/80) (139/160)).sq
    (dIof 200 Dc28.1 Dc28.2.2.2.2.1) 12 12 6 3 = Oc28_3 := by
  f2_arc_cert

/-- Final combination of cell `[69/80, 139/160]`. -/
theorem c28_final : cellCheckOf 200 128 12 12 6 (69/80) (139/160) Dc28
    (add3 (add3 Oc28_0 Oc28_1) (add3 Oc28_2 Oc28_3)) = true := by fiv_cert

/-- **Certificate for the cell `[69/80, 139/160]`.** -/
theorem cell28 : cellCheck 200 128 12 12 6 (69/80) (139/160) = true :=
  cellCheck_of_pieces c28_oneD c28_arc0 c28_arc1 c28_arc2 c28_arc3 c28_final

end PlasmaLean.Design.LandremanFamily2Cert
