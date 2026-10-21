/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Quad

/-!
# Mercier certificate for Landreman's family 2, `λ = 200`: cell group 7

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

/-! ### Cell `[141/160, 71/80]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[141/160, 71/80]`. -/
@[expose] def Dc31 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4859150072, 5064560722, true⟩, ⟨8461062997, 9812466133, true⟩, ⟨55983838086, 57674373755,
  true⟩, ⟨213481694787, 232750627293, true⟩, ⟨37700054467, 38536992865, true⟩, ⟨60168996772,
  66102189121, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[141/160, 71/80]`. -/
@[expose] def Oc31_0 : FIv × FIv × FIv :=
  (⟨55320486624946, 185420376444807, true⟩, ⟨-6250576656656, 1611447202880, true⟩, ⟨-348488530466,
  739751926498, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[141/160, 71/80]`. -/
@[expose] def Oc31_1 : FIv × FIv × FIv :=
  (⟨53421087348743, 180826634428011, true⟩, ⟨-6030597429124, 1726155490098, true⟩, ⟨-365475210894,
  718098223834, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[141/160, 71/80]`. -/
@[expose] def Oc31_2 : FIv × FIv × FIv :=
  (⟨48308267139872, 207616624004174, true⟩, ⟨-7487319588336, 2201662630131, true⟩, ⟨-471129591937,
  910215765039, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[141/160, 71/80]`. -/
@[expose] def Oc31_3 : FIv × FIv × FIv :=
  (⟨48308267139872, 207616624004174, true⟩, ⟨-7487319588336, 2201662630131, true⟩, ⟨-471129591937,
  910215765039, true⟩)

/-- One-dimensional piece of cell `[141/160, 71/80]`. -/
theorem c31_oneD : oneD 128 (Ecell (141/160) (71/80)) = Dc31 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[141/160, 71/80]`. -/
theorem c31_arc0 : outerArc (lamC 200) (Ecell (141/160) (71/80)) (Ecell (141/160) (71/80)).sq
    (dIof 200 Dc31.1 Dc31.2.2.2.2.1) 12 12 6 0 = Oc31_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[141/160, 71/80]`. -/
theorem c31_arc1 : outerArc (lamC 200) (Ecell (141/160) (71/80)) (Ecell (141/160) (71/80)).sq
    (dIof 200 Dc31.1 Dc31.2.2.2.2.1) 12 12 6 1 = Oc31_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[141/160, 71/80]`. -/
theorem c31_arc2 : outerArc (lamC 200) (Ecell (141/160) (71/80)) (Ecell (141/160) (71/80)).sq
    (dIof 200 Dc31.1 Dc31.2.2.2.2.1) 12 12 6 2 = Oc31_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[141/160, 71/80]`. -/
theorem c31_arc3 : outerArc (lamC 200) (Ecell (141/160) (71/80)) (Ecell (141/160) (71/80)).sq
    (dIof 200 Dc31.1 Dc31.2.2.2.2.1) 12 12 6 3 = Oc31_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[141/160, 71/80]`. -/
theorem c31_final : cellCheckOf 200 128 12 12 6 (141/160) (71/80) Dc31
    (add3 (add3 Oc31_0 Oc31_1) (add3 Oc31_2 Oc31_3)) = true := by decide +kernel

/-- **Certificate for the cell `[141/160, 71/80]`.** -/
theorem cell31 : cellCheck 200 128 12 12 6 (141/160) (71/80) = true :=
  cellCheck_of_pieces c31_oneD c31_arc0 c31_arc1 c31_arc2 c31_arc3 c31_final

/-! ### Cell `[71/80, 143/160]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[71/80, 143/160]`. -/
@[expose] def Dc32 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4913171723, 5128470008, true⟩, ⟨8989199370, 10482282905, true⟩, ⟨57372898003, 59192098860,
  true⟩, ⟨231409687751, 253398390052, true⟩, ⟨38087682801, 38963610007, true⟩, ⟨63940965494,
  70500717568, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[71/80, 143/160]`. -/
@[expose] def Oc32_0 : FIv × FIv × FIv :=
  (⟨56608094041518, 204438992962339, true⟩, ⟨-7405227216194, 1889257457530, true⟩, ⟨-403242029562,
  868696175940, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[71/80, 143/160]`. -/
@[expose] def Oc32_1 : FIv × FIv × FIv :=
  (⟨54652424846018, 199552912260469, true⟩, ⟨-7149898009282, 2035557108018, true⟩, ⟨-425003199573,
  844236827044, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[71/80, 143/160]`. -/
@[expose] def Oc32_2 : FIv × FIv × FIv :=
  (⟨49081945890339, 234817684428507, true⟩, ⟨-9255584025842, 2664778962341, true⟩, ⟨-557856517339,
  1106694813324, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[71/80, 143/160]`. -/
@[expose] def Oc32_3 : FIv × FIv × FIv :=
  (⟨49081945890339, 234817684428507, true⟩, ⟨-9255584025842, 2664778962341, true⟩, ⟨-557856517339,
  1106694813324, true⟩)

/-- One-dimensional piece of cell `[71/80, 143/160]`. -/
theorem c32_oneD : oneD 128 (Ecell (71/80) (143/160)) = Dc32 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[71/80, 143/160]`. -/
theorem c32_arc0 : outerArc (lamC 200) (Ecell (71/80) (143/160)) (Ecell (71/80) (143/160)).sq
    (dIof 200 Dc32.1 Dc32.2.2.2.2.1) 12 12 6 0 = Oc32_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[71/80, 143/160]`. -/
theorem c32_arc1 : outerArc (lamC 200) (Ecell (71/80) (143/160)) (Ecell (71/80) (143/160)).sq
    (dIof 200 Dc32.1 Dc32.2.2.2.2.1) 12 12 6 1 = Oc32_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[71/80, 143/160]`. -/
theorem c32_arc2 : outerArc (lamC 200) (Ecell (71/80) (143/160)) (Ecell (71/80) (143/160)).sq
    (dIof 200 Dc32.1 Dc32.2.2.2.2.1) 12 12 6 2 = Oc32_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[71/80, 143/160]`. -/
theorem c32_arc3 : outerArc (lamC 200) (Ecell (71/80) (143/160)) (Ecell (71/80) (143/160)).sq
    (dIof 200 Dc32.1 Dc32.2.2.2.2.1) 12 12 6 3 = Oc32_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[71/80, 143/160]`. -/
theorem c32_final : cellCheckOf 200 128 12 12 6 (71/80) (143/160) Dc32
    (add3 (add3 Oc32_0 Oc32_1) (add3 Oc32_2 Oc32_3)) = true := by decide +kernel

/-- **Certificate for the cell `[71/80, 143/160]`.** -/
theorem cell32 : cellCheck 200 128 12 12 6 (71/80) (143/160) = true :=
  cellCheck_of_pieces c32_oneD c32_arc0 c32_arc1 c32_arc2 c32_arc3 c32_final

/-! ### Cell `[143/160, 9/10]`, grids `(12, 12, 6)` -/

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` on the cell `[143/160, 9/10]`. -/
@[expose] def Dc33 : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨4970633050, 5196889282, true⟩, ⟨9579692154, 11239077924, true⟩, ⟨58881846625, 60848440939,
  true⟩, ⟨251927604216, 277213481600, true⟩, ⟨38500252890, 39419418944, true⟩, ⟨68162943862,
  75460251658, true⟩)

/-- Outer arc 0 surface-integral enclosures on the cell `[143/160, 9/10]`. -/
@[expose] def Oc33_0 : FIv × FIv × FIv :=
  (⟨58012472059239, 229645186791938, true⟩, ⟨-9030136270724, 2278595097950, true⟩, ⟨-477433808228,
  1048223983268, true⟩)

/-- Outer arc 1 surface-integral enclosures on the cell `[143/160, 9/10]`. -/
@[expose] def Oc33_1 : FIv × FIv × FIv :=
  (⟨55995185417577, 224419808849142, true⟩, ⟨-8727083060990, 2470878750384, true⟩, ⟨-506271225490,
  1020344788650, true⟩)

/-- Outer arc 2 surface-integral enclosures on the cell `[143/160, 9/10]`. -/
@[expose] def Oc33_2 : FIv × FIv × FIv :=
  (⟨49900828302970, 274436390002777, true⟩, ⟨-12020756618525, 3369764682808, true⟩, ⟨-685839598759,
  1408527254063, true⟩)

/-- Outer arc 3 surface-integral enclosures on the cell `[143/160, 9/10]`. -/
@[expose] def Oc33_3 : FIv × FIv × FIv :=
  (⟨49900828302970, 274436390002777, true⟩, ⟨-12020756618525, 3369764682808, true⟩, ⟨-685839598759,
  1408527254063, true⟩)

/-- One-dimensional piece of cell `[143/160, 9/10]`. -/
theorem c33_oneD : oneD 128 (Ecell (143/160) (9/10)) = Dc33 := eq6_sound (by decide +kernel)

/-- Outer-arc piece 0 of cell `[143/160, 9/10]`. -/
theorem c33_arc0 : outerArc (lamC 200) (Ecell (143/160) (9/10)) (Ecell (143/160) (9/10)).sq
    (dIof 200 Dc33.1 Dc33.2.2.2.2.1) 12 12 6 0 = Oc33_0 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 1 of cell `[143/160, 9/10]`. -/
theorem c33_arc1 : outerArc (lamC 200) (Ecell (143/160) (9/10)) (Ecell (143/160) (9/10)).sq
    (dIof 200 Dc33.1 Dc33.2.2.2.2.1) 12 12 6 1 = Oc33_1 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 2 of cell `[143/160, 9/10]`. -/
theorem c33_arc2 : outerArc (lamC 200) (Ecell (143/160) (9/10)) (Ecell (143/160) (9/10)).sq
    (dIof 200 Dc33.1 Dc33.2.2.2.2.1) 12 12 6 2 = Oc33_2 := eq3_sound (by decide +kernel)

/-- Outer-arc piece 3 of cell `[143/160, 9/10]`. -/
theorem c33_arc3 : outerArc (lamC 200) (Ecell (143/160) (9/10)) (Ecell (143/160) (9/10)).sq
    (dIof 200 Dc33.1 Dc33.2.2.2.2.1) 12 12 6 3 = Oc33_3 := eq3_sound (by decide +kernel)

/-- Final combination of cell `[143/160, 9/10]`. -/
theorem c33_final : cellCheckOf 200 128 12 12 6 (143/160) (9/10) Dc33
    (add3 (add3 Oc33_0 Oc33_1) (add3 Oc33_2 Oc33_3)) = true := by decide +kernel

/-- **Certificate for the cell `[143/160, 9/10]`.** -/
theorem cell33 : cellCheck 200 128 12 12 6 (143/160) (9/10) = true :=
  cellCheck_of_pieces c33_oneD c33_arc0 c33_arc1 c33_arc2 c33_arc3 c33_final

end PlasmaLean.Design.LandremanFamily2Cert
