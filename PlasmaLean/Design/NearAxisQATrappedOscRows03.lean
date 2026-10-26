/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 3

Leaves 16–23 of the adaptive cover of the start window used by
`Design/NearAxisQATrappedOscCover` (amplitude target `Kn = 40`, period range
`[59, 72] μs`, precession range `ι₀ Δ ∈ [3086000000, 4502000000] · 2⁻³²`).
For each index box `[a, b] × [c, d]` (`ψ₀ ∈ PBI a b`, `B_t ∈ TBI c d`) the inner-leg check
`legAOk`, the outer-leg check `legBOk` (with the inner leg's `I(z₁)` enclosure) and the final
check `finalOk` are checked on the oracle enclosures (all computed by the untrusted exact
mirror `scripts/trapped_reanchor/osc_mirror.py`), all three by evaluation certificates
(`fiv_cert`, `Certificates/EvalCert`: one kernel leaf per interval operation; the leg checks are
≈ 4·10⁴ leaves each, so the private `.olean` of this module is ≈ 300 MB).
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [72, 80]`. -/
theorem oscA_0_15_72_80 : legAOk (PBI 0 15) (TBI 72 80) ⟨5017000801, 5115894705, true⟩
    ⟨-9058359150, 20285803468, true⟩ ⟨-33566562673, -6781381639, true⟩
    ⟨1850051273, 2294153378, true⟩ ⟨122847184068, 142457839424, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [72, 80]`. -/
theorem oscB_0_15_72_80 : legBOk (PBI 0 15) (TBI 72 80) ⟨5017000801, 5115894705, true⟩
    ⟨1850051273, 2294153378, true⟩ ⟨-54795447072, 28835921935, true⟩
    ⟨-57430886303, 23470126728, true⟩ ⟨3606156410, 4395056137, true⟩
    ⟨142294011812, 161271507820, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [72, 80]`. -/
theorem oscF_0_15_72_80 : finalOk
    ⟨-9058359150, 20285803468, true⟩ ⟨-33566562673, -6781381639, true⟩
    ⟨-54795447072, 28835921935, true⟩ ⟨-57430886303, 23470126728, true⟩
    ⟨3606156410, 4395056137, true⟩ ⟨122847184068, 142457839424, true⟩
    ⟨142294011812, 161271507820, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [72, 80]` is a leaf of the cover. -/
theorem oscLeaf_0_15_72_80 : OscLeaf 40 59 72 3086000000 4502000000 0 15 72 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_72_80, oscB_0_15_72_80, oscF_0_15_72_80⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [80, 88]`. -/
theorem oscA_0_15_80_88 : legAOk (PBI 0 15) (TBI 80 88) ⟨5078536527, 5175811175, true⟩
    ⟨-9227697362, 17049708370, true⟩ ⟨-31618371217, -6805165733, true⟩
    ⟨1854804248, 2245888213, true⟩ ⟨123821009022, 140470742139, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [80, 88]`. -/
theorem oscB_0_15_80_88 : legBOk (PBI 0 15) (TBI 80 88) ⟨5078536527, 5175811175, true⟩
    ⟨1854804248, 2245888213, true⟩ ⟨-54124296547, 24207702070, true⟩
    ⟨-54752570543, 22863860415, true⟩ ⟨3603919048, 4337201562, true⟩
    ⟨142750703001, 161590484605, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [80, 88]`. -/
theorem oscF_0_15_80_88 : finalOk
    ⟨-9227697362, 17049708370, true⟩ ⟨-31618371217, -6805165733, true⟩
    ⟨-54124296547, 24207702070, true⟩ ⟨-54752570543, 22863860415, true⟩
    ⟨3603919048, 4337201562, true⟩ ⟨123821009022, 140470742139, true⟩
    ⟨142750703001, 161590484605, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [80, 88]` is a leaf of the cover. -/
theorem oscLeaf_0_15_80_88 : OscLeaf 40 59 72 3086000000 4502000000 0 15 80 88 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_80_88, oscB_0_15_80_88, oscF_0_15_80_88⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [88, 96]`. -/
theorem oscA_0_15_88_96 : legAOk (PBI 0 15) (TBI 88 96) ⟨5139526794, 5235228550, true⟩
    ⟨-10852216475, 16047830895, true⟩ ⟨-31580159340, -4490669102, true⟩
    ⟨1816033160, 2254831965, true⟩ ⟨122242406922, 141591490276, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [88, 96]`. -/
theorem oscB_0_15_88_96 : legBOk (PBI 0 15) (TBI 88 96) ⟨5139526794, 5235228550, true⟩
    ⟨1816033160, 2254831965, true⟩ ⟨-57056679458, 24289010348, true⟩
    ⟨-55749754536, 26796586406, true⟩ ⟨3557804369, 4337162232, true⟩
    ⟨143188335530, 161949187020, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [88, 96]`. -/
theorem oscF_0_15_88_96 : finalOk
    ⟨-10852216475, 16047830895, true⟩ ⟨-31580159340, -4490669102, true⟩
    ⟨-57056679458, 24289010348, true⟩ ⟨-55749754536, 26796586406, true⟩
    ⟨3557804369, 4337162232, true⟩ ⟨122242406922, 141591490276, true⟩
    ⟨143188335530, 161949187020, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [88, 96]` is a leaf of the cover. -/
theorem oscLeaf_0_15_88_96 : OscLeaf 40 59 72 3086000000 4502000000 0 15 88 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_88_96, oscB_0_15_88_96, oscF_0_15_88_96⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [96, 104]`. -/
theorem oscA_0_15_96_104 : legAOk (PBI 0 15) (TBI 96 104) ⟨5199994729, 5294167452, true⟩
    ⟨-11672727937, 14650919076, true⟩ ⟨-31061073253, -3524211734, true⟩
    ⟨1820975856, 2261112251, true⟩ ⟨123243484075, 142573959695, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [96, 104]`. -/
theorem oscB_0_15_96_104 : legBOk (PBI 0 15) (TBI 96 104) ⟨5199994729, 5294167452, true⟩
    ⟨1820975856, 2261112251, true⟩ ⟨-58872674087, 23610874323, true⟩
    ⟨-55818101181, 29248661671, true⟩ ⟨3528322301, 4335988303, true⟩
    ⟨141668942415, 162412982199, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [96, 104]`. -/
theorem oscF_0_15_96_104 : finalOk
    ⟨-11672727937, 14650919076, true⟩ ⟨-31061073253, -3524211734, true⟩
    ⟨-58872674087, 23610874323, true⟩ ⟨-55818101181, 29248661671, true⟩
    ⟨3528322301, 4335988303, true⟩ ⟨123243484075, 142573959695, true⟩
    ⟨141668942415, 162412982199, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [96, 104]` is a leaf of the cover. -/
theorem oscLeaf_0_15_96_104 : OscLeaf 40 59 72 3086000000 4502000000 0 15 96 104 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_96_104, oscB_0_15_96_104, oscF_0_15_96_104⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [104, 112]`. -/
theorem oscA_0_15_104_112 : legAOk (PBI 0 15) (TBI 104 112) ⟨5259962312, 5352647527, true⟩
    ⟨-12506822736, 13424501348, true⟩ ⟨-30370545357, -2464290951, true⟩
    ⟨1827488737, 2269557565, true⟩ ⟨124361369501, 143718917262, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [104, 112]`. -/
theorem oscB_0_15_104_112 : legBOk (PBI 0 15) (TBI 104 112) ⟨5259962312, 5352647527, true⟩
    ⟨1827488737, 2269557565, true⟩ ⟨-59069512909, 19637329123, true⟩
    ⟨-53952412664, 28677317422, true⟩ ⟨3528912292, 4302383018, true⟩
    ⟨142203609246, 160516422832, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [104, 112]`. -/
theorem oscF_0_15_104_112 : finalOk
    ⟨-12506822736, 13424501348, true⟩ ⟨-30370545357, -2464290951, true⟩
    ⟨-59069512909, 19637329123, true⟩ ⟨-53952412664, 28677317422, true⟩
    ⟨3528912292, 4302383018, true⟩ ⟨124361369501, 143718917262, true⟩
    ⟨142203609246, 160516422832, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [104, 112]` is a leaf of the cover. -/
theorem oscLeaf_0_15_104_112 : OscLeaf 40 59 72 3086000000 4502000000 0 15 104 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_104_112, oscB_0_15_104_112, oscF_0_15_104_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [112, 120]`. -/
theorem oscA_0_15_112_120 : legAOk (PBI 0 15) (TBI 112 120) ⟨5319450438, 5410687519, true⟩
    ⟨-12361646756, 11090856555, true⟩ ⟨-27555450566, -1615540408, true⟩
    ⟨1832461570, 2223011308, true⟩ ⟨125396952236, 141865410289, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [112, 120]`. -/
theorem oscB_0_15_112_120 : legBOk (PBI 0 15) (TBI 112 120) ⟨5319450438, 5410687519, true⟩
    ⟨1832461570, 2223011308, true⟩ ⟨-58410576832, 16206018087, true⟩
    ⟨-50528724996, 28854931962, true⟩ ⟨3527462673, 4248963463, true⟩
    ⟨142712679302, 161018289960, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [112, 120]`. -/
theorem oscF_0_15_112_120 : finalOk
    ⟨-12361646756, 11090856555, true⟩ ⟨-27555450566, -1615540408, true⟩
    ⟨-58410576832, 16206018087, true⟩ ⟨-50528724996, 28854931962, true⟩
    ⟨3527462673, 4248963463, true⟩ ⟨125396952236, 141865410289, true⟩
    ⟨142712679302, 161018289960, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [112, 120]` is a leaf of the cover. -/
theorem oscLeaf_0_15_112_120 : OscLeaf 40 59 72 3086000000 4502000000 0 15 112 120 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_112_120, oscB_0_15_112_120, oscF_0_15_112_120⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [120, 128]`. -/
theorem oscA_0_15_120_128 : legAOk (PBI 0 15) (TBI 120 128) ⟨5378479021, 5468305325, true⟩
    ⟨-13512486897, 11251285233, true⟩ ⟨-26932018597, 1079762141, true⟩
    ⟨1795460633, 2232241068, true⟩ ⟨123951915483, 143034193737, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [120, 128]`. -/
theorem oscB_0_15_120_128 : legBOk (PBI 0 15) (TBI 120 128) ⟨5378479021, 5468305325, true⟩
    ⟨1795460633, 2232241068, true⟩ ⟨-60807214768, 17365300484, true⟩
    ⟨-51164356496, 33292705790, true⟩ ⟨3485461961, 4249770611, true⟩
    ⟨143314935921, 161417023412, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [120, 128]`. -/
theorem oscF_0_15_120_128 : finalOk
    ⟨-13512486897, 11251285233, true⟩ ⟨-26932018597, 1079762141, true⟩
    ⟨-60807214768, 17365300484, true⟩ ⟨-51164356496, 33292705790, true⟩
    ⟨3485461961, 4249770611, true⟩ ⟨123951915483, 143034193737, true⟩
    ⟨143314935921, 161417023412, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [120, 128]` is a leaf of the cover. -/
theorem oscLeaf_0_15_120_128 : OscLeaf 40 59 72 3086000000 4502000000 0 15 120 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_120_128, oscB_0_15_120_128, oscF_0_15_120_128⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [0, 4]`. -/
theorem oscA_15_30_0_4 : legAOk (PBI 15 30) (TBI 0 4) ⟨4483819864, 4564071793, true⟩
    ⟨7087317492, 32721632861, true⟩ ⟨-28986318561, -4665449467, true⟩
    ⟨1866935317, 2261498545, true⟩ ⟨119440241756, 137466570046, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [0, 4]`. -/
theorem oscB_15_30_0_4 : legBOk (PBI 15 30) (TBI 0 4) ⟨4483819864, 4564071793, true⟩
    ⟨1866935317, 2261498545, true⟩ ⟨-37769035214, 38454501509, true⟩
    ⟨-50483744826, 23465653576, true⟩ ⟨3733338852, 4462488160, true⟩
    ⟨142845762970, 161251479421, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [0, 4]`. -/
theorem oscF_15_30_0_4 : finalOk
    ⟨7087317492, 32721632861, true⟩ ⟨-28986318561, -4665449467, true⟩
    ⟨-37769035214, 38454501509, true⟩ ⟨-50483744826, 23465653576, true⟩
    ⟨3733338852, 4462488160, true⟩ ⟨119440241756, 137466570046, true⟩
    ⟨142845762970, 161251479421, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [0, 4]` is a leaf of the cover. -/
theorem oscLeaf_15_30_0_4 : OscLeaf 40 59 72 3086000000 4502000000 15 30 0 4 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_0_4, oscB_15_30_0_4, oscF_15_30_0_4⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
