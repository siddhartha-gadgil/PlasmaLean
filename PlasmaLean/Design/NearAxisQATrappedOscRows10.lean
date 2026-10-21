/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells

/-!
# Kernel checks of the oscillatory-kick cover, part 10

Leaves 72–79 of the adaptive cover of the start window used by
`Design/NearAxisQATrappedOscCover` (amplitude target `Kn = 40`, period range
`[59, 72] μs`, precession range `ι₀ Δ ∈ [3086000000, 4502000000] · 2⁻³²`).
For each index box `[a, b] × [c, d]` (`ψ₀ ∈ PBI a b`, `B_t ∈ TBI c d`) the inner-leg check
`legAOk`, the outer-leg check `legBOk` (with the inner leg's `I(z₁)` enclosure) and the final
check `finalOk` are evaluated by `decide +kernel` on the oracle enclosures (all computed by the
untrusted exact mirror `scripts/trapped_reanchor/osc_mirror.py`; the kernel recomputes them).
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [80, 88]`. -/
theorem oscA_45_60_80_88 : legAOk (PBI 45 60) (TBI 80 88) ⟨5186305443, 5276638653, true⟩
    ⟨-12304256920, 13923716893, true⟩ ⟨-31794104321, -3616826748, true⟩
    ⟨1736486436, 2133951671, true⟩ ⟨121575912274, 139895175607, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [80, 88]`. -/
theorem oscB_45_60_80_88 : legBOk (PBI 45 60) (TBI 80 88) ⟨5186305443, 5276638653, true⟩
    ⟨1736486436, 2133951671, true⟩ ⟨-60135823566, 17057973953, true⟩
    ⟨-53094455771, 29522439439, true⟩ ⟨3390720745, 4102681930, true⟩
    ⟨139989591615, 157900853937, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [80, 88]`. -/
theorem oscF_45_60_80_88 : finalOk
    ⟨-12304256920, 13923716893, true⟩ ⟨-31794104321, -3616826748, true⟩
    ⟨-60135823566, 17057973953, true⟩ ⟨-53094455771, 29522439439, true⟩
    ⟨3390720745, 4102681930, true⟩ ⟨121575912274, 139895175607, true⟩
    ⟨139989591615, 157900853937, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [80, 88]` is a leaf of the cover. -/
theorem oscLeaf_45_60_80_88 : OscLeaf 40 59 72 3086000000 4502000000 45 60 80 88 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_80_88, oscB_45_60_80_88, oscF_45_60_80_88⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [88, 96]`. -/
theorem oscA_45_60_88_96 : legAOk (PBI 45 60) (TBI 88 96) ⟨5244228467, 5333194510, true⟩
    ⟨-13169682896, 12915263690, true⟩ ⟨-31071888087, -2372594573, true⟩
    ⟨1740375564, 2142488919, true⟩ ⟨122520583808, 140988515773, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [88, 96]`. -/
theorem oscB_45_60_88_96 : legBOk (PBI 45 60) (TBI 88 96) ⟨5244228467, 5333194510, true⟩
    ⟨1740375564, 2142488919, true⟩ ⟨-61066984668, 16185089575, true⟩
    ⟨-52401563861, 31392284939, true⟩ ⟨3389698039, 4103637149, true⟩
    ⟨140520132901, 158272515317, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [88, 96]`. -/
theorem oscF_45_60_88_96 : finalOk
    ⟨-13169682896, 12915263690, true⟩ ⟨-31071888087, -2372594573, true⟩
    ⟨-61066984668, 16185089575, true⟩ ⟨-52401563861, 31392284939, true⟩
    ⟨3389698039, 4103637149, true⟩ ⟨122520583808, 140988515773, true⟩
    ⟨140520132901, 158272515317, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [88, 96]` is a leaf of the cover. -/
theorem oscLeaf_45_60_88_96 : OscLeaf 40 59 72 3086000000 4502000000 45 60 88 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_88_96, oscB_45_60_88_96, oscF_45_60_88_96⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [96, 112]`. -/
theorem oscA_45_60_96_112 : legAOk (PBI 45 60) (TBI 96 112) ⟨5301693600, 5445056029, true⟩
    ⟨-16269400407, 14530787354, true⟩ ⟨-31691982623, 3293143878, true⟩
    ⟨1700645764, 2164058797, true⟩ ⟨121513423402, 142846799943, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [96, 112]`. -/
theorem oscB_45_60_96_112 : legBOk (PBI 45 60) (TBI 96 112) ⟨5301693600, 5445056029, true⟩
    ⟨1700645764, 2164058797, true⟩ ⟨-69703788711, 24699565081, true⟩
    ⟨-60579553889, 45153518079, true⟩ ⟨3301726896, 4164947786, true⟩
    ⟨138717546682, 162056924867, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [96, 112]`. -/
theorem oscF_45_60_96_112 : finalOk
    ⟨-16269400407, 14530787354, true⟩ ⟨-31691982623, 3293143878, true⟩
    ⟨-69703788711, 24699565081, true⟩ ⟨-60579553889, 45153518079, true⟩
    ⟨3301726896, 4164947786, true⟩ ⟨121513423402, 142846799943, true⟩
    ⟨138717546682, 162056924867, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [96, 112]` is a leaf of the cover. -/
theorem oscLeaf_45_60_96_112 : OscLeaf 40 59 72 3086000000 4502000000 45 60 96 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_96_112, oscB_45_60_96_112, oscF_45_60_96_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [112, 128]`. -/
theorem oscA_45_60_112_128 : legAOk (PBI 45 60) (TBI 112 128) ⟨5415322596, 5555357380, true⟩
    ⟨-18153541099, 15096181073, true⟩ ⟨-29966474532, 7329726108, true⟩
    ⟨1673507985, 2182621794, true⟩ ⟨121273139923, 145156808623, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [112, 128]`. -/
theorem oscB_45_60_112_128 : legBOk (PBI 45 60) (TBI 112 128) ⟨5415322596, 5555357380, true⟩
    ⟨1673507985, 2182621794, true⟩ ⟨-72773204288, 24726529461, true⟩
    ⟨-59216370372, 50319955820, true⟩ ⟨3240414557, 4141790034, true⟩
    ⟨137975370783, 160943054375, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [112, 128]`. -/
theorem oscF_45_60_112_128 : finalOk
    ⟨-18153541099, 15096181073, true⟩ ⟨-29966474532, 7329726108, true⟩
    ⟨-72773204288, 24726529461, true⟩ ⟨-59216370372, 50319955820, true⟩
    ⟨3240414557, 4141790034, true⟩ ⟨121273139923, 145156808623, true⟩
    ⟨137975370783, 160943054375, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [112, 128]` is a leaf of the cover. -/
theorem oscLeaf_45_60_112_128 : OscLeaf 40 59 72 3086000000 4502000000 45 60 112 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_112_128, oscB_45_60_112_128, oscF_45_60_112_128⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [0, 8]`. -/
theorem oscA_60_75_0_8 : legAOk (PBI 60 75) (TBI 0 8) ⟨4620995538, 4724656387, true⟩
    ⟨543747148, 31153547929, true⟩ ⟨-34163927665, -8745216027, true⟩
    ⟨1756547897, 2148467697, true⟩ ⟨118008048927, 136731430779, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [0, 8]`. -/
theorem oscB_60_75_0_8 : legBOk (PBI 60 75) (TBI 0 8) ⟨4620995538, 4724656387, true⟩
    ⟨1756547897, 2148467697, true⟩ ⟨-47173097864, 37074983974, true⟩
    ⟨-55804650025, 24987818451, true⟩ ⟨3510476781, 4242840419, true⟩
    ⟨139941252066, 159408476696, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [0, 8]`. -/
theorem oscF_60_75_0_8 : finalOk
    ⟨543747148, 31153547929, true⟩ ⟨-34163927665, -8745216027, true⟩
    ⟨-47173097864, 37074983974, true⟩ ⟨-55804650025, 24987818451, true⟩
    ⟨3510476781, 4242840419, true⟩ ⟨118008048927, 136731430779, true⟩
    ⟨139941252066, 159408476696, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [0, 8]` is a leaf of the cover. -/
theorem oscLeaf_60_75_0_8 : OscLeaf 40 59 72 3086000000 4502000000 60 75 0 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_0_8, oscB_60_75_0_8, oscF_60_75_0_8⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [8, 16]`. -/
theorem oscA_60_75_8_16 : legAOk (PBI 60 75) (TBI 8 16) ⟨4683555417, 4785451995, true⟩
    ⟨-1403814281, 29621079507, true⟩ ⟨-34962921288, -9257286213, true⟩
    ⟨1757917951, 2153068081, true⟩ ⟨118723728292, 137547788925, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [8, 16]`. -/
theorem oscB_60_75_8_16 : legBOk (PBI 60 75) (TBI 8 16) ⟨4683555417, 4785451995, true⟩
    ⟨1757917951, 2153068081, true⟩ ⟨-48899055025, 35753410716, true⟩
    ⟨-56338860816, 24584841822, true⟩ ⟨3503262967, 4234585910, true⟩
    ⟨140173540267, 159391258671, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [8, 16]`. -/
theorem oscF_60_75_8_16 : finalOk
    ⟨-1403814281, 29621079507, true⟩ ⟨-34962921288, -9257286213, true⟩
    ⟨-48899055025, 35753410716, true⟩ ⟨-56338860816, 24584841822, true⟩
    ⟨3503262967, 4234585910, true⟩ ⟨118723728292, 137547788925, true⟩
    ⟨140173540267, 159391258671, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [8, 16]` is a leaf of the cover. -/
theorem oscLeaf_60_75_8_16 : OscLeaf 40 59 72 3086000000 4502000000 60 75 8 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_8_16, oscB_60_75_8_16, oscF_60_75_8_16⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [16, 24]`. -/
theorem oscA_60_75_16_24 : legAOk (PBI 60 75) (TBI 16 24) ⟨4745444707, 4845635367, true⟩
    ⟨-3208926253, 27963662644, true⟩ ⟨-35695108367, -9621886348, true⟩
    ⟨1760324746, 2154929303, true⟩ ⟨119471319488, 138197536169, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [16, 24]`. -/
theorem oscB_60_75_16_24 : legBOk (PBI 60 75) (TBI 16 24) ⟨4745444707, 4845635367, true⟩
    ⟨1760324746, 2154929303, true⟩ ⟨-51137302027, 34819362613, true⟩
    ⟨-57726703625, 25272053604, true⟩ ⟨3471824294, 4225057532, true⟩
    ⟨138526246924, 159473613834, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [16, 24]`. -/
theorem oscF_60_75_16_24 : finalOk
    ⟨-3208926253, 27963662644, true⟩ ⟨-35695108367, -9621886348, true⟩
    ⟨-51137302027, 34819362613, true⟩ ⟨-57726703625, 25272053604, true⟩
    ⟨3471824294, 4225057532, true⟩ ⟨119471319488, 138197536169, true⟩
    ⟨138526246924, 159473613834, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [16, 24]` is a leaf of the cover. -/
theorem oscLeaf_60_75_16_24 : OscLeaf 40 59 72 3086000000 4502000000 60 75 16 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_16_24, oscB_60_75_16_24, oscF_60_75_16_24⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [24, 32]`. -/
theorem oscA_60_75_24_32 : legAOk (PBI 60 75) (TBI 24 32) ⟨4806692712, 4905232323, true⟩
    ⟨-4993117706, 26319860884, true⟩ ⟨-36381769084, -9714750836, true⟩
    ⟨1762892321, 2158285201, true⟩ ⟨120238667837, 138941625944, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [24, 32]`. -/
theorem oscB_60_75_24_32 : legBOk (PBI 60 75) (TBI 24 32) ⟨4806692712, 4905232323, true⟩
    ⟨1762892321, 2158285201, true⟩ ⟨-52897959656, 33394073573, true⟩
    ⟨-58156514371, 25616910941, true⟩ ⟨3466199684, 4219932629, true⟩
    ⟨138795784644, 159764934166, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [24, 32]`. -/
theorem oscF_60_75_24_32 : finalOk
    ⟨-4993117706, 26319860884, true⟩ ⟨-36381769084, -9714750836, true⟩
    ⟨-52897959656, 33394073573, true⟩ ⟨-58156514371, 25616910941, true⟩
    ⟨3466199684, 4219932629, true⟩ ⟨120238667837, 138941625944, true⟩
    ⟨138795784644, 159764934166, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [24, 32]` is a leaf of the cover. -/
theorem oscLeaf_60_75_24_32 : OscLeaf 40 59 72 3086000000 4502000000 60 75 24 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_24_32, oscB_60_75_24_32, oscF_60_75_24_32⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
