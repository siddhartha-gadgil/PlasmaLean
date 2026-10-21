/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells

/-!
# Kernel checks of the oscillatory-kick cover, part 11

Leaves 80–87 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[60, 75] × [32, 40]`. -/
theorem oscA_60_75_32_40 : legAOk (PBI 60 75) (TBI 32 40) ⟨4867327029, 4964267276, true⟩
    ⟨-5826342174, 22856262241, true⟩ ⟨-35091321453, -10341196228, true⟩
    ⟨1766743967, 2114650609, true⟩ ⟨121107806436, 136989232904, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [32, 40]`. -/
theorem oscB_60_75_32_40 : legBOk (PBI 60 75) (TBI 32 40) ⟨4867327029, 4964267276, true⟩
    ⟨1766743967, 2114650609, true⟩ ⟨-51996593327, 26044485282, true⟩
    ⟨-55147937138, 22062943561, true⟩ ⟨3464485716, 4134954473, true⟩
    ⟨139254732239, 157730515601, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [32, 40]`. -/
theorem oscF_60_75_32_40 : finalOk
    ⟨-5826342174, 22856262241, true⟩ ⟨-35091321453, -10341196228, true⟩
    ⟨-51996593327, 26044485282, true⟩ ⟨-55147937138, 22062943561, true⟩
    ⟨3464485716, 4134954473, true⟩ ⟨121107806436, 136989232904, true⟩
    ⟨139254732239, 157730515601, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [32, 40]` is a leaf of the cover. -/
theorem oscLeaf_60_75_32_40 : OscLeaf 40 59 72 3086000000 4502000000 60 75 32 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_32_40, oscB_60_75_32_40, oscF_60_75_32_40⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [40, 48]`. -/
theorem oscA_60_75_40_48 : legAOk (PBI 60 75) (TBI 40 48) ⟨4927373707, 5022763326, true⟩
    ⟨-8439444441, 21577700794, true⟩ ⟨-35588564530, -8561758721, true⟩
    ⟨1730514148, 2120626552, true⟩ ⟨119465963481, 137891015577, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [40, 48]`. -/
theorem oscB_60_75_40_48 : legBOk (PBI 60 75) (TBI 40 48) ⟨4927373707, 5022763326, true⟩
    ⟨1730514148, 2120626552, true⟩ ⟨-55613627100, 25897587461, true⟩
    ⟨-56395860460, 25164401678, true⟩ ⟨3420132068, 4130788816, true⟩
    ⟨139526454763, 157894148047, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [40, 48]`. -/
theorem oscF_60_75_40_48 : finalOk
    ⟨-8439444441, 21577700794, true⟩ ⟨-35588564530, -8561758721, true⟩
    ⟨-55613627100, 25897587461, true⟩ ⟨-56395860460, 25164401678, true⟩
    ⟨3420132068, 4130788816, true⟩ ⟨119465963481, 137891015577, true⟩
    ⟨139526454763, 157894148047, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_60_75_40_48 : OscLeaf 40 59 72 3086000000 4502000000 60 75 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_40_48, oscB_60_75_40_48, oscF_60_75_40_48⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [48, 56]`. -/
theorem oscA_60_75_48_56 : legAOk (PBI 60 75) (TBI 48 56) ⟨4986857367, 5080742385, true⟩
    ⟨-9565409286, 19896253732, true⟩ ⟨-35479875607, -7985958879, true⟩
    ⟨1735403198, 2124104429, true⟩ ⟨120400544619, 138686683356, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [48, 56]`. -/
theorem oscB_60_75_48_56 : legBOk (PBI 60 75) (TBI 48 56) ⟨4986857367, 5080742385, true⟩
    ⟨1735403198, 2124104429, true⟩ ⟨-56777910489, 24112944112, true⟩
    ⟨-55974445004, 26066670599, true⟩ ⟨3418714383, 4125541982, true⟩
    ⟨139930098073, 158158888884, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [48, 56]`. -/
theorem oscF_60_75_48_56 : finalOk
    ⟨-9565409286, 19896253732, true⟩ ⟨-35479875607, -7985958879, true⟩
    ⟨-56777910489, 24112944112, true⟩ ⟨-55974445004, 26066670599, true⟩
    ⟨3418714383, 4125541982, true⟩ ⟨120400544619, 138686683356, true⟩
    ⟨139930098073, 158158888884, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [48, 56]` is a leaf of the cover. -/
theorem oscLeaf_60_75_48_56 : OscLeaf 40 59 72 3086000000 4502000000 60 75 48 56 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_48_56, oscB_60_75_48_56, oscF_60_75_48_56⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [56, 64]`. -/
theorem oscA_60_75_56_64 : legAOk (PBI 60 75) (TBI 56 64) ⟨5045801319, 5138225250, true⟩
    ⟨-10724868825, 18397689670, true⟩ ⟨-35230521231, -7131955179, true⟩
    ⟨1738127194, 2130940144, true⟩ ⟨121221046246, 139656636053, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [56, 64]`. -/
theorem oscB_60_75_56_64 : legBOk (PBI 60 75) (TBI 56 64) ⟨5045801319, 5138225250, true⟩
    ⟨1738127194, 2130940144, true⟩ ⟨-57963487466, 22642966021, true⟩
    ⟨-55637307349, 27379488665, true⟩ ⟨3415931949, 4123876167, true⟩
    ⟨140389687819, 158439443865, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [56, 64]`. -/
theorem oscF_60_75_56_64 : finalOk
    ⟨-10724868825, 18397689670, true⟩ ⟨-35230521231, -7131955179, true⟩
    ⟨-57963487466, 22642966021, true⟩ ⟨-55637307349, 27379488665, true⟩
    ⟨3415931949, 4123876167, true⟩ ⟨121221046246, 139656636053, true⟩
    ⟨140389687819, 158439443865, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [56, 64]` is a leaf of the cover. -/
theorem oscLeaf_60_75_56_64 : OscLeaf 40 59 72 3086000000 4502000000 60 75 56 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_56_64, oscB_60_75_56_64, oscF_60_75_56_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [64, 72]`. -/
theorem oscA_60_75_64_72 : legAOk (PBI 60 75) (TBI 64 72) ⟨5104227664, 5195231697, true⟩
    ⟨-11694332845, 16827102999, true⟩ ⟨-34801486682, -6199090163, true⟩
    ⟨1742951836, 2136601341, true⟩ ⟨122169808691, 140567815622, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [64, 72]`. -/
theorem oscB_60_75_64_72 : legBOk (PBI 60 75) (TBI 64 72) ⟨5104227664, 5195231697, true⟩
    ⟨1742951836, 2136601341, true⟩ ⟨-59375547237, 19241289495, true⟩
    ⟨-54763212732, 27520574962, true⟩ ⟨3388496112, 4093418097, true⟩
    ⟨138870873145, 156768356721, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [64, 72]`. -/
theorem oscF_60_75_64_72 : finalOk
    ⟨-11694332845, 16827102999, true⟩ ⟨-34801486682, -6199090163, true⟩
    ⟨-59375547237, 19241289495, true⟩ ⟨-54763212732, 27520574962, true⟩
    ⟨3388496112, 4093418097, true⟩ ⟨122169808691, 140567815622, true⟩
    ⟨138870873145, 156768356721, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [64, 72]` is a leaf of the cover. -/
theorem oscLeaf_60_75_64_72 : OscLeaf 40 59 72 3086000000 4502000000 60 75 64 72 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_64_72, oscB_60_75_64_72, oscF_60_75_64_72⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [72, 80]`. -/
theorem oscA_60_75_72_80 : legAOk (PBI 60 75) (TBI 72 80) ⟨5162157387, 5251780559, true⟩
    ⟨-11707363302, 13736683131, true⟩ ⟨-32117456777, -5573759006, true⟩
    ⟨1747680428, 2094606225, true⟩ ⟨123118626268, 138766526736, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [72, 80]`. -/
theorem oscB_60_75_72_80 : legBOk (PBI 60 75) (TBI 72 80) ⟨5162157387, 5251780559, true⟩
    ⟨1747680428, 2094606225, true⟩ ⟨-58748744259, 15116247946, true⟩
    ⟨-51335851644, 27338398771, true⟩ ⟨3388166561, 4042763033, true⟩
    ⟨139365910114, 157039213119, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [72, 80]`. -/
theorem oscF_60_75_72_80 : finalOk
    ⟨-11707363302, 13736683131, true⟩ ⟨-32117456777, -5573759006, true⟩
    ⟨-58748744259, 15116247946, true⟩ ⟨-51335851644, 27338398771, true⟩
    ⟨3388166561, 4042763033, true⟩ ⟨123118626268, 138766526736, true⟩
    ⟨139365910114, 157039213119, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [72, 80]` is a leaf of the cover. -/
theorem oscLeaf_60_75_72_80 : OscLeaf 40 59 72 3086000000 4502000000 60 75 72 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_72_80, oscB_60_75_72_80, oscF_60_75_72_80⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [80, 88]`. -/
theorem oscA_60_75_80_88 : legAOk (PBI 60 75) (TBI 80 88) ⟨5219610447, 5307889785, true⟩
    ⟨-13124464162, 13106224402, true⟩ ⟨-31607134227, -2801471763, true⟩
    ⟨1713258768, 2102757447, true⟩ ⟨121662745373, 139842571836, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [80, 88]`. -/
theorem oscB_60_75_80_88 : legBOk (PBI 60 75) (TBI 80 88) ⟨5219610447, 5307889785, true⟩
    ⟨1713258768, 2102757447, true⟩ ⟨-61278444681, 15454936245, true⟩
    ⟨-52075216566, 31574112171, true⟩ ⟨3349279113, 4043890463, true⟩
    ⟨139906083903, 157424524441, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [80, 88]`. -/
theorem oscF_60_75_80_88 : finalOk
    ⟨-13124464162, 13106224402, true⟩ ⟨-31607134227, -2801471763, true⟩
    ⟨-61278444681, 15454936245, true⟩ ⟨-52075216566, 31574112171, true⟩
    ⟨3349279113, 4043890463, true⟩ ⟨121662745373, 139842571836, true⟩
    ⟨139906083903, 157424524441, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [80, 88]` is a leaf of the cover. -/
theorem oscLeaf_60_75_80_88 : OscLeaf 40 59 72 3086000000 4502000000 60 75 80 88 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_80_88, oscB_60_75_80_88, oscF_60_75_80_88⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [88, 96]`. -/
theorem oscA_60_75_88_96 : legAOk (PBI 60 75) (TBI 88 96) ⟨5276605847, 5363576516, true⟩
    ⟨-13917449872, 12291682679, true⟩ ⟨-30729715342, -1620360936, true⟩
    ⟨1719425909, 2109460750, true⟩ ⟨122718163064, 140852903590, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [88, 96]`. -/
theorem oscB_60_75_88_96 : legBOk (PBI 60 75) (TBI 88 96) ⟨5276605847, 5363576516, true⟩
    ⟨1719425909, 2109460750, true⟩ ⟨-62038315253, 14843559012, true⟩
    ⟨-51295818707, 33408363360, true⟩ ⟨3349974338, 4044824286, true⟩
    ⟨140381200118, 157891562305, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [88, 96]`. -/
theorem oscF_60_75_88_96 : finalOk
    ⟨-13917449872, 12291682679, true⟩ ⟨-30729715342, -1620360936, true⟩
    ⟨-62038315253, 14843559012, true⟩ ⟨-51295818707, 33408363360, true⟩
    ⟨3349974338, 4044824286, true⟩ ⟨122718163064, 140852903590, true⟩
    ⟨140381200118, 157891562305, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[60, 75] × [88, 96]` is a leaf of the cover. -/
theorem oscLeaf_60_75_88_96 : OscLeaf 40 59 72 3086000000 4502000000 60 75 88 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_88_96, oscB_60_75_88_96, oscF_60_75_88_96⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
