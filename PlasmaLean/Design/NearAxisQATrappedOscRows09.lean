/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells

/-!
# Kernel checks of the oscillatory-kick cover, part 9

Leaves 64–71 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[45, 60] × [16, 24]`. -/
theorem oscA_45_60_16_24 : legAOk (PBI 45 60) (TBI 16 24) ⟨4703910591, 4806725524, true⟩
    ⟨-1693428291, 29072297232, true⟩ ⟨-34447126769, -8929663161, true⟩
    ⟨1785860551, 2190967910, true⟩ ⟨119449648874, 138435930283, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [16, 24]`. -/
theorem oscB_45_60_16_24 : legBOk (PBI 45 60) (TBI 16 24) ⟨4703910591, 4806725524, true⟩
    ⟨1785860551, 2190967910, true⟩ ⟨-48853918775, 36135934846, true⟩
    ⟨-56540976609, 23906376275, true⟩ ⟨3547805101, 4294995978, true⟩
    ⟨140779212968, 160142171611, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [16, 24]`. -/
theorem oscF_45_60_16_24 : finalOk
    ⟨-1693428291, 29072297232, true⟩ ⟨-34447126769, -8929663161, true⟩
    ⟨-48853918775, 36135934846, true⟩ ⟨-56540976609, 23906376275, true⟩
    ⟨3547805101, 4294995978, true⟩ ⟨119449648874, 138435930283, true⟩
    ⟨140779212968, 160142171611, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [16, 24]` is a leaf of the cover. -/
theorem oscLeaf_45_60_16_24 : OscLeaf 40 59 72 3086000000 4502000000 45 60 16 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_16_24, oscB_45_60_16_24, oscF_45_60_16_24⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [24, 32]`. -/
theorem oscA_45_60_24_32 : legAOk (PBI 45 60) (TBI 24 32) ⟨4766279372, 4867359840, true⟩
    ⟨-3560013622, 27527924296, true⟩ ⟨-35209255408, -9187733897, true⟩
    ⟨1787280764, 2195012090, true⟩ ⟨120158719537, 139215610852, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [24, 32]`. -/
theorem oscB_45_60_24_32 : legBOk (PBI 45 60) (TBI 24 32) ⟨4766279372, 4867359840, true⟩
    ⟨1787280764, 2195012090, true⟩ ⟨-51212742696, 35372306036, true⟩
    ⟨-58012644595, 24738810854, true⟩ ⟨3514466416, 4286956758, true⟩
    ⟨139104427222, 160204215954, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [24, 32]`. -/
theorem oscF_45_60_24_32 : finalOk
    ⟨-3560013622, 27527924296, true⟩ ⟨-35209255408, -9187733897, true⟩
    ⟨-51212742696, 35372306036, true⟩ ⟨-58012644595, 24738810854, true⟩
    ⟨3514466416, 4286956758, true⟩ ⟨120158719537, 139215610852, true⟩
    ⟨139104427222, 160204215954, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [24, 32]` is a leaf of the cover. -/
theorem oscLeaf_45_60_24_32 : OscLeaf 40 59 72 3086000000 4502000000 45 60 24 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_24_32, oscB_45_60_24_32, oscF_45_60_24_32⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [32, 40]`. -/
theorem oscA_45_60_32_40 : legAOk (PBI 45 60) (TBI 32 40) ⟨4828004824, 4927406518, true⟩
    ⟨-5293899830, 25885384057, true⟩ ⟨-35827901100, -9262821698, true⟩
    ⟨1791532597, 2198479875, true⟩ ⟨121042292903, 139999367844, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [32, 40]`. -/
theorem oscB_45_60_32_40 : legBOk (PBI 45 60) (TBI 32 40) ⟨4828004824, 4927406518, true⟩
    ⟨1791532597, 2198479875, true⟩ ⟨-52852857976, 33886933699, true⟩
    ⟨-58370273782, 25055723019, true⟩ ⟨3510302924, 4281725290, true⟩
    ⟨139382780540, 160505710080, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [32, 40]`. -/
theorem oscF_45_60_32_40 : finalOk
    ⟨-5293899830, 25885384057, true⟩ ⟨-35827901100, -9262821698, true⟩
    ⟨-52852857976, 33886933699, true⟩ ⟨-58370273782, 25055723019, true⟩
    ⟨3510302924, 4281725290, true⟩ ⟨121042292903, 139999367844, true⟩
    ⟨139382780540, 160505710080, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [32, 40]` is a leaf of the cover. -/
theorem oscLeaf_45_60_32_40 : OscLeaf 40 59 72 3086000000 4502000000 45 60 32 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_32_40, oscB_45_60_32_40, oscF_45_60_32_40⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [40, 48]`. -/
theorem oscA_45_60_40_48 : legAOk (PBI 45 60) (TBI 40 48) ⟨4889114818, 4986890177, true⟩
    ⟨-6138719923, 22471013716, true⟩ ⟨-34627399030, -9843480041, true⟩
    ⟨1793491747, 2154293912, true⟩ ⟨121805748422, 138019962926, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [40, 48]`. -/
theorem oscB_45_60_40_48 : legBOk (PBI 45 60) (TBI 40 48) ⟨4889114818, 4986890177, true⟩
    ⟨1793491747, 2154293912, true⟩ ⟨-52004939637, 26619089387, true⟩
    ⟨-55483182242, 21675681664, true⟩ ⟨3506500426, 4195411382, true⟩
    ⟨139850763545, 158461726523, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [40, 48]`. -/
theorem oscF_45_60_40_48 : finalOk
    ⟨-6138719923, 22471013716, true⟩ ⟨-34627399030, -9843480041, true⟩
    ⟨-52004939637, 26619089387, true⟩ ⟨-55483182242, 21675681664, true⟩
    ⟨3506500426, 4195411382, true⟩ ⟨121805748422, 138019962926, true⟩
    ⟨139850763545, 158461726523, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_45_60_40_48 : OscLeaf 40 59 72 3086000000 4502000000 45 60 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_40_48, oscB_45_60_40_48, oscF_45_60_40_48⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [48, 56]`. -/
theorem oscA_45_60_48_56 : legAOk (PBI 45 60) (TBI 48 56) ⟨4949635656, 5045834129, true⟩
    ⟨-8627748992, 21187729420, true⟩ ⟨-35077815774, -8133755308, true⟩
    ⟨1757160074, 2159354365, true⟩ ⟨120192067159, 138891867388, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [48, 56]`. -/
theorem oscB_45_60_48_56 : legBOk (PBI 45 60) (TBI 48 56) ⟨4949635656, 5045834129, true⟩
    ⟨1757160074, 2159354365, true⟩ ⟨-55486035460, 26406776594, true⟩
    ⟨-56652592908, 24750169198, true⟩ ⟨3462146497, 4190454779, true⟩
    ⟨140155695771, 158662047292, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [48, 56]`. -/
theorem oscF_45_60_48_56 : finalOk
    ⟨-8627748992, 21187729420, true⟩ ⟨-35077815774, -8133755308, true⟩
    ⟨-55486035460, 26406776594, true⟩ ⟨-56652592908, 24750169198, true⟩
    ⟨3462146497, 4190454779, true⟩ ⟨120192067159, 138891867388, true⟩
    ⟨140155695771, 158662047292, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [48, 56]` is a leaf of the cover. -/
theorem oscLeaf_45_60_48_56 : OscLeaf 40 59 72 3086000000 4502000000 45 60 48 56 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_48_56, oscB_45_60_48_56, oscF_45_60_48_56⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [56, 64]`. -/
theorem oscA_45_60_56_64 : legAOk (PBI 45 60) (TBI 56 64) ⟨5009592197, 5104260473, true⟩
    ⟨-9741391756, 19563062427, true⟩ ⟨-34907437255, -7520149681, true⟩
    ⟨1762810297, 2163849390, true⟩ ⟨121191854414, 139771659852, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [56, 64]`. -/
theorem oscB_45_60_56_64 : legBOk (PBI 45 60) (TBI 56 64) ⟨5009592197, 5104260473, true⟩
    ⟨1762810297, 2163849390, true⟩ ⟨-56613184879, 24707097178, true⟩
    ⟨-56252614721, 25727636249, true⟩ ⟨3460752788, 4186180212, true⟩
    ⟨140531228074, 158948205434, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [56, 64]`. -/
theorem oscF_45_60_56_64 : finalOk
    ⟨-9741391756, 19563062427, true⟩ ⟨-34907437255, -7520149681, true⟩
    ⟨-56613184879, 24707097178, true⟩ ⟨-56252614721, 25727636249, true⟩
    ⟨3460752788, 4186180212, true⟩ ⟨121191854414, 139771659852, true⟩
    ⟨140531228074, 158948205434, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [56, 64]` is a leaf of the cover. -/
theorem oscLeaf_45_60_56_64 : OscLeaf 40 59 72 3086000000 4502000000 45 60 56 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_56_64, oscB_45_60_56_64, oscF_45_60_56_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [64, 72]`. -/
theorem oscA_45_60_64_72 : legAOk (PBI 45 60) (TBI 64 72) ⟨5069007985, 5162190196, true⟩
    ⟨-10809961051, 18029385183, true⟩ ⟨-34697687334, -6670812709, true⟩
    ⟨1766398691, 2170881865, true⟩ ⟨122090500178, 140758620276, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [64, 72]`. -/
theorem oscB_45_60_64_72 : legBOk (PBI 45 60) (TBI 64 72) ⟨5069007985, 5162190196, true⟩
    ⟨1766398691, 2170881865, true⟩ ⟨-57734083802, 23229606752, true⟩
    ⟨-55888914986, 27021424254, true⟩ ⟨3458937410, 4184796048, true⟩
    ⟨141022766627, 159261211919, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [64, 72]`. -/
theorem oscF_45_60_64_72 : finalOk
    ⟨-10809961051, 18029385183, true⟩ ⟨-34697687334, -6670812709, true⟩
    ⟨-57734083802, 23229606752, true⟩ ⟨-55888914986, 27021424254, true⟩
    ⟨3458937410, 4184796048, true⟩ ⟨122090500178, 140758620276, true⟩
    ⟨141022766627, 159261211919, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [64, 72]` is a leaf of the cover. -/
theorem oscLeaf_45_60_64_72 : OscLeaf 40 59 72 3086000000 4502000000 45 60 64 72 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_64_72, oscB_45_60_64_72, oscF_45_60_64_72⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [72, 80]`. -/
theorem oscA_45_60_72_80 : legAOk (PBI 45 60) (TBI 72 80) ⟨5127905333, 5219643256, true⟩
    ⟨-10890492843, 14873499037, true⟩ ⟨-32237906102, -6192896413, true⟩
    ⟨1770117276, 2127422760, true⟩ ⟨122978649095, 138894826277, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [72, 80]`. -/
theorem oscB_45_60_72_80 : legBOk (PBI 45 60) (TBI 72 80) ⟨5127905333, 5219643256, true⟩
    ⟨1770117276, 2127422760, true⟩ ⟨-58150237604, 19704944652, true⟩
    ⟨-53565775045, 27716536468, true⟩ ⟨3430432811, 4134174358, true⟩
    ⟨139539492455, 159660976511, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [72, 80]`. -/
theorem oscF_45_60_72_80 : finalOk
    ⟨-10890492843, 14873499037, true⟩ ⟨-32237906102, -6192896413, true⟩
    ⟨-58150237604, 19704944652, true⟩ ⟨-53565775045, 27716536468, true⟩
    ⟨3430432811, 4134174358, true⟩ ⟨122978649095, 138894826277, true⟩
    ⟨139539492455, 159660976511, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[45, 60] × [72, 80]` is a leaf of the cover. -/
theorem oscLeaf_45_60_72_80 : OscLeaf 40 59 72 3086000000 4502000000 45 60 72 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_72_80, oscB_45_60_72_80, oscF_45_60_72_80⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
