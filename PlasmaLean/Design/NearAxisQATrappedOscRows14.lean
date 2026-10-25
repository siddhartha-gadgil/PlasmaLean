/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 14

Leaves 104–111 of the adaptive cover of the start window used by
`Design/NearAxisQATrappedOscCover` (amplitude target `Kn = 40`, period range
`[59, 72] μs`, precession range `ι₀ Δ ∈ [3086000000, 4502000000] · 2⁻³²`).
For each index box `[a, b] × [c, d]` (`ψ₀ ∈ PBI a b`, `B_t ∈ TBI c d`) the inner-leg check
`legAOk`, the outer-leg check `legBOk` (with the inner leg's `I(z₁)` enclosure) and the final
check `finalOk` are checked on the oracle enclosures (all computed by the untrusted exact
mirror `scripts/trapped_reanchor/osc_mirror.py`): the leg checks by `decide +kernel`, the final
check by an evaluation certificate (`fiv_cert`, `Certificates/EvalCert`: one kernel leaf per
interval operation).
-/
public section
namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Design.NearAxisQATrappedCells

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [8, 16]`. -/
theorem oscA_90_105_8_16 : legAOk (PBI 90 105) (TBI 8 16) ⟨4764181923, 4861127163, true⟩
    ⟨-4346300482, 27382168307, true⟩ ⟨-37454790933, -10534396837, true⟩
    ⟨1711776891, 2086973801, true⟩ ⟨118875877259, 137168580928, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [8, 16]`. -/
theorem oscB_90_105_8_16 : legBOk (PBI 90 105) (TBI 8 16) ⟨4764181923, 4861127163, true⟩
    ⟨1711776891, 2086973801, true⟩ ⟨-52090205390, 29991899782, true⟩
    ⟨-56646587319, 24484084553, true⟩ ⟨3386494937, 4077375416, true⟩
    ⟨137740595943, 156179844700, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [8, 16]`. -/
theorem oscF_90_105_8_16 : finalOk
    ⟨-4346300482, 27382168307, true⟩ ⟨-37454790933, -10534396837, true⟩
    ⟨-52090205390, 29991899782, true⟩ ⟨-56646587319, 24484084553, true⟩
    ⟨3386494937, 4077375416, true⟩ ⟨118875877259, 137168580928, true⟩
    ⟨137740595943, 156179844700, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [8, 16]` is a leaf of the cover. -/
theorem oscLeaf_90_105_8_16 : OscLeaf 40 59 72 3086000000 4502000000 90 105 8 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_8_16, oscB_90_105_8_16, oscF_90_105_8_16⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [16, 24]`. -/
theorem oscA_90_105_16_24 : legAOk (PBI 90 105) (TBI 16 24) ⟨4823937707, 4919331949, true⟩
    ⟨-6072051044, 25618383900, true⟩ ⟨-37913091660, -10499152319, true⟩
    ⟨1715182289, 2089337517, true⟩ ⟨119672227066, 137849988321, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [16, 24]`. -/
theorem oscB_90_105_16_24 : legBOk (PBI 90 105) (TBI 16 24) ⟨4823937707, 4919331949, true⟩
    ⟨1715182289, 2089337517, true⟩ ⟨-53746101516, 28176559367, true⟩
    ⟨-56704058028, 24794503670, true⟩ ⟨3382966454, 4070021060, true⟩
    ⟨138052411214, 156325302987, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [16, 24]`. -/
theorem oscF_90_105_16_24 : finalOk
    ⟨-6072051044, 25618383900, true⟩ ⟨-37913091660, -10499152319, true⟩
    ⟨-53746101516, 28176559367, true⟩ ⟨-56704058028, 24794503670, true⟩
    ⟨3382966454, 4070021060, true⟩ ⟨119672227066, 137849988321, true⟩
    ⟨138052411214, 156325302987, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [16, 24]` is a leaf of the cover. -/
theorem oscLeaf_90_105_16_24 : OscLeaf 40 59 72 3086000000 4502000000 90 105 16 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_16_24, oscB_90_105_16_24, oscF_90_105_16_24⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [24, 32]`. -/
theorem oscA_90_105_24_32 : legAOk (PBI 90 105) (TBI 24 32) ⟨4883108027, 4976998768, true⟩
    ⟨-6851962257, 22101382618, true⟩ ⟨-36298775124, -10890705840, true⟩
    ⟨1718674966, 2047584119, true⟩ ⟨120492052384, 135926093576, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [24, 32]`. -/
theorem oscB_90_105_24_32 : legBOk (PBI 90 105) (TBI 24 32) ⟨4883108027, 4976998768, true⟩
    ⟨1718674966, 2047584119, true⟩ ⟨-53679628013, 23692839358, true⟩
    ⟨-54314731946, 23687313436, true⟩ ⟨3379752670, 4018097801, true⟩
    ⟨138378152875, 156436836108, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [24, 32]`. -/
theorem oscF_90_105_24_32 : finalOk
    ⟨-6851962257, 22101382618, true⟩ ⟨-36298775124, -10890705840, true⟩
    ⟨-53679628013, 23692839358, true⟩ ⟨-54314731946, 23687313436, true⟩
    ⟨3379752670, 4018097801, true⟩ ⟨120492052384, 135926093576, true⟩
    ⟨138378152875, 156436836108, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [24, 32]` is a leaf of the cover. -/
theorem oscLeaf_90_105_24_32 : OscLeaf 40 59 72 3086000000 4502000000 90 105 24 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_24_32, oscB_90_105_24_32, oscF_90_105_24_32⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [32, 40]`. -/
theorem oscA_90_105_32_40 : legAOk (PBI 90 105) (TBI 32 40) ⟨4941717097, 5034149210, true⟩
    ⟨-9244155567, 20773324950, true⟩ ⟨-36620941812, -8847691363, true⟩
    ⟨1684981914, 2053482346, true⟩ ⟨118952971208, 136825411203, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [32, 40]`. -/
theorem oscB_90_105_32_40 : legBOk (PBI 90 105) (TBI 32 40) ⟨4941717097, 5034149210, true⟩
    ⟨1684981914, 2053482346, true⟩ ⟨-57039827681, 23454725108, true⟩
    ⟨-55448081545, 26867913813, true⟩ ⟨3340175153, 4015790385, true⟩
    ⟨138769336653, 156688373069, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [32, 40]`. -/
theorem oscF_90_105_32_40 : finalOk
    ⟨-9244155567, 20773324950, true⟩ ⟨-36620941812, -8847691363, true⟩
    ⟨-57039827681, 23454725108, true⟩ ⟨-55448081545, 26867913813, true⟩
    ⟨3340175153, 4015790385, true⟩ ⟨118952971208, 136825411203, true⟩
    ⟨138769336653, 156688373069, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [32, 40]` is a leaf of the cover. -/
theorem oscLeaf_90_105_32_40 : OscLeaf 40 59 72 3086000000 4502000000 90 105 32 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_32_40, oscB_90_105_32_40, oscF_90_105_32_40⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [40, 48]`. -/
theorem oscA_90_105_40_48 : legAOk (PBI 90 105) (TBI 40 48) ⟨4999787848, 5090803758, true⟩
    ⟨-10408604325, 19167930746, true⟩ ⟨-36432800670, -8085765364, true⟩
    ⟨1688263602, 2058725492, true⟩ ⟨119786014690, 137698341621, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [40, 48]`. -/
theorem oscB_90_105_40_48 : legBOk (PBI 90 105) (TBI 40 48) ⟨4999787848, 5090803758, true⟩
    ⟨1688263602, 2058725492, true⟩ ⟨-58336050123, 21945804530, true⟩
    ⟨-55201334160, 28152707188, true⟩ ⟨3337161219, 4014088214, true⟩
    ⟨139130368005, 157026922172, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [40, 48]`. -/
theorem oscF_90_105_40_48 : finalOk
    ⟨-10408604325, 19167930746, true⟩ ⟨-36432800670, -8085765364, true⟩
    ⟨-58336050123, 21945804530, true⟩ ⟨-55201334160, 28152707188, true⟩
    ⟨3337161219, 4014088214, true⟩ ⟨119786014690, 137698341621, true⟩
    ⟨139130368005, 157026922172, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_90_105_40_48 : OscLeaf 40 59 72 3086000000 4502000000 90 105 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_40_48, oscB_90_105_40_48, oscF_90_105_40_48⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [48, 56]`. -/
theorem oscA_90_105_48_56 : legAOk (PBI 90 105) (TBI 48 56) ⟨5057342012, 5146981890, true⟩
    ⟨-11456154181, 17567826783, true⟩ ⟨-35951179450, -7226132610, true⟩
    ⟨1692787994, 2062941401, true⟩ ⟨120677472169, 138518221159, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [48, 56]`. -/
theorem oscB_90_105_48_56 : legBOk (PBI 90 105) (TBI 48 56) ⟨5057342012, 5146981890, true⟩
    ⟨1692787994, 2062941401, true⟩ ⟨-59758931891, 18387550296, true⟩
    ⟨-54190088108, 28060305247, true⟩ ⟨3311677082, 3983262266, true⟩
    ⟨137704086431, 155357975518, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [48, 56]`. -/
theorem oscF_90_105_48_56 : finalOk
    ⟨-11456154181, 17567826783, true⟩ ⟨-35951179450, -7226132610, true⟩
    ⟨-59758931891, 18387550296, true⟩ ⟨-54190088108, 28060305247, true⟩
    ⟨3311677082, 3983262266, true⟩ ⟨120677472169, 138518221159, true⟩
    ⟨137704086431, 155357975518, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [48, 56]` is a leaf of the cover. -/
theorem oscLeaf_90_105_48_56 : OscLeaf 40 59 72 3086000000 4502000000 90 105 48 56 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_48_56, oscB_90_105_48_56, oscF_90_105_48_56⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [56, 64]`. -/
theorem oscA_90_105_56_64 : legAOk (PBI 90 105) (TBI 56 64) ⟨5114400220, 5202702146, true⟩
    ⟨-12470484487, 16084430612, true⟩ ⟨-35439367545, -6129642811, true⟩
    ⟨1696831390, 2070239294, true⟩ ⟨121582933105, 139517025038, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [56, 64]`. -/
theorem oscB_90_105_56_64 : legBOk (PBI 90 105) (TBI 56 64) ⟨5114400220, 5202702146, true⟩
    ⟨1696831390, 2070239294, true⟩ ⟨-60761090895, 16948603093, true⟩
    ⟨-53517602491, 29612339734, true⟩ ⟨3310473306, 3981680023, true⟩
    ⟨138139832970, 155559364478, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [56, 64]`. -/
theorem oscF_90_105_56_64 : finalOk
    ⟨-12470484487, 16084430612, true⟩ ⟨-35439367545, -6129642811, true⟩
    ⟨-60761090895, 16948603093, true⟩ ⟨-53517602491, 29612339734, true⟩
    ⟨3310473306, 3981680023, true⟩ ⟨121582933105, 139517025038, true⟩
    ⟨138139832970, 155559364478, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [56, 64]` is a leaf of the cover. -/
theorem oscLeaf_90_105_56_64 : OscLeaf 40 59 72 3086000000 4502000000 90 105 56 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_56_64, oscB_90_105_56_64, oscF_90_105_56_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [64, 80]`. -/
theorem oscA_90_105_64_80 : legAOk (PBI 90 105) (TBI 64 80) ⟨5170982095, 5312838899, true⟩
    ⟨-16009381447, 16656518747, true⟩ ⟨-36261640380, -417484394, true⟩
    ⟨1658587286, 2090246990, true⟩ ⟨120469822081, 141287235746, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [64, 80]`. -/
theorem oscB_90_105_64_80 : legBOk (PBI 90 105) (TBI 64 80) ⟨5170982095, 5312838899, true⟩
    ⟨1658587286, 2090246990, true⟩ ⟨-69741957433, 24326811320, true⟩
    ⟨-61862317889, 43155558774, true⟩ ⟨3226765988, 4039342641, true⟩
    ⟨136336356145, 159197178838, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [64, 80]`. -/
theorem oscF_90_105_64_80 : finalOk
    ⟨-16009381447, 16656518747, true⟩ ⟨-36261640380, -417484394, true⟩
    ⟨-69741957433, 24326811320, true⟩ ⟨-61862317889, 43155558774, true⟩
    ⟨3226765988, 4039342641, true⟩ ⟨120469822081, 141287235746, true⟩
    ⟨136336356145, 159197178838, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [64, 80]` is a leaf of the cover. -/
theorem oscLeaf_90_105_64_80 : OscLeaf 40 59 72 3086000000 4502000000 90 105 64 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_64_80, oscB_90_105_64_80, oscF_90_105_64_80⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
