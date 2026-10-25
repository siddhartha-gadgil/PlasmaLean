/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 15

Leaves 112–119 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[90, 105] × [80, 96]`. -/
theorem oscA_90_105_80_96 : legAOk (PBI 90 105) (TBI 80 96) ⟨5282790666, 5421346032, true⟩
    ⟨-17107235571, 14586019496, true⟩ ⟨-32600490093, 3450679490, true⟩
    ⟨1630727924, 2058811483, true⟩ ⟨120018969086, 140617179541, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [80, 96]`. -/
theorem oscB_90_105_80_96 : legBOk (PBI 90 105) (TBI 80 96) ⟨5282790666, 5421346032, true⟩
    ⟨1630727924, 2058811483, true⟩ ⟨-71612720158, 20685310211, true⟩
    ⟨-58047922447, 46542098082, true⟩ ⟨3165818798, 3968285893, true⟩
    ⟨135500422445, 158033686163, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [80, 96]`. -/
theorem oscF_90_105_80_96 : finalOk
    ⟨-17107235571, 14586019496, true⟩ ⟨-32600490093, 3450679490, true⟩
    ⟨-71612720158, 20685310211, true⟩ ⟨-58047922447, 46542098082, true⟩
    ⟨3165818798, 3968285893, true⟩ ⟨120018969086, 140617179541, true⟩
    ⟨135500422445, 158033686163, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [80, 96]` is a leaf of the cover. -/
theorem oscLeaf_90_105_80_96 : OscLeaf 40 59 72 3086000000 4502000000 90 105 80 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_80_96, oscB_90_105_80_96, oscF_90_105_80_96⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [96, 112]`. -/
theorem oscA_90_105_96_112 : legAOk (PBI 90 105) (TBI 96 112) ⟨5392907025, 5528344352, true⟩
    ⟨-19081919294, 15281326172, true⟩ ⟨-30779340727, 7597993447, true⟩
    ⟨1605968611, 2076336302, true⟩ ⟨119792158474, 142845685710, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [96, 112]`. -/
theorem oscB_90_105_96_112 : legBOk (PBI 90 105) (TBI 96 112) ⟨5392907025, 5528344352, true⟩
    ⟨1605968611, 2076336302, true⟩ ⟨-74091921005, 22906770312, true⟩
    ⟨-57982398853, 52952125415, true⟩ ⟨3133451756, 3976277121, true⟩
    ⟨136620494667, 159035727566, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [96, 112]`. -/
theorem oscF_90_105_96_112 : finalOk
    ⟨-19081919294, 15281326172, true⟩ ⟨-30779340727, 7597993447, true⟩
    ⟨-74091921005, 22906770312, true⟩ ⟨-57982398853, 52952125415, true⟩
    ⟨3133451756, 3976277121, true⟩ ⟨119792158474, 142845685710, true⟩
    ⟨136620494667, 159035727566, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [96, 112]` is a leaf of the cover. -/
theorem oscLeaf_90_105_96_112 : OscLeaf 40 59 72 3086000000 4502000000 90 105 96 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_96_112, oscB_90_105_96_112, oscF_90_105_96_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [112, 128]`. -/
theorem oscA_90_105_112_128 : legAOk (PBI 90 105) (TBI 112 128) ⟨5501458377, 5633944924, true⟩
    ⟨-19445174038, 14536586951, true⟩ ⟨-26285609133, 9556097368, true⟩
    ⟨1616985304, 2046035407, true⟩ ⟨121877533442, 142330734311, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [112, 128]`. -/
theorem oscB_90_105_112_128 : legBOk (PBI 90 105) (TBI 112 128) ⟨5501458377, 5633944924, true⟩
    ⟨1616985304, 2046035407, true⟩ ⟨-73780003297, 20221037895, true⟩
    ⟨-51328376789, 53571981784, true⟩ ⟨3115086536, 3908320404, true⟩
    ⟨136069647882, 158022962471, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [112, 128]`. -/
theorem oscF_90_105_112_128 : finalOk
    ⟨-19445174038, 14536586951, true⟩ ⟨-26285609133, 9556097368, true⟩
    ⟨-73780003297, 20221037895, true⟩ ⟨-51328376789, 53571981784, true⟩
    ⟨3115086536, 3908320404, true⟩ ⟨121877533442, 142330734311, true⟩
    ⟨136069647882, 158022962471, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [112, 128]` is a leaf of the cover. -/
theorem oscLeaf_90_105_112_128 : OscLeaf 40 59 72 3086000000 4502000000 90 105 112 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_112_128, oscB_90_105_112_128, oscF_90_105_112_128⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [0, 8]`. -/
theorem oscA_105_120_0_8 : legAOk (PBI 105 120) (TBI 0 8) ⟨4742978538, 4839186548, true⟩
    ⟨-3914186597, 27923641826, true⟩ ⟨-37956649624, -11008204091, true⟩
    ⟨1689421682, 2053113932, true⟩ ⟨118306312374, 136296841920, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [0, 8]`. -/
theorem oscB_105_120_0_8 : legBOk (PBI 105 120) (TBI 0 8) ⟨4742978538, 4839186548, true⟩
    ⟨1689421682, 2053113932, true⟩ ⟨-51850287395, 29717353064, true⟩
    ⟨-56186710977, 24932192557, true⟩ ⟨3350623151, 4024261262, true⟩
    ⟨137245564083, 155502443382, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [0, 8]`. -/
theorem oscF_105_120_0_8 : finalOk
    ⟨-3914186597, 27923641826, true⟩ ⟨-37956649624, -11008204091, true⟩
    ⟨-51850287395, 29717353064, true⟩ ⟨-56186710977, 24932192557, true⟩
    ⟨3350623151, 4024261262, true⟩ ⟨118306312374, 136296841920, true⟩
    ⟨137245564083, 155502443382, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[105, 120] × [0, 8]` is a leaf of the cover. -/
theorem oscLeaf_105_120_0_8 : OscLeaf 40 59 72 3086000000 4502000000 105 120 0 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_0_8, oscB_105_120_0_8, oscF_105_120_0_8⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [8, 16]`. -/
theorem oscA_105_120_8_16 : legAOk (PBI 105 120) (TBI 8 16) ⟨4802328838, 4897007511, true⟩
    ⟨-5746677487, 26183833349, true⟩ ⟨-38449749603, -10916086922, true⟩
    ⟨1691581521, 2056603885, true⟩ ⟨119032191395, 137026107835, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [8, 16]`. -/
theorem oscB_105_120_8_16 : legBOk (PBI 105 120) (TBI 8 16) ⟨4802328838, 4897007511, true⟩
    ⟨1691581521, 2056603885, true⟩ ⟨-53660960940, 27998243974, true⟩
    ⟨-56369445547, 25303229726, true⟩ ⟨3345660774, 4017869735, true⟩
    ⟨137518950885, 155611346117, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [8, 16]`. -/
theorem oscF_105_120_8_16 : finalOk
    ⟨-5746677487, 26183833349, true⟩ ⟨-38449749603, -10916086922, true⟩
    ⟨-53660960940, 27998243974, true⟩ ⟨-56369445547, 25303229726, true⟩
    ⟨3345660774, 4017869735, true⟩ ⟨119032191395, 137026107835, true⟩
    ⟨137518950885, 155611346117, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[105, 120] × [8, 16]` is a leaf of the cover. -/
theorem oscLeaf_105_120_8_16 : OscLeaf 40 59 72 3086000000 4502000000 105 120 8 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_8_16, oscB_105_120_8_16, oscF_105_120_8_16⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [16, 24]`. -/
theorem oscA_105_120_16_24 : legAOk (PBI 105 120) (TBI 16 24) ⟨4861094353, 4954290658, true⟩
    ⟨-7460974259, 24441185797, true⟩ ⟨-38736911521, -10640484881, true⟩
    ⟨1694715747, 2060543753, true⟩ ⟨119822602615, 137795387263, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [16, 24]`. -/
theorem oscB_105_120_16_24 : legBOk (PBI 105 120) (TBI 16 24) ⟨4861094353, 4954290658, true⟩
    ⟨1694715747, 2060543753, true⟩ ⟨-55397471657, 26314113387, true⟩
    ⟨-56354784839, 25921271411, true⟩ ⟨3342156020, 4013433205, true⟩
    ⟨137831287003, 155826713399, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [16, 24]`. -/
theorem oscF_105_120_16_24 : finalOk
    ⟨-7460974259, 24441185797, true⟩ ⟨-38736911521, -10640484881, true⟩
    ⟨-55397471657, 26314113387, true⟩ ⟨-56354784839, 25921271411, true⟩
    ⟨3342156020, 4013433205, true⟩ ⟨119822602615, 137795387263, true⟩
    ⟨137831287003, 155826713399, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[105, 120] × [16, 24]` is a leaf of the cover. -/
theorem oscLeaf_105_120_16_24 : OscLeaf 40 59 72 3086000000 4502000000 105 120 16 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_16_24, oscB_105_120_16_24, oscF_105_120_16_24⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [24, 32]`. -/
theorem oscA_105_120_24_32 : legAOk (PBI 105 120) (TBI 24 32) ⟨4919299139, 5011057434, true⟩
    ⟨-8050639596, 20851040541, true⟩ ⟨-36850778965, -10818278046, true⟩
    ⟨1699160358, 2019153602, true⟩ ⟨120690771703, 135866366661, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [24, 32]`. -/
theorem oscB_105_120_24_32 : legBOk (PBI 105 120) (TBI 24 32) ⟨4919299139, 5011057434, true⟩
    ⟨1699160358, 2019153602, true⟩ ⟨-55220360362, 21777773089, true⟩
    ⟨-53587790989, 24901321490, true⟩ ⟨3341277965, 3962849410, true⟩
    ⟨138239347657, 155984601346, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [24, 32]`. -/
theorem oscF_105_120_24_32 : finalOk
    ⟨-8050639596, 20851040541, true⟩ ⟨-36850778965, -10818278046, true⟩
    ⟨-55220360362, 21777773089, true⟩ ⟨-53587790989, 24901321490, true⟩
    ⟨3341277965, 3962849410, true⟩ ⟨120690771703, 135866366661, true⟩
    ⟨138239347657, 155984601346, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[105, 120] × [24, 32]` is a leaf of the cover. -/
theorem oscLeaf_105_120_24_32 : OscLeaf 40 59 72 3086000000 4502000000 105 120 24 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_24_32, oscB_105_120_24_32, oscF_105_120_24_32⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [32, 40]`. -/
theorem oscA_105_120_32_40 : legAOk (PBI 105 120) (TBI 32 40) ⟨4976965960, 5067328206, true⟩
    ⟨-10281770009, 19665750334, true⟩ ⟨-37051027927, -8530143936, true⟩
    ⟨1664338899, 2026399173, true⟩ ⟨119060152742, 136828853790, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [32, 40]`. -/
theorem oscB_105_120_32_40 : legBOk (PBI 105 120) (TBI 32 40) ⟨4976965960, 5067328206, true⟩
    ⟨1664338899, 2026399173, true⟩ ⟨-58492217096, 21806124759, true⟩
    ⟨-54978041141, 28594672145, true⟩ ⟨3300155177, 3963977337, true⟩
    ⟨138580330023, 156360411503, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [32, 40]`. -/
theorem oscF_105_120_32_40 : finalOk
    ⟨-10281770009, 19665750334, true⟩ ⟨-37051027927, -8530143936, true⟩
    ⟨-58492217096, 21806124759, true⟩ ⟨-54978041141, 28594672145, true⟩
    ⟨3300155177, 3963977337, true⟩ ⟨119060152742, 136828853790, true⟩
    ⟨138580330023, 156360411503, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[105, 120] × [32, 40]` is a leaf of the cover. -/
theorem oscLeaf_105_120_32_40 : OscLeaf 40 59 72 3086000000 4502000000 105 120 32 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_32_40, oscB_105_120_32_40, oscF_105_120_32_40⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
