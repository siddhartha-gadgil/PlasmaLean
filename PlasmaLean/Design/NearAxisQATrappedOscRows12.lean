/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 12

Leaves 88–95 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[60, 75] × [96, 112]`. -/
theorem oscA_60_75_96_112 : legAOk (PBI 60 75) (TBI 96 112) ⟨5333161703, 5473747297, true⟩
    ⟨-17091255815, 14398587654, true⟩ ⟨-31372572596, 4258631301, true⟩
    ⟨1678649697, 2133050954, true⟩ ⟨121614080728, 142810200581, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [96, 112]`. -/
theorem oscB_60_75_96_112 : legBOk (PBI 60 75) (TBI 96 112) ⟨5333161703, 5473747297, true⟩
    ⟨1678649697, 2133050954, true⟩ ⟨-71117442952, 22050698309, true⟩
    ⟨-58431960656, 46191635010, true⟩ ⟨3237454913, 4078899311, true⟩
    ⟨136733856431, 159615346312, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [96, 112]`. -/
theorem oscF_60_75_96_112 : finalOk
    ⟨-17091255815, 14398587654, true⟩ ⟨-31372572596, 4258631301, true⟩
    ⟨-71117442952, 22050698309, true⟩ ⟨-58431960656, 46191635010, true⟩
    ⟨3237454913, 4078899311, true⟩ ⟨121614080728, 142810200581, true⟩
    ⟨136733856431, 159615346312, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[60, 75] × [96, 112]` is a leaf of the cover. -/
theorem oscLeaf_60_75_96_112 : OscLeaf 40 59 72 3086000000 4502000000 60 75 96 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_96_112, oscB_60_75_96_112, oscF_60_75_96_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[60, 75] × [112, 128]`. -/
theorem oscA_60_75_112_128 : legAOk (PBI 60 75) (TBI 112 128) ⟨5445023222, 5582415776, true⟩
    ⟨-18942951756, 15260640875, true⟩ ⟨-29452148708, 8248918365, true⟩
    ⟨1653796582, 2150516475, true⟩ ⟨121478826788, 145078758682, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[60, 75] × [112, 128]`. -/
theorem oscB_60_75_112_128 : legBOk (PBI 60 75) (TBI 112 128) ⟨5445023222, 5582415776, true⟩
    ⟨1653796582, 2150516475, true⟩ ⟨-73485675109, 24295043976, true⟩
    ⟨-58101176809, 52406571479, true⟩ ⟨3205328458, 4084209986, true⟩
    ⟨137963387943, 160525185626, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[60, 75] × [112, 128]`. -/
theorem oscF_60_75_112_128 : finalOk
    ⟨-18942951756, 15260640875, true⟩ ⟨-29452148708, 8248918365, true⟩
    ⟨-73485675109, 24295043976, true⟩ ⟨-58101176809, 52406571479, true⟩
    ⟨3205328458, 4084209986, true⟩ ⟨121478826788, 145078758682, true⟩
    ⟨137963387943, 160525185626, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[60, 75] × [112, 128]` is a leaf of the cover. -/
theorem oscLeaf_60_75_112_128 : OscLeaf 40 59 72 3086000000 4502000000 60 75 112 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_60_75_112_128, oscB_60_75_112_128, oscF_60_75_112_128⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [0, 8]`. -/
theorem oscA_75_90_0_8 : legAOk (PBI 75 90) (TBI 0 8) ⟨4663188367, 4764214733, true⟩
    ⟨-939691929, 30107654135, true⟩ ⟨-35406305255, -9707754308, true⟩
    ⟨1733536041, 2114789260, true⟩ ⟨118141495752, 136569786033, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [0, 8]`. -/
theorem oscB_75_90_0_8 : legBOk (PBI 75 90) (TBI 0 8) ⟨4663188367, 4764214733, true⟩
    ⟨1733536041, 2114789260, true⟩ ⟨-48644548112, 35223146731, true⟩
    ⟨-55896018658, 25066992737, true⟩ ⟨3463576433, 4174610457, true⟩
    ⟨139638338980, 158666210223, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [0, 8]`. -/
theorem oscF_75_90_0_8 : finalOk
    ⟨-939691929, 30107654135, true⟩ ⟨-35406305255, -9707754308, true⟩
    ⟨-48644548112, 35223146731, true⟩ ⟨-55896018658, 25066992737, true⟩
    ⟨3463576433, 4174610457, true⟩ ⟨118141495752, 136569786033, true⟩
    ⟨139638338980, 158666210223, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [0, 8]` is a leaf of the cover. -/
theorem oscLeaf_75_90_0_8 : OscLeaf 40 59 72 3086000000 4502000000 75 90 0 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_0_8, oscB_75_90_0_8, oscF_75_90_0_8⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [8, 16]`. -/
theorem oscA_75_90_8_16 : legAOk (PBI 75 90) (TBI 8 16) ⟨4724623577, 4823970518, true⟩
    ⟨-2933798064, 28552790280, true⟩ ⟨-36238475745, -9949405081, true⟩
    ⟨1733526363, 2119754989, true⟩ ⟨118756028235, 137382938871, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [8, 16]`. -/
theorem oscB_75_90_8_16 : legBOk (PBI 75 90) (TBI 8 16) ⟨4724623577, 4823970518, true⟩
    ⟨1733526363, 2119754989, true⟩ ⟨-51267170457, 34732153589, true⟩
    ⟨-57631873717, 26118704301, true⟩ ⟨3428454220, 4169980356, true⟩
    ⟨137866605316, 158846625610, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [8, 16]`. -/
theorem oscF_75_90_8_16 : finalOk
    ⟨-2933798064, 28552790280, true⟩ ⟨-36238475745, -9949405081, true⟩
    ⟨-51267170457, 34732153589, true⟩ ⟨-57631873717, 26118704301, true⟩
    ⟨3428454220, 4169980356, true⟩ ⟨118756028235, 137382938871, true⟩
    ⟨137866605316, 158846625610, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [8, 16]` is a leaf of the cover. -/
theorem oscLeaf_75_90_8_16 : OscLeaf 40 59 72 3086000000 4502000000 75 90 8 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_8_16, oscB_75_90_8_16, oscF_75_90_8_16⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [16, 24]`. -/
theorem oscA_75_90_16_24 : legAOk (PBI 75 90) (TBI 16 24) ⟨4785419182, 4883140838, true⟩
    ⟨-4631313114, 26766215852, true⟩ ⟨-36887188996, -10167555958, true⟩
    ⟨1737245954, 2120300294, true⟩ ⟨119566576006, 137956729368, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [16, 24]`. -/
theorem oscB_75_90_16_24 : legBOk (PBI 75 90) (TBI 16 24) ⟨4785419182, 4883140838, true⟩
    ⟨1737245954, 2120300294, true⟩ ⟨-52057711784, 30160986521, true⟩
    ⟨-56875285666, 23868637358, true⟩ ⟨3425481897, 4130118705, true⟩
    ⟨138219063143, 156841798280, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [16, 24]`. -/
theorem oscF_75_90_16_24 : finalOk
    ⟨-4631313114, 26766215852, true⟩ ⟨-36887188996, -10167555958, true⟩
    ⟨-52057711784, 30160986521, true⟩ ⟨-56875285666, 23868637358, true⟩
    ⟨3425481897, 4130118705, true⟩ ⟨119566576006, 137956729368, true⟩
    ⟨138219063143, 156841798280, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [16, 24]` is a leaf of the cover. -/
theorem oscLeaf_75_90_16_24 : OscLeaf 40 59 72 3086000000 4502000000 75 90 16 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_16_24, oscB_75_90_16_24, oscF_75_90_16_24⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [24, 32]`. -/
theorem oscA_75_90_24_32 : legAOk (PBI 75 90) (TBI 24 32) ⟨4845602556, 4941749907, true⟩
    ⟨-6418144297, 25130369618, true⟩ ⟨-37338389588, -10003986880, true⟩
    ⟨1740398602, 2125379786, true⟩ ⟨120383806322, 138816063007, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [24, 32]`. -/
theorem oscB_75_90_24_32 : legBOk (PBI 75 90) (TBI 24 32) ⟨4845602556, 4941749907, true⟩
    ⟨1740398602, 2125379786, true⟩ ⟨-53757685220, 28467012055, true⟩
    ⟨-57002435252, 24249512139, true⟩ ⟨3423241839, 4125455279, true⟩
    ⟨138667809911, 157012211757, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [24, 32]`. -/
theorem oscF_75_90_24_32 : finalOk
    ⟨-6418144297, 25130369618, true⟩ ⟨-37338389588, -10003986880, true⟩
    ⟨-53757685220, 28467012055, true⟩ ⟨-57002435252, 24249512139, true⟩
    ⟨3423241839, 4125455279, true⟩ ⟨120383806322, 138816063007, true⟩
    ⟨138667809911, 157012211757, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [24, 32]` is a leaf of the cover. -/
theorem oscLeaf_75_90_24_32 : OscLeaf 40 59 72 3086000000 4502000000 75 90 24 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_24_32, oscB_75_90_24_32, oscF_75_90_24_32⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [32, 40]`. -/
theorem oscA_75_90_32_40 : legAOk (PBI 75 90) (TBI 32 40) ⟨4905199512, 4999820657, true⟩
    ⟨-7152725118, 21635540042, true⟩ ⟨-35783294247, -10371129189, true⟩
    ⟨1743521926, 2082990611, true⟩ ⟨121195484192, 136885468028, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [32, 40]`. -/
theorem oscB_75_90_32_40 : legBOk (PBI 75 90) (TBI 32 40) ⟨4905199512, 4999820657, true⟩
    ⟨1743521926, 2082990611, true⟩ ⟨-53749911255, 24100881206, true⟩
    ⟨-54741620249, 23348083214, true⟩ ⟨3417932717, 4073438068, true⟩
    ⟨138892615043, 157185024014, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [32, 40]`. -/
theorem oscF_75_90_32_40 : finalOk
    ⟨-7152725118, 21635540042, true⟩ ⟨-35783294247, -10371129189, true⟩
    ⟨-53749911255, 24100881206, true⟩ ⟨-54741620249, 23348083214, true⟩
    ⟨3417932717, 4073438068, true⟩ ⟨121195484192, 136885468028, true⟩
    ⟨138892615043, 157185024014, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [32, 40]` is a leaf of the cover. -/
theorem oscLeaf_75_90_32_40 : OscLeaf 40 59 72 3086000000 4502000000 75 90 32 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_32_40, oscB_75_90_32_40, oscF_75_90_32_40⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [40, 48]`. -/
theorem oscA_75_90_40_48 : legAOk (PBI 75 90) (TBI 40 48) ⟨4964234466, 5057374819, true⟩
    ⟨-9478731385, 20380405922, true⟩ ⟨-36078928486, -8354323025, true⟩
    ⟨1708119724, 2088898756, true⟩ ⟨119577846348, 137783524031, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [40, 48]`. -/
theorem oscB_75_90_40_48 : legBOk (PBI 75 90) (TBI 40 48) ⟨4964234466, 5057374819, true⟩
    ⟨1708119724, 2088898756, true⟩ ⟨-57070748776, 23894125557, true⟩
    ⟨-55888041750, 26650315677, true⟩ ⟨3376470706, 4070882266, true⟩
    ⟨139293078129, 157442054452, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [40, 48]`. -/
theorem oscF_75_90_40_48 : finalOk
    ⟨-9478731385, 20380405922, true⟩ ⟨-36078928486, -8354323025, true⟩
    ⟨-57070748776, 23894125557, true⟩ ⟨-55888041750, 26650315677, true⟩
    ⟨3376470706, 4070882266, true⟩ ⟨119577846348, 137783524031, true⟩
    ⟨139293078129, 157442054452, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_75_90_40_48 : OscLeaf 40 59 72 3086000000 4502000000 75 90 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_40_48, oscB_75_90_40_48, oscF_75_90_40_48⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
