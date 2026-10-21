/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells

/-!
# Kernel checks of the oscillatory-kick cover, part 5

Leaves 32–39 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[15, 30] × [36, 40]`. -/
theorem oscA_15_30_36_40 : legAOk (PBI 15 30) (TBI 36 40) ⟨4776369527, 4849390534, true⟩
    ⟨-1097644160, 25811424985, true⟩ ⟨-32320449162, -9828432955, true⟩
    ⟨1853816895, 2245535772, true⟩ ⟨121428376592, 139111746915, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [36, 40]`. -/
theorem oscB_15_30_36_40 : legBOk (PBI 15 30) (TBI 36 40) ⟨4776369527, 4849390534, true⟩
    ⟨1853816895, 2245535772, true⟩ ⟨-44529028098, 31680147264, true⟩
    ⟨-53507997035, 18309399765, true⟩ ⟨3657932024, 4369563586, true⟩
    ⟨142577965033, 160259871288, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [36, 40]`. -/
theorem oscF_15_30_36_40 : finalOk
    ⟨-1097644160, 25811424985, true⟩ ⟨-32320449162, -9828432955, true⟩
    ⟨-44529028098, 31680147264, true⟩ ⟨-53507997035, 18309399765, true⟩
    ⟨3657932024, 4369563586, true⟩ ⟨121428376592, 139111746915, true⟩
    ⟨142577965033, 160259871288, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [36, 40]` is a leaf of the cover. -/
theorem oscLeaf_15_30_36_40 : OscLeaf 40 59 72 3086000000 4502000000 15 30 36 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_36_40, oscB_15_30_36_40, oscF_15_30_36_40⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [40, 48]`. -/
theorem oscA_15_30_40_48 : legAOk (PBI 15 30) (TBI 40 48) ⟨4807991748, 4911002438, true⟩
    ⟨-3272857681, 24933037501, true⟩ ⟨-32766653164, -9306169472, true⟩
    ⟨1849515679, 2230227284, true⟩ ⟨121873074373, 138520720036, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [40, 48]`. -/
theorem oscB_15_30_40_48 : legBOk (PBI 15 30) (TBI 40 48) ⟨4807991748, 4911002438, true⟩
    ⟨1849515679, 2230227284, true⟩ ⟨-48509522661, 33064797121, true⟩
    ⟨-55603793883, 20982045614, true⟩ ⟨3638377880, 4370656301, true⟩
    ⟨142401038273, 161898923951, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [40, 48]`. -/
theorem oscF_15_30_40_48 : finalOk
    ⟨-3272857681, 24933037501, true⟩ ⟨-32766653164, -9306169472, true⟩
    ⟨-48509522661, 33064797121, true⟩ ⟨-55603793883, 20982045614, true⟩
    ⟨3638377880, 4370656301, true⟩ ⟨121873074373, 138520720036, true⟩
    ⟨142401038273, 161898923951, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_15_30_40_48 : OscLeaf 40 59 72 3086000000 4502000000 15 30 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_40_48, oscB_15_30_40_48, oscF_15_30_40_48⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [48, 56]`. -/
theorem oscA_15_30_48_56 : legAOk (PBI 15 30) (TBI 48 56) ⟨4870753483, 4972023364, true⟩
    ⟨-6133085066, 23678169451, true⟩ ⟨-33642312333, -8081727875, true⟩
    ⟨1810515361, 2235308268, true⟩ ⟨120156719077, 139387288073, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [48, 56]`. -/
theorem oscB_15_30_48_56 : legBOk (PBI 15 30) (TBI 48 56) ⟨4870753483, 4972023364, true⟩
    ⟨1810515361, 2235308268, true⟩ ⟨-53027306162, 33861590970, true⟩
    ⟨-58228023023, 24474661631, true⟩ ⟨3564081166, 4366945980, true⟩
    ⟨140772722491, 162250789431, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [48, 56]`. -/
theorem oscF_15_30_48_56 : finalOk
    ⟨-6133085066, 23678169451, true⟩ ⟨-33642312333, -8081727875, true⟩
    ⟨-53027306162, 33861590970, true⟩ ⟨-58228023023, 24474661631, true⟩
    ⟨3564081166, 4366945980, true⟩ ⟨120156719077, 139387288073, true⟩
    ⟨140772722491, 162250789431, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [48, 56]` is a leaf of the cover. -/
theorem oscLeaf_15_30_48_56 : OscLeaf 40 59 72 3086000000 4502000000 15 30 48 56 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_48_56, oscB_15_30_48_56, oscF_15_30_48_56⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [56, 64]`. -/
theorem oscA_15_30_56_64 : legAOk (PBI 15 30) (TBI 56 64) ⟨4932895187, 5032478440, true⟩
    ⟨-7642951695, 22071749450, true⟩ ⟨-33913121900, -7795021852, true⟩
    ⟨1814113359, 2239236944, true⟩ ⟨121032586050, 140210593681, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [56, 64]`. -/
theorem oscB_15_30_56_64 : legBOk (PBI 15 30) (TBI 56 64) ⟨4932895187, 5032478440, true⟩
    ⟨1814113359, 2239236944, true⟩ ⟨-53678503763, 29313898550, true⟩
    ⟨-57215743756, 22852420385, true⟩ ⟨3560175659, 4325483308, true⟩
    ⟨141168874250, 160077983373, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [56, 64]`. -/
theorem oscF_15_30_56_64 : finalOk
    ⟨-7642951695, 22071749450, true⟩ ⟨-33913121900, -7795021852, true⟩
    ⟨-53678503763, 29313898550, true⟩ ⟨-57215743756, 22852420385, true⟩
    ⟨3560175659, 4325483308, true⟩ ⟨121032586050, 140210593681, true⟩
    ⟨141168874250, 160077983373, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [56, 64]` is a leaf of the cover. -/
theorem oscLeaf_15_30_56_64 : OscLeaf 40 59 72 3086000000 4502000000 15 30 56 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_56_64, oscB_15_30_56_64, oscF_15_30_56_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [64, 72]`. -/
theorem oscA_15_30_64_72 : legAOk (PBI 15 30) (TBI 64 72) ⟨4994443762, 5092391459, true⟩
    ⟨-8997263418, 20605258721, true⟩ ⟨-34077851430, -7173463077, true⟩
    ⟨1816167592, 2247679258, true⟩ ⟨121865825670, 141278617032, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [64, 72]`. -/
theorem oscB_15_30_64_72 : legBOk (PBI 15 30) (TBI 64 72) ⟨4994443762, 5092391459, true⟩
    ⟨1816167592, 2247679258, true⟩ ⟨-55168615497, 27991134046, true⟩
    ⟨-57263232534, 24003652237, true⟩ ⟨3554348114, 4324076262, true⟩
    ⟨141537543721, 160348228579, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [64, 72]`. -/
theorem oscF_15_30_64_72 : finalOk
    ⟨-8997263418, 20605258721, true⟩ ⟨-34077851430, -7173463077, true⟩
    ⟨-55168615497, 27991134046, true⟩ ⟨-57263232534, 24003652237, true⟩
    ⟨3554348114, 4324076262, true⟩ ⟨121865825670, 141278617032, true⟩
    ⟨141537543721, 160348228579, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [64, 72]` is a leaf of the cover. -/
theorem oscLeaf_15_30_64_72 : OscLeaf 40 59 72 3086000000 4502000000 15 30 64 72 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_64_72, oscB_15_30_64_72, oscF_15_30_64_72⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [72, 80]`. -/
theorem oscA_15_30_72_80 : legAOk (PBI 15 30) (TBI 72 80) ⟨5055424637, 5151784986, true⟩
    ⟨-10038274021, 19016188751, true⟩ ⟨-33967769850, -6551256559, true⟩
    ⟨1821240421, 2252720480, true⟩ ⟨122842479526, 142172927458, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [72, 80]`. -/
theorem oscB_15_30_72_80 : legBOk (PBI 15 30) (TBI 72 80) ⟨5055424637, 5151784986, true⟩
    ⟨1821240421, 2252720480, true⟩ ⟨-56203493346, 26353015513, true⟩
    ⟨-56860132471, 25040318415, true⟩ ⟨3552396501, 4319499398, true⟩
    ⟨141964184735, 160634525098, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [72, 80]`. -/
theorem oscF_15_30_72_80 : finalOk
    ⟨-10038274021, 19016188751, true⟩ ⟨-33967769850, -6551256559, true⟩
    ⟨-56203493346, 26353015513, true⟩ ⟨-56860132471, 25040318415, true⟩
    ⟨3552396501, 4319499398, true⟩ ⟨122842479526, 142172927458, true⟩
    ⟨141964184735, 160634525098, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [72, 80]` is a leaf of the cover. -/
theorem oscLeaf_15_30_72_80 : OscLeaf 40 59 72 3086000000 4502000000 15 30 72 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_72_80, oscB_15_30_72_80, oscF_15_30_72_80⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [80, 88]`. -/
theorem oscA_15_30_80_88 : legAOk (PBI 15 30) (TBI 80 88) ⟨5115861897, 5210680448, true⟩
    ⟨-10097902640, 15793817437, true⟩ ⟨-31691323929, -6380546080, true⟩
    ⟨1827262752, 2205389717, true⟩ ⟨123881976789, 140212343705, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [80, 88]`. -/
theorem oscB_15_30_80_88 : legBOk (PBI 15 30) (TBI 80 88) ⟨5115861897, 5210680448, true⟩
    ⟨1827262752, 2205389717, true⟩ ⟨-55468424731, 21814813052, true⟩
    ⟨-53925626675, 24578233684, true⟩ ⟨3551564171, 4263792844, true⟩
    ⟨142404869383, 161005582744, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [80, 88]`. -/
theorem oscF_15_30_80_88 : finalOk
    ⟨-10097902640, 15793817437, true⟩ ⟨-31691323929, -6380546080, true⟩
    ⟨-55468424731, 21814813052, true⟩ ⟨-53925626675, 24578233684, true⟩
    ⟨3551564171, 4263792844, true⟩ ⟨123881976789, 140212343705, true⟩
    ⟨142404869383, 161005582744, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [80, 88]` is a leaf of the cover. -/
theorem oscLeaf_15_30_80_88 : OscLeaf 40 59 72 3086000000 4502000000 15 30 80 88 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_80_88, oscB_15_30_80_88, oscF_15_30_80_88⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [88, 96]`. -/
theorem oscA_15_30_88_96 : legAOk (PBI 15 30) (TBI 88 96) ⟨5175778371, 5269098227, true⟩
    ⟨-11614799846, 14836420604, true⟩ ⟨-31492462005, -3890628909, true⟩
    ⟨1789228173, 2213888465, true⟩ ⟨122310779677, 141297903790, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [88, 96]`. -/
theorem oscB_15_30_88_96 : legBOk (PBI 15 30) (TBI 88 96) ⟨5175778371, 5269098227, true⟩
    ⟨1789228173, 2213888465, true⟩ ⟨-59238440230, 22626438283, true⟩
    ⟨-55560585849, 29573179715, true⟩ ⟨3479564521, 4264835194, true⟩
    ⟨140877929503, 161438249208, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [88, 96]`. -/
theorem oscF_15_30_88_96 : finalOk
    ⟨-11614799846, 14836420604, true⟩ ⟨-31492462005, -3890628909, true⟩
    ⟨-59238440230, 22626438283, true⟩ ⟨-55560585849, 29573179715, true⟩
    ⟨3479564521, 4264835194, true⟩ ⟨122310779677, 141297903790, true⟩
    ⟨140877929503, 161438249208, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[15, 30] × [88, 96]` is a leaf of the cover. -/
theorem oscLeaf_15_30_88_96 : OscLeaf 40 59 72 3086000000 4502000000 15 30 88 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_88_96, oscB_15_30_88_96, oscF_15_30_88_96⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
