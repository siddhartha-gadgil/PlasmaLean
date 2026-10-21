/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells

/-!
# Kernel checks of the oscillatory-kick cover, part 2

Leaves 8–15 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[0, 15] × [24, 28]`. -/
theorem oscA_0_15_24_28 : legAOk (PBI 0 15) (TBI 24 28) ⟨4634862596, 4712656564, true⟩
    ⟨4073330391, 28157427727, true⟩ ⟨-29092910657, -8782596629, true⟩
    ⟨1903079960, 2258425008, true⟩ ⟨121647756993, 136925060735, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [24, 28]`. -/
theorem oscB_0_15_24_28 : legBOk (PBI 0 15) (TBI 24 28) ⟨4634862596, 4712656564, true⟩
    ⟨1903079960, 2258425008, true⟩ ⟨-38461672134, 34401281626, true⟩
    ⟨-50512087062, 17724723677, true⟩ ⟨3766731036, 4457118096, true⟩
    ⟨143777598695, 162038790250, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [24, 28]`. -/
theorem oscF_0_15_24_28 : finalOk
    ⟨4073330391, 28157427727, true⟩ ⟨-29092910657, -8782596629, true⟩
    ⟨-38461672134, 34401281626, true⟩ ⟨-50512087062, 17724723677, true⟩
    ⟨3766731036, 4457118096, true⟩ ⟨121647756993, 136925060735, true⟩
    ⟨143777598695, 162038790250, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [24, 28]` is a leaf of the cover. -/
theorem oscLeaf_0_15_24_28 : OscLeaf 40 59 72 3086000000 4502000000 0 15 24 28 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_24_28, oscB_0_15_24_28, oscF_0_15_24_28⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [28, 32]`. -/
theorem oscA_0_15_28_32 : legAOk (PBI 0 15) (TBI 28 32) ⟨4667640728, 4744614285, true⟩
    ⟨2087242258, 28505217997, true⟩ ⟨-30400564063, -8129855201, true⟩
    ⟨1880281228, 2288549008, true⟩ ⟨120616555603, 138858422462, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [28, 32]`. -/
theorem oscB_0_15_28_32 : legBOk (PBI 0 15) (TBI 28 32) ⟨4667640728, 4744614285, true⟩
    ⟨1880281228, 2288549008, true⟩ ⟨-41056243608, 35366129925, true⟩
    ⟨-52736651789, 18670864401, true⟩ ⟨3726614970, 4463846038, true⟩
    ⟨143006020117, 160941628140, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [28, 32]`. -/
theorem oscF_0_15_28_32 : finalOk
    ⟨2087242258, 28505217997, true⟩ ⟨-30400564063, -8129855201, true⟩
    ⟨-41056243608, 35366129925, true⟩ ⟨-52736651789, 18670864401, true⟩
    ⟨3726614970, 4463846038, true⟩ ⟨120616555603, 138858422462, true⟩
    ⟨143006020117, 160941628140, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [28, 32]` is a leaf of the cover. -/
theorem oscLeaf_0_15_28_32 : OscLeaf 40 59 72 3086000000 4502000000 0 15 28 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_28_32, oscB_0_15_28_32, oscF_0_15_28_32⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [32, 36]`. -/
theorem oscA_0_15_32_36 : legAOk (PBI 0 15) (TBI 32 36) ⟨4700235864, 4776402338, true⟩
    ⟨2298493777, 26743454593, true⟩ ⟨-29913738383, -9631822243, true⟩
    ⟨1903819625, 2261481902, true⟩ ⟨122329668174, 137655720453, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [32, 36]`. -/
theorem oscB_0_15_32_36 : legBOk (PBI 0 15) (TBI 32 36) ⟨4700235864, 4776402338, true⟩
    ⟨1903819625, 2261481902, true⟩ ⟨-40011337245, 33111230593, true⟩
    ⟨-51146445108, 16935086118, true⟩ ⟨3758137738, 4445390402, true⟩
    ⟨144064838737, 162015960137, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [32, 36]`. -/
theorem oscF_0_15_32_36 : finalOk
    ⟨2298493777, 26743454593, true⟩ ⟨-29913738383, -9631822243, true⟩
    ⟨-40011337245, 33111230593, true⟩ ⟨-51146445108, 16935086118, true⟩
    ⟨3758137738, 4445390402, true⟩ ⟨122329668174, 137655720453, true⟩
    ⟨144064838737, 162015960137, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [32, 36]` is a leaf of the cover. -/
theorem oscLeaf_0_15_32_36 : OscLeaf 40 59 72 3086000000 4502000000 0 15 32 36 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_32_36, oscB_0_15_32_36, oscF_0_15_32_36⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [36, 40]`. -/
theorem oscA_0_15_36_40 : legAOk (PBI 0 15) (TBI 36 40) ⟨4732652280, 4808024559, true⟩
    ⟨432762226, 26950081939, true⟩ ⟨-31086217260, -8967389944, true⟩
    ⟨1884982527, 2288729027, true⟩ ⟨121511153894, 139484070078, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [36, 40]`. -/
theorem oscB_0_15_36_40 : legBOk (PBI 0 15) (TBI 36 40) ⟨4732652280, 4808024559, true⟩
    ⟨1884982527, 2288729027, true⟩ ⟨-42618965316, 33897722812, true⟩
    ⟨-53253282724, 17984464090, true⟩ ⟨3718844647, 4451411150, true⟩
    ⟨143086787800, 161054072315, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [36, 40]`. -/
theorem oscF_0_15_36_40 : finalOk
    ⟨432762226, 26950081939, true⟩ ⟨-31086217260, -8967389944, true⟩
    ⟨-42618965316, 33897722812, true⟩ ⟨-53253282724, 17984464090, true⟩
    ⟨3718844647, 4451411150, true⟩ ⟨121511153894, 139484070078, true⟩
    ⟨143086787800, 161054072315, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [36, 40]` is a leaf of the cover. -/
theorem oscLeaf_0_15_36_40 : OscLeaf 40 59 72 3086000000 4502000000 0 15 36 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_36_40, oscB_0_15_36_40, oscF_0_15_36_40⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [40, 48]`. -/
theorem oscA_0_15_40_48 : legAOk (PBI 0 15) (TBI 40 48) ⟨4764894113, 4870786292, true⟩
    ⟨-1773685195, 26129621663, true⟩ ⟨-31588787676, -8715713993, true⟩
    ⟨1880352155, 2272860431, true⟩ ⟨121950565582, 138870529828, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [40, 48]`. -/
theorem oscB_0_15_40_48 : legBOk (PBI 0 15) (TBI 40 48) ⟨4764894113, 4870786292, true⟩
    ⟨1880352155, 2272860431, true⟩ ⟨-46658232099, 35344186094, true⟩
    ⟨-55339485254, 20355046001, true⟩ ⟨3697711739, 4451230675, true⟩
    ⟨142855014811, 162649610733, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [40, 48]`. -/
theorem oscF_0_15_40_48 : finalOk
    ⟨-1773685195, 26129621663, true⟩ ⟨-31588787676, -8715713993, true⟩
    ⟨-46658232099, 35344186094, true⟩ ⟨-55339485254, 20355046001, true⟩
    ⟨3697711739, 4451230675, true⟩ ⟨121950565582, 138870529828, true⟩
    ⟨142855014811, 162649610733, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_0_15_40_48 : OscLeaf 40 59 72 3086000000 4502000000 0 15 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_40_48, oscB_0_15_40_48, oscF_0_15_40_48⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [48, 56]`. -/
theorem oscA_0_15_48_56 : legAOk (PBI 0 15) (TBI 48 56) ⟨4828869945, 4932927995, true⟩
    ⟨-4745511069, 24923801453, true⟩ ⟨-32619623623, -7754679123, true⟩
    ⟨1839561248, 2278037482, true⟩ ⟨120162498530, 139735300256, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [48, 56]`. -/
theorem oscB_0_15_48_56 : legBOk (PBI 0 15) (TBI 48 56) ⟨4828869945, 4932927995, true⟩
    ⟨1839561248, 2278037482, true⟩ ⟨-50651224803, 35516435656, true⟩
    ⟨-57216106329, 22625682725, true⟩ ⟨3648059206, 4445118502, true⟩
    ⟨143181113380, 162855380180, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [48, 56]`. -/
theorem oscF_0_15_48_56 : finalOk
    ⟨-4745511069, 24923801453, true⟩ ⟨-32619623623, -7754679123, true⟩
    ⟨-50651224803, 35516435656, true⟩ ⟨-57216106329, 22625682725, true⟩
    ⟨3648059206, 4445118502, true⟩ ⟨120162498530, 139735300256, true⟩
    ⟨143181113380, 162855380180, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [48, 56]` is a leaf of the cover. -/
theorem oscLeaf_0_15_48_56 : OscLeaf 40 59 72 3086000000 4502000000 0 15 48 56 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_48_56, oscB_0_15_48_56, oscF_0_15_48_56⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [56, 64]`. -/
theorem oscA_0_15_56_64 : legAOk (PBI 0 15) (TBI 56 64) ⟨4892194019, 4994476572, true⟩
    ⟨-6305071668, 23339451972, true⟩ ⟨-33127098696, -7681756003, true⟩
    ⟨1843624239, 2281400752, true⟩ ⟨121069290879, 140541817927, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [56, 64]`. -/
theorem oscB_0_15_56_64 : legBOk (PBI 0 15) (TBI 56 64) ⟨4892194019, 4994476572, true⟩
    ⟨1843624239, 2281400752, true⟩ ⟨-52836541875, 34705985235, true⟩
    ⟨-58405283623, 23914470759, true⟩ ⟨3615720824, 4438923169, true⟩
    ⟨141516319117, 163185962584, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [56, 64]`. -/
theorem oscF_0_15_56_64 : finalOk
    ⟨-6305071668, 23339451972, true⟩ ⟨-33127098696, -7681756003, true⟩
    ⟨-52836541875, 34705985235, true⟩ ⟨-58405283623, 23914470759, true⟩
    ⟨3615720824, 4438923169, true⟩ ⟨121069290879, 140541817927, true⟩
    ⟨141516319117, 163185962584, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [56, 64]` is a leaf of the cover. -/
theorem oscLeaf_0_15_56_64 : OscLeaf 40 59 72 3086000000 4502000000 0 15 56 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_56_64, oscB_0_15_56_64, oscF_0_15_56_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [64, 72]`. -/
theorem oscA_0_15_64_72 : legAOk (PBI 0 15) (TBI 64 72) ⟨4954895220, 5055457447, true⟩
    ⟨-7932299059, 21913228549, true⟩ ⟨-33496233511, -7219468707, true⟩
    ⟨1844836981, 2290094676, true⟩ ⟨121862982690, 141614885955, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [64, 72]`. -/
theorem oscB_0_15_64_72 : legBOk (PBI 0 15) (TBI 64 72) ⟨4954895220, 5055457447, true⟩
    ⟨1844836981, 2290094676, true⟩ ⟨-53636009572, 30508797529, true⟩
    ⟨-57651661105, 22615022222, true⟩ ⟨3608793226, 4400817995, true⟩
    ⟨141895396368, 160968784741, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [64, 72]`. -/
theorem oscF_0_15_64_72 : finalOk
    ⟨-7932299059, 21913228549, true⟩ ⟨-33496233511, -7219468707, true⟩
    ⟨-53636009572, 30508797529, true⟩ ⟨-57651661105, 22615022222, true⟩
    ⟨3608793226, 4400817995, true⟩ ⟨121862982690, 141614885955, true⟩
    ⟨141895396368, 160968784741, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[0, 15] × [64, 72]` is a leaf of the cover. -/
theorem oscLeaf_0_15_64_72 : OscLeaf 40 59 72 3086000000 4502000000 0 15 64 72 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_64_72, oscB_0_15_64_72, oscF_0_15_64_72⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
