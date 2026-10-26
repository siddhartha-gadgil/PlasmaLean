/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 4

Leaves 24–31 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[15, 30] × [4, 8]`. -/
theorem oscA_15_30_4_8 : legAOk (PBI 15 30) (TBI 4 8) ⟨4517083570, 4596476722, true⟩
    ⟨7263282051, 31276035772, true⟩ ⟨-28674236537, -6756565045, true⟩
    ⟨1887021880, 2236767238, true⟩ ⟨120967042930, 136318537349, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [4, 8]`. -/
theorem oscB_15_30_4_8 : legBOk (PBI 15 30) (TBI 4 8) ⟨4517083570, 4596476722, true⟩
    ⟨1887021880, 2236767238, true⟩ ⟨-35925146459, 35033773702, true⟩
    ⟨-49348448092, 19885239051, true⟩ ⟨3735438264, 4411686502, true⟩
    ⟨142013583135, 159936375411, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [4, 8]`. -/
theorem oscF_15_30_4_8 : finalOk
    ⟨7263282051, 31276035772, true⟩ ⟨-28674236537, -6756565045, true⟩
    ⟨-35925146459, 35033773702, true⟩ ⟨-49348448092, 19885239051, true⟩
    ⟨3735438264, 4411686502, true⟩ ⟨120967042930, 136318537349, true⟩
    ⟨142013583135, 159936375411, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [4, 8]` is a leaf of the cover. -/
theorem oscLeaf_15_30_4_8 : OscLeaf 40 59 72 3086000000 4502000000 15 30 4 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_4_8, oscB_15_30_4_8, oscF_15_30_4_8⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [8, 12]`. -/
theorem oscA_15_30_8_12 : legAOk (PBI 15 30) (TBI 8 12) ⟨4550147042, 4628696359, true⟩
    ⟨5403723092, 31586416048, true⟩ ⟨-29945945880, -6484780839, true⟩
    ⟨1867572680, 2264206340, true⟩ ⟨120108442246, 138171578758, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [8, 12]`. -/
theorem oscB_15_30_8_12 : legBOk (PBI 15 30) (TBI 8 12) ⟨4550147042, 4628696359, true⟩
    ⟨1867572680, 2264206340, true⟩ ⟨-38994222832, 37491661096, true⟩
    ⟨-51280353958, 21520798439, true⟩ ⟨3723705195, 4448009602, true⟩
    ⟨143035557207, 161037726629, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [8, 12]`. -/
theorem oscF_15_30_8_12 : finalOk
    ⟨5403723092, 31586416048, true⟩ ⟨-29945945880, -6484780839, true⟩
    ⟨-38994222832, 37491661096, true⟩ ⟨-51280353958, 21520798439, true⟩
    ⟨3723705195, 4448009602, true⟩ ⟨120108442246, 138171578758, true⟩
    ⟨143035557207, 161037726629, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [8, 12]` is a leaf of the cover. -/
theorem oscLeaf_15_30_8_12 : OscLeaf 40 59 72 3086000000 4502000000 15 30 8 12 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_8_12, oscB_15_30_8_12, oscF_15_30_8_12⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [12, 16]`. -/
theorem oscA_15_30_12_16 : legAOk (PBI 15 30) (TBI 12 16) ⟨4583015085, 4660735006, true⟩
    ⟨5624474036, 29962435754, true⟩ ⟨-29540940808, -8407151200, true⟩
    ⟨1889580015, 2238279982, true⟩ ⟨121731103762, 136981020548, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [12, 16]`. -/
theorem oscB_15_30_12_16 : legBOk (PBI 15 30) (TBI 12 16) ⟨4583015085, 4660735006, true⟩
    ⟨1889580015, 2238279982, true⟩ ⟨-37282458457, 33951003832, true⟩
    ⟨-50188097275, 18268920341, true⟩ ⟨3725663423, 4399041787, true⟩
    ⟨142066609788, 159924246519, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [12, 16]`. -/
theorem oscF_15_30_12_16 : finalOk
    ⟨5624474036, 29962435754, true⟩ ⟨-29540940808, -8407151200, true⟩
    ⟨-37282458457, 33951003832, true⟩ ⟨-50188097275, 18268920341, true⟩
    ⟨3725663423, 4399041787, true⟩ ⟨121731103762, 136981020548, true⟩
    ⟨142066609788, 159924246519, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [12, 16]` is a leaf of the cover. -/
theorem oscLeaf_15_30_12_16 : OscLeaf 40 59 72 3086000000 4502000000 15 30 12 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_12_16, oscB_15_30_12_16, oscF_15_30_12_16⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [16, 20]`. -/
theorem oscA_15_30_16_20 : legAOk (PBI 15 30) (TBI 16 20) ⟨4615692354, 4692596826, true⟩
    ⟨3687129572, 30249459288, true⟩ ⟨-30821761996, -7942690679, true⟩
    ⟨1868183480, 2264840099, true⟩ ⟨120742878600, 138749044512, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [16, 20]`. -/
theorem oscB_15_30_16_20 : legBOk (PBI 15 30) (TBI 16 20) ⟨4615692354, 4692596826, true⟩
    ⟨1868183480, 2264840099, true⟩ ⟨-40604395670, 36568733459, true⟩
    ⟨-52206676911, 20280730920, true⟩ ⟨3712000610, 4437181727, true⟩
    ⟨143098243630, 161195891903, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [16, 20]`. -/
theorem oscF_15_30_16_20 : finalOk
    ⟨3687129572, 30249459288, true⟩ ⟨-30821761996, -7942690679, true⟩
    ⟨-40604395670, 36568733459, true⟩ ⟨-52206676911, 20280730920, true⟩
    ⟨3712000610, 4437181727, true⟩ ⟨120742878600, 138749044512, true⟩
    ⟨143098243630, 161195891903, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [16, 20]` is a leaf of the cover. -/
theorem oscLeaf_15_30_16_20 : OscLeaf 40 59 72 3086000000 4502000000 15 30 16 20 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_16_20, oscB_15_30_16_20, oscF_15_30_16_20⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [20, 24]`. -/
theorem oscA_15_30_20_24 : legAOk (PBI 15 30) (TBI 20 24) ⟨4648183341, 4724285854, true⟩
    ⟨2384778007, 28903367272, true⟩ ⟨-30864278818, -8540988748, true⟩
    ⟨1847323092, 2241957689, true⟩ ⟨119788770106, 137729787330, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [20, 24]`. -/
theorem oscB_15_30_20_24 : legBOk (PBI 15 30) (TBI 20 24) ⟨4648183341, 4724285854, true⟩
    ⟨1847323092, 2241957689, true⟩ ⟨-41185666758, 34524673566, true⟩
    ⟨-52473113405, 19254492048, true⟩ ⟨3673418455, 4390518390, true⟩
    ⟨142278240218, 160047698789, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [20, 24]`. -/
theorem oscF_15_30_20_24 : finalOk
    ⟨2384778007, 28903367272, true⟩ ⟨-30864278818, -8540988748, true⟩
    ⟨-41185666758, 34524673566, true⟩ ⟨-52473113405, 19254492048, true⟩
    ⟨3673418455, 4390518390, true⟩ ⟨119788770106, 137729787330, true⟩
    ⟨142278240218, 160047698789, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [20, 24]` is a leaf of the cover. -/
theorem oscLeaf_15_30_20_24 : OscLeaf 40 59 72 3086000000 4502000000 15 30 20 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_20_24, oscB_15_30_20_24, oscF_15_30_20_24⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [24, 28]`. -/
theorem oscA_15_30_24_28 : legAOk (PBI 15 30) (TBI 24 28) ⟨4680492404, 4755806000, true⟩
    ⟨2597903786, 27104453773, true⟩ ⟨-30343930297, -10045211847, true⟩
    ⟨1871097212, 2215413008, true⟩ ⟨121537428984, 136552497013, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [24, 28]`. -/
theorem oscB_15_30_24_28 : legBOk (PBI 15 30) (TBI 24 28) ⟨4680492404, 4755806000, true⟩
    ⟨1871097212, 2215413008, true⟩ ⟨-40077388655, 32250273478, true⟩
    ⟨-50838587206, 17451126201, true⟩ ⟨3704723193, 4372016410, true⟩
    ⟨143297431973, 161075483498, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [24, 28]`. -/
theorem oscF_15_30_24_28 : finalOk
    ⟨2597903786, 27104453773, true⟩ ⟨-30343930297, -10045211847, true⟩
    ⟨-40077388655, 32250273478, true⟩ ⟨-50838587206, 17451126201, true⟩
    ⟨3704723193, 4372016410, true⟩ ⟨121537428984, 136552497013, true⟩
    ⟨143297431973, 161075483498, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [24, 28]` is a leaf of the cover. -/
theorem oscLeaf_15_30_24_28 : OscLeaf 40 59 72 3086000000 4502000000 15 30 24 28 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_24_28, oscB_15_30_24_28, oscF_15_30_24_28⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [28, 32]`. -/
theorem oscA_15_30_28_32 : legAOk (PBI 15 30) (TBI 28 32) ⟨4712623756, 4787161062, true⟩
    ⟨601935872, 27401528825, true⟩ ⟨-31644332972, -9293779651, true⟩
    ⟨1849268116, 2244218272, true⟩ ⟨120536944612, 138428310292, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [28, 32]`. -/
theorem oscB_15_30_28_32 : legBOk (PBI 15 30) (TBI 28 32) ⟨4712623756, 4787161062, true⟩
    ⟨1849268116, 2244218272, true⟩ ⟨-42869403176, 33157957367, true⟩
    ⟨-53045896228, 18601333036, true⟩ ⟨3664275834, 4378891921, true⟩
    ⟨142420293963, 160045796649, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [28, 32]`. -/
theorem oscF_15_30_28_32 : finalOk
    ⟨601935872, 27401528825, true⟩ ⟨-31644332972, -9293779651, true⟩
    ⟨-42869403176, 33157957367, true⟩ ⟨-53045896228, 18601333036, true⟩
    ⟨3664275834, 4378891921, true⟩ ⟨120536944612, 138428310292, true⟩
    ⟨142420293963, 160045796649, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [28, 32]` is a leaf of the cover. -/
theorem oscLeaf_15_30_28_32 : OscLeaf 40 59 72 3086000000 4502000000 15 30 28 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_28_32, oscB_15_30_28_32, oscF_15_30_28_32⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [32, 36]`. -/
theorem oscA_15_30_32_36 : legAOk (PBI 15 30) (TBI 32 36) ⟨4744581475, 4818354715, true⟩
    ⟨806482150, 25596513355, true⟩ ⟨-31139664133, -10633040102, true⟩
    ⟨1872380975, 2218011671, true⟩ ⟨122235940340, 137255817649, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [32, 36]`. -/
theorem oscB_15_30_32_36 : legBOk (PBI 15 30) (TBI 32 36) ⟨4744581475, 4818354715, true⟩
    ⟨1872380975, 2218011671, true⟩ ⟨-40761048303, 28344365182, true⟩
    ⟨-50415327251, 14811192778, true⟩ ⟨3697337402, 4328496651, true⟩
    ⟨143610735363, 158855603398, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [32, 36]`. -/
theorem oscF_15_30_32_36 : finalOk
    ⟨806482150, 25596513355, true⟩ ⟨-31139664133, -10633040102, true⟩
    ⟨-40761048303, 28344365182, true⟩ ⟨-50415327251, 14811192778, true⟩
    ⟨3697337402, 4328496651, true⟩ ⟨122235940340, 137255817649, true⟩
    ⟨143610735363, 158855603398, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [32, 36]` is a leaf of the cover. -/
theorem oscLeaf_15_30_32_36 : OscLeaf 40 59 72 3086000000 4502000000 15 30 32 36 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_32_36, oscB_15_30_32_36, oscF_15_30_32_36⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
