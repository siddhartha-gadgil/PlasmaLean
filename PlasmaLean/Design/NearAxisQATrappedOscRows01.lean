/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 1

Leaves 0–7 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[0, 7] × [0, 4]`. -/
theorem oscA_0_7_0_4 : legAOk (PBI 0 7) (TBI 0 4) ⟨4434093233, 4491241253, true⟩
    ⟨11542907674, 29858705710, true⟩ ⟨-24088436074, -5425848162, true⟩
    ⟨1951551564, 2244768546, true⟩ ⟨121448026856, 134706579975, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 7] × [0, 4]`. -/
theorem oscB_0_7_0_4 : legBOk (PBI 0 7) (TBI 0 4) ⟨4434093233, 4491241253, true⟩
    ⟨1951551564, 2244768546, true⟩ ⟨-26633426543, 29757221062, true⟩
    ⟨-41011660294, 15234226288, true⟩ ⟨3893098347, 4448690253, true⟩
    ⟨145285978081, 159605339222, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 7] × [0, 4]`. -/
theorem oscF_0_7_0_4 : finalOk
    ⟨11542907674, 29858705710, true⟩ ⟨-24088436074, -5425848162, true⟩
    ⟨-26633426543, 29757221062, true⟩ ⟨-41011660294, 15234226288, true⟩
    ⟨3893098347, 4448690253, true⟩ ⟨121448026856, 134706579975, true⟩
    ⟨145285978081, 159605339222, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 7] × [0, 4]` is a leaf of the cover. -/
theorem oscLeaf_0_7_0_4 : OscLeaf 40 59 72 3086000000 4502000000 0 7 0 4 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_7_0_4, oscB_0_7_0_4, oscF_0_7_0_4⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[7, 15] × [0, 4]`. -/
theorem oscA_7_15_0_4 : legAOk (PBI 7 15) (TBI 0 4) ⟨4457571259, 4517116383, true⟩
    ⟨11193278112, 30530301314, true⟩ ⟨-25361777403, -5979416030, true⟩
    ⟨1951501420, 2251997506, true⟩ ⟨122482599863, 136045313093, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[7, 15] × [0, 4]`. -/
theorem oscB_7_15_0_4 : legBOk (PBI 7 15) (TBI 0 4) ⟨4457571259, 4517116383, true⟩
    ⟨1951501420, 2251997506, true⟩ ⟨-28933686058, 31465498819, true⟩
    ⟨-43382409093, 16915099621, true⟩ ⟨3857120660, 4452735044, true⟩
    ⟨143745818726, 160300670908, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[7, 15] × [0, 4]`. -/
theorem oscF_7_15_0_4 : finalOk
    ⟨11193278112, 30530301314, true⟩ ⟨-25361777403, -5979416030, true⟩
    ⟨-28933686058, 31465498819, true⟩ ⟨-43382409093, 16915099621, true⟩
    ⟨3857120660, 4452735044, true⟩ ⟨122482599863, 136045313093, true⟩
    ⟨143745818726, 160300670908, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[7, 15] × [0, 4]` is a leaf of the cover. -/
theorem oscLeaf_7_15_0_4 : OscLeaf 40 59 72 3086000000 4502000000 7 15 0 4 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_7_15_0_4, oscB_7_15_0_4, oscF_7_15_0_4⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [4, 8]`. -/
theorem oscA_0_15_4_8 : legAOk (PBI 0 15) (TBI 4 8) ⟨4468067359, 4550179853, true⟩
    ⟨7104344288, 32167446389, true⟩ ⟨-27780873072, -3649979066, true⟩
    ⟨1878776087, 2282480590, true⟩ ⟨118629637481, 136833611361, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [4, 8]`. -/
theorem oscB_0_15_4_8 : legBOk (PBI 0 15) (TBI 4 8) ⟨4468067359, 4550179853, true⟩
    ⟨1878776087, 2282480590, true⟩ ⟨-36080467062, 37749523003, true⟩
    ⟨-49091490353, 22080355151, true⟩ ⟨3787014819, 4501739608, true⟩
    ⟨144551041159, 160974278699, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [4, 8]`. -/
theorem oscF_0_15_4_8 : finalOk
    ⟨7104344288, 32167446389, true⟩ ⟨-27780873072, -3649979066, true⟩
    ⟨-36080467062, 37749523003, true⟩ ⟨-49091490353, 22080355151, true⟩
    ⟨3787014819, 4501739608, true⟩ ⟨118629637481, 136833611361, true⟩
    ⟨144551041159, 160974278699, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [4, 8]` is a leaf of the cover. -/
theorem oscLeaf_0_15_4_8 : OscLeaf 40 59 72 3086000000 4502000000 0 15 4 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_4_8, oscB_0_15_4_8, oscF_0_15_4_8⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 7] × [8, 12]`. -/
theorem oscA_0_7_8_12 : legAOk (PBI 0 7) (TBI 8 12) ⟨4501829670, 4557901830, true⟩
    ⟨10152329650, 28895382956, true⟩ ⟨-25190829826, -7260710579, true⟩
    ⟨1951975671, 2245812096, true⟩ ⟨122089350945, 135328961188, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 7] × [8, 12]`. -/
theorem oscB_0_7_8_12 : legBOk (PBI 0 7) (TBI 8 12) ⟨4501829670, 4557901830, true⟩
    ⟨1951975671, 2245812096, true⟩ ⟨-27615029715, 28910146630, true⟩
    ⟨-42077993601, 13234165202, true⟩ ⟨3881846218, 4432184195, true⟩
    ⟨145439542579, 159394441734, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 7] × [8, 12]`. -/
theorem oscF_0_7_8_12 : finalOk
    ⟨10152329650, 28895382956, true⟩ ⟨-25190829826, -7260710579, true⟩
    ⟨-27615029715, 28910146630, true⟩ ⟨-42077993601, 13234165202, true⟩
    ⟨3881846218, 4432184195, true⟩ ⟨122089350945, 135328961188, true⟩
    ⟨145439542579, 159394441734, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 7] × [8, 12]` is a leaf of the cover. -/
theorem oscLeaf_0_7_8_12 : OscLeaf 40 59 72 3086000000 4502000000 0 7 8 12 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_7_8_12, oscB_0_7_8_12, oscF_0_7_8_12⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[7, 15] × [8, 12]`. -/
theorem oscA_7_15_8_12 : legAOk (PBI 7 15) (TBI 8 12) ⟨4524639348, 4583047898, true⟩
    ⟨8331416144, 29764328387, true⟩ ⟨-26984667268, -7019896537, true⟩
    ⟨1908921246, 2252869844, true⟩ ⟨120544428722, 136650798767, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[7, 15] × [8, 12]`. -/
theorem oscB_7_15_8_12 : legBOk (PBI 7 15) (TBI 8 12) ⟨4524639348, 4583047898, true⟩
    ⟨1908921246, 2252869844, true⟩ ⟨-32090047553, 32234200833, true⟩
    ⟨-45945242601, 16776376613, true⟩ ⟨3803633045, 4437538667, true⟩
    ⟨143922780035, 160181976147, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[7, 15] × [8, 12]`. -/
theorem oscF_7_15_8_12 : finalOk
    ⟨8331416144, 29764328387, true⟩ ⟨-26984667268, -7019896537, true⟩
    ⟨-32090047553, 32234200833, true⟩ ⟨-45945242601, 16776376613, true⟩
    ⟨3803633045, 4437538667, true⟩ ⟨120544428722, 136650798767, true⟩
    ⟨143922780035, 160181976147, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[7, 15] × [8, 12]` is a leaf of the cover. -/
theorem oscLeaf_7_15_8_12 : OscLeaf 40 59 72 3086000000 4502000000 7 15 8 12 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_7_15_8_12, oscB_7_15_8_12, oscF_7_15_8_12⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [12, 16]`. -/
theorem oscA_0_15_12_16 : legAOk (PBI 0 15) (TBI 12 16) ⟨4535385389, 4615725166, true⟩
    ⟨5550491279, 31071691529, true⟩ ⟨-28686141220, -5533044624, true⟩
    ⟨1879622083, 2283425560, true⟩ ⟨119296330551, 137455199857, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [12, 16]`. -/
theorem oscB_0_15_12_16 : legBOk (PBI 0 15) (TBI 12 16) ⟨4535385389, 4615725166, true⟩
    ⟨1879622083, 2283425560, true⟩ ⟨-37823404861, 37355326405, true⟩
    ⟨-51053175991, 20940698497, true⟩ ⟨3748578519, 4485427903, true⟩
    ⟨142704871256, 160788778178, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [12, 16]`. -/
theorem oscF_0_15_12_16 : finalOk
    ⟨5550491279, 31071691529, true⟩ ⟨-28686141220, -5533044624, true⟩
    ⟨-37823404861, 37355326405, true⟩ ⟨-51053175991, 20940698497, true⟩
    ⟨3748578519, 4485427903, true⟩ ⟨119296330551, 137455199857, true⟩
    ⟨142704871256, 160788778178, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [12, 16]` is a leaf of the cover. -/
theorem oscLeaf_0_15_12_16 : OscLeaf 40 59 72 3086000000 4502000000 0 15 12 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_12_16, oscB_0_15_12_16, oscF_0_15_12_16⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [16, 20]`. -/
theorem oscA_0_15_16_20 : legAOk (PBI 0 15) (TBI 16 20) ⟨4568739561, 4648216154, true⟩
    ⟨5717556911, 29512759323, true⟩ ⟨-28286865783, -7510526447, true⟩
    ⟨1900767831, 2256896246, true⟩ ⟨120893091708, 136246223357, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [16, 20]`. -/
theorem oscB_0_15_16_20 : legBOk (PBI 0 15) (TBI 16 20) ⟨4568739561, 4648216154, true⟩
    ⟨1900767831, 2256896246, true⟩ ⟨-37011583535, 35538342105, true⟩
    ⟨-49729603050, 18974708029, true⟩ ⟨3776374606, 4469726528, true⟩
    ⟨143663837676, 162024532777, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [16, 20]`. -/
theorem oscF_0_15_16_20 : finalOk
    ⟨5717556911, 29512759323, true⟩ ⟨-28286865783, -7510526447, true⟩
    ⟨-37011583535, 35538342105, true⟩ ⟨-49729603050, 18974708029, true⟩
    ⟨3776374606, 4469726528, true⟩ ⟨120893091708, 136246223357, true⟩
    ⟨143663837676, 162024532777, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [16, 20]` is a leaf of the cover. -/
theorem oscLeaf_0_15_16_20 : OscLeaf 40 59 72 3086000000 4502000000 0 15 16 20 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_16_20, oscB_0_15_16_20, oscF_0_15_16_20⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[0, 15] × [20, 24]`. -/
theorem oscA_0_15_20_24 : legAOk (PBI 0 15) (TBI 20 24) ⟨4601897061, 4680525216, true⟩
    ⟨3886513218, 29829757920, true⟩ ⟨-29552746791, -7111433442, true⟩
    ⟨1880264101, 2285111035, true⟩ ⟨119968252165, 138109865901, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[0, 15] × [20, 24]`. -/
theorem oscB_0_15_20_24 : legBOk (PBI 0 15) (TBI 20 24) ⟨4601897061, 4680525216, true⟩
    ⟨1880264101, 2285111035, true⟩ ⟨-39423430077, 36467884418, true⟩
    ⟨-51958779962, 19573261343, true⟩ ⟨3736054732, 4474066558, true⟩
    ⟨142731594287, 160881523902, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[0, 15] × [20, 24]`. -/
theorem oscF_0_15_20_24 : finalOk
    ⟨3886513218, 29829757920, true⟩ ⟨-29552746791, -7111433442, true⟩
    ⟨-39423430077, 36467884418, true⟩ ⟨-51958779962, 19573261343, true⟩
    ⟨3736054732, 4474066558, true⟩ ⟨119968252165, 138109865901, true⟩
    ⟨142731594287, 160881523902, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[0, 15] × [20, 24]` is a leaf of the cover. -/
theorem oscLeaf_0_15_20_24 : OscLeaf 40 59 72 3086000000 4502000000 0 15 20 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_0_15_20_24, oscB_0_15_20_24, oscF_0_15_20_24⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
