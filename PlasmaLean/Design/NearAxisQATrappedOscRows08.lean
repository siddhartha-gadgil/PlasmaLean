/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 8

Leaves 56–63 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[30, 45] × [80, 88]`. -/
theorem oscA_30_45_80_88 : legAOk (PBI 30 45) (TBI 80 88) ⟨5151752177, 5244261273, true⟩
    ⟨-10905002724, 14540484451, true⟩ ⟨-31648162716, -5839333559, true⟩
    ⟨1801878708, 2167153662, true⟩ ⟨123984654035, 139966191901, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [80, 88]`. -/
theorem oscB_30_45_80_88 : legBOk (PBI 30 45) (TBI 80 88) ⟨5151752177, 5244261273, true⟩
    ⟨1801878708, 2167153662, true⟩ ⟨-57663767632, 20200743296, true⟩
    ⟨-53625387688, 27172998492, true⟩ ⟨3477207854, 4195029562, true⟩
    ⟨140214262420, 160495281892, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [80, 88]`. -/
theorem oscF_30_45_80_88 : finalOk
    ⟨-10905002724, 14540484451, true⟩ ⟨-31648162716, -5839333559, true⟩
    ⟨-57663767632, 20200743296, true⟩ ⟨-53625387688, 27172998492, true⟩
    ⟨3477207854, 4195029562, true⟩ ⟨123984654035, 139966191901, true⟩
    ⟨140214262420, 160495281892, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [80, 88]` is a leaf of the cover. -/
theorem oscLeaf_30_45_80_88 : OscLeaf 40 59 72 3086000000 4502000000 30 45 80 88 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_80_88, oscB_30_45_80_88, oscF_30_45_80_88⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [88, 96]`. -/
theorem oscA_30_45_88_96 : legAOk (PBI 30 45) (TBI 88 96) ⟨5210647640, 5301726409, true⟩
    ⟨-12421536643, 13761056320, true⟩ ⟨-31350606376, -3141978574, true⟩
    ⟨1763427851, 2177721933, true⟩ ⟨122378643001, 141165024439, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [88, 96]`. -/
theorem oscB_30_45_88_96 : legBOk (PBI 30 45) (TBI 88 96) ⟨5210647640, 5301726409, true⟩
    ⟨1763427851, 2177721933, true⟩ ⟨-59940774154, 17909230770, true⟩
    ⟨-53505404570, 29412783841, true⟩ ⟨3432455823, 4166814369, true⟩
    ⟨140673694102, 158726513196, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [88, 96]`. -/
theorem oscF_30_45_88_96 : finalOk
    ⟨-12421536643, 13761056320, true⟩ ⟨-31350606376, -3141978574, true⟩
    ⟨-59940774154, 17909230770, true⟩ ⟨-53505404570, 29412783841, true⟩
    ⟨3432455823, 4166814369, true⟩ ⟨122378643001, 141165024439, true⟩
    ⟨140673694102, 158726513196, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [88, 96]` is a leaf of the cover. -/
theorem oscLeaf_30_45_88_96 : OscLeaf 40 59 72 3086000000 4502000000 30 45 88 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_88_96, oscB_30_45_88_96, oscF_30_45_88_96⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [96, 104]`. -/
theorem oscA_30_45_96_104 : legAOk (PBI 30 45) (TBI 96 104) ⟨5269065418, 5358751960, true⟩
    ⟨-13195612284, 12730188200, true⟩ ⟨-30537943292, -2028532015, true⟩
    ⟨1769733084, 2183768923, true⟩ ⟨123443627610, 142140407790, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [96, 104]`. -/
theorem oscB_30_45_96_104 : legBOk (PBI 30 45) (TBI 96 104) ⟨5269065418, 5358751960, true⟩
    ⟨1769733084, 2183768923, true⟩ ⟨-60756329291, 16950364685, true⟩
    ⟨-52645841649, 31125936059, true⟩ ⟨3432963783, 4165834807, true⟩
    ⟨141168767075, 159161029503, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [96, 104]`. -/
theorem oscF_30_45_96_104 : finalOk
    ⟨-13195612284, 12730188200, true⟩ ⟨-30537943292, -2028532015, true⟩
    ⟨-60756329291, 16950364685, true⟩ ⟨-52645841649, 31125936059, true⟩
    ⟨3432963783, 4165834807, true⟩ ⟨123443627610, 142140407790, true⟩
    ⟨141168767075, 159161029503, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [96, 104]` is a leaf of the cover. -/
theorem oscLeaf_30_45_96_104 : OscLeaf 40 59 72 3086000000 4502000000 30 45 96 104 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_96_104, oscB_30_45_96_104, oscF_30_45_96_104⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [104, 112]`. -/
theorem oscA_30_45_104_112 : legAOk (PBI 30 45) (TBI 104 112) ⟨5327024922, 5415355404, true⟩
    ⟨-13037587698, 10607764287, true⟩ ⟨-27482114597, -1172547979, true⟩
    ⟨1776441560, 2139313558, true⟩ ⟨124560138200, 140353577923, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [104, 112]`. -/
theorem oscB_30_45_104_112 : legBOk (PBI 30 45) (TBI 104 112) ⟨5327024922, 5415355404, true⟩
    ⟨1776441560, 2139313558, true⟩ ⟨-59848792276, 13829430242, true⟩
    ⟨-48979025337, 31162375669, true⟩ ⟨3434753613, 4114719043, true⟩
    ⟨141728393787, 159622944186, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [104, 112]`. -/
theorem oscF_30_45_104_112 : finalOk
    ⟨-13037587698, 10607764287, true⟩ ⟨-27482114597, -1172547979, true⟩
    ⟨-59848792276, 13829430242, true⟩ ⟨-48979025337, 31162375669, true⟩
    ⟨3434753613, 4114719043, true⟩ ⟨124560138200, 140353577923, true⟩
    ⟨141728393787, 159622944186, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [104, 112]` is a leaf of the cover. -/
theorem oscLeaf_30_45_104_112 : OscLeaf 40 59 72 3086000000 4502000000 30 45 104 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_104_112, oscB_30_45_104_112, oscF_30_45_104_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [112, 120]`. -/
theorem oscA_30_45_112_120 : legAOk (PBI 30 45) (TBI 112 120) ⟨5384544661, 5471553458, true⟩
    ⟨-14308066508, 11090584524, true⟩ ⟨-26900627108, 1775348394, true⟩
    ⟨1738843659, 2151615904, true⟩ ⟨123034067988, 141653044280, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [112, 120]`. -/
theorem oscB_30_45_112_120 : legBOk (PBI 30 45) (TBI 112 120) ⟨5384544661, 5471553458, true⟩
    ⟨1738843659, 2151615904, true⟩ ⟨-61665621485, 12932721985, true⟩
    ⟨-48377539052, 33877929597, true⟩ ⟨3392846044, 4090271234, true⟩
    ⟨142335843058, 157993649390, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [112, 120]`. -/
theorem oscF_30_45_112_120 : finalOk
    ⟨-14308066508, 11090584524, true⟩ ⟨-26900627108, 1775348394, true⟩
    ⟨-61665621485, 12932721985, true⟩ ⟨-48377539052, 33877929597, true⟩
    ⟨3392846044, 4090271234, true⟩ ⟨123034067988, 141653044280, true⟩
    ⟨142335843058, 157993649390, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [112, 120]` is a leaf of the cover. -/
theorem oscLeaf_30_45_112_120 : OscLeaf 40 59 72 3086000000 4502000000 30 45 112 120 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_112_120, oscB_30_45_112_120, oscF_30_45_112_120⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [120, 128]`. -/
theorem oscA_30_45_120_128 : legAOk (PBI 30 45) (TBI 120 128) ⟨5441642318, 5527362117, true⟩
    ⟨-14997619109, 10886420206, true⟩ ⟨-25778703839, 2896778333, true⟩
    ⟨1746657687, 2158021152, true⟩ ⟨124203841390, 142687488381, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [120, 128]`. -/
theorem oscB_30_45_120_128 : legBOk (PBI 30 45) (TBI 120 128) ⟨5441642318, 5527362117, true⟩
    ⟨1746657687, 2158021152, true⟩ ⟨-63433657685, 13554977617, true⟩
    ⟨-47671978294, 36386603366, true⟩ ⟨3370159418, 4090368262, true⟩
    ⟨141016572673, 158484224090, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [120, 128]`. -/
theorem oscF_30_45_120_128 : finalOk
    ⟨-14997619109, 10886420206, true⟩ ⟨-25778703839, 2896778333, true⟩
    ⟨-63433657685, 13554977617, true⟩ ⟨-47671978294, 36386603366, true⟩
    ⟨3370159418, 4090368262, true⟩ ⟨124203841390, 142687488381, true⟩
    ⟨141016572673, 158484224090, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [120, 128]` is a leaf of the cover. -/
theorem oscLeaf_30_45_120_128 : OscLeaf 40 59 72 3086000000 4502000000 30 45 120 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_120_128, oscB_30_45_120_128, oscF_30_45_120_128⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [0, 8]`. -/
theorem oscA_45_60_0_8 : legAOk (PBI 45 60) (TBI 0 8) ⟨4577122851, 4683588227, true⟩
    ⟨2001911269, 32142498935, true⟩ ⟨-32906267692, -7472746448, true⟩
    ⟨1782238225, 2185756150, true⟩ ⟨117994032292, 137034409747, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [0, 8]`. -/
theorem oscB_45_60_0_8 : legBOk (PBI 45 60) (TBI 0 8) ⟨4577122851, 4683588227, true⟩
    ⟨1782238225, 2185756150, true⟩ ⟨-45544024149, 38786290448, true⟩
    ⟨-55494262662, 25125146327, true⟩ ⟨3562565491, 4314374488, true⟩
    ⟨140345556340, 160045405906, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [0, 8]`. -/
theorem oscF_45_60_0_8 : finalOk
    ⟨2001911269, 32142498935, true⟩ ⟨-32906267692, -7472746448, true⟩
    ⟨-45544024149, 38786290448, true⟩ ⟨-55494262662, 25125146327, true⟩
    ⟨3562565491, 4314374488, true⟩ ⟨117994032292, 137034409747, true⟩
    ⟨140345556340, 160045405906, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[45, 60] × [0, 8]` is a leaf of the cover. -/
theorem oscLeaf_45_60_0_8 : OscLeaf 40 59 72 3086000000 4502000000 45 60 0 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_0_8, oscB_45_60_0_8, oscF_45_60_0_8⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[45, 60] × [8, 16]`. -/
theorem oscA_45_60_8_16 : legAOk (PBI 45 60) (TBI 8 16) ⟨4640868904, 4745477519, true⟩
    ⟨102742814, 30675598172, true⟩ ⟨-33689171902, -8288109757, true⟩
    ⟨1784018159, 2189849314, true⟩ ⟨118738756522, 137832563431, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[45, 60] × [8, 16]`. -/
theorem oscB_45_60_8_16 : legBOk (PBI 45 60) (TBI 8 16) ⟨4640868904, 4745477519, true⟩
    ⟨1784018159, 2189849314, true⟩ ⟨-47136847275, 37531998831, true⟩
    ⟨-56039871985, 24254199361, true⟩ ⟨3556711645, 4305593799, true⟩
    ⟨140668830270, 160057832949, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[45, 60] × [8, 16]`. -/
theorem oscF_45_60_8_16 : finalOk
    ⟨102742814, 30675598172, true⟩ ⟨-33689171902, -8288109757, true⟩
    ⟨-47136847275, 37531998831, true⟩ ⟨-56039871985, 24254199361, true⟩
    ⟨3556711645, 4305593799, true⟩ ⟨118738756522, 137832563431, true⟩
    ⟨140668830270, 160057832949, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[45, 60] × [8, 16]` is a leaf of the cover. -/
theorem oscLeaf_45_60_8_16 : OscLeaf 40 59 72 3086000000 4502000000 45 60 8 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_45_60_8_16, oscB_45_60_8_16, oscF_45_60_8_16⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
