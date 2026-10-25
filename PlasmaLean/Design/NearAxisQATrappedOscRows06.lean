/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 6

Leaves 40–47 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[15, 30] × [96, 104]`. -/
theorem oscA_15_30_96_104 : legAOk (PBI 15 30) (TBI 96 104) ⟨5235195743, 5327057730, true⟩
    ⟨-12462891617, 13563068458, true⟩ ⟨-30866976193, -2787361433, true⟩
    ⟨1794048358, 2222014565, true⟩ ⟨123317955510, 142390342783, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [96, 104]`. -/
theorem oscB_15_30_96_104 : legBOk (PBI 15 30) (TBI 96 104) ⟨5235195743, 5327057730, true⟩
    ⟨1794048358, 2222014565, true⟩ ⟨-59487049231, 18665077086, true⟩
    ⟨-53681691694, 29044053096, true⟩ ⟨3479514560, 4231931417, true⟩
    ⟨141459075704, 159564664154, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [96, 104]`. -/
theorem oscF_15_30_96_104 : finalOk
    ⟨-12462891617, 13563068458, true⟩ ⟨-30866976193, -2787361433, true⟩
    ⟨-59487049231, 18665077086, true⟩ ⟨-53681691694, 29044053096, true⟩
    ⟨3479514560, 4231931417, true⟩ ⟨123317955510, 142390342783, true⟩
    ⟨141459075704, 159564664154, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [96, 104]` is a leaf of the cover. -/
theorem oscLeaf_15_30_96_104 : OscLeaf 40 59 72 3086000000 4502000000 15 30 96 104 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_96_104, oscB_15_30_96_104, oscF_15_30_96_104⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [104, 112]`. -/
theorem oscA_15_30_104_112 : legAOk (PBI 15 30) (TBI 104 112) ⟨5294134645, 5384577470, true⟩
    ⟨-13245082872, 12621217746, true⟩ ⟨-30033827303, -1683391128, true⟩
    ⟨1800918189, 2228942012, true⟩ ⟨124428405237, 143431807089, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [104, 112]`. -/
theorem oscB_15_30_104_112 : legBOk (PBI 15 30) (TBI 104 112) ⟨5294134645, 5384577470, true⟩
    ⟨1800918189, 2228942012, true⟩ ⟨-60243149898, 17719728638, true⟩
    ⟨-52771872199, 30667761330, true⟩ ⟨3481082659, 4230781155, true⟩
    ⟨142016906772, 159955678458, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [104, 112]`. -/
theorem oscF_15_30_104_112 : finalOk
    ⟨-13245082872, 12621217746, true⟩ ⟨-30033827303, -1683391128, true⟩
    ⟨-60243149898, 17719728638, true⟩ ⟨-52771872199, 30667761330, true⟩
    ⟨3481082659, 4230781155, true⟩ ⟨124428405237, 143431807089, true⟩
    ⟨142016906772, 159955678458, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [104, 112]` is a leaf of the cover. -/
theorem oscLeaf_15_30_104_112 : OscLeaf 40 59 72 3086000000 4502000000 15 30 104 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_104_112, oscB_15_30_104_112, oscF_15_30_104_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [112, 120]`. -/
theorem oscA_15_30_112_120 : legAOk (PBI 15 30) (TBI 112 120) ⟨5352614721, 5441675126, true⟩
    ⟨-13114531718, 10615275382, true⟩ ⟨-27116540711, -724688488, true⟩
    ⟨1805514648, 2185316599, true⟩ ⟨125444341240, 141699538388, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [112, 120]`. -/
theorem oscB_15_30_112_120 : legBOk (PBI 15 30) (TBI 112 120) ⟨5352614721, 5441675126, true⟩
    ⟨1805514648, 2185316599, true⟩ ⟨-59613219958, 14884339272, true⟩
    ⟨-49434880921, 31066890400, true⟩ ⟨3478847699, 4181535987, true⟩
    ⟨142468879197, 160512237294, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [112, 120]`. -/
theorem oscF_15_30_112_120 : finalOk
    ⟨-13114531718, 10615275382, true⟩ ⟨-27116540711, -724688488, true⟩
    ⟨-59613219958, 14884339272, true⟩ ⟨-49434880921, 31066890400, true⟩
    ⟨3478847699, 4181535987, true⟩ ⟨125444341240, 141699538388, true⟩
    ⟨142468879197, 160512237294, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [112, 120]` is a leaf of the cover. -/
theorem oscLeaf_15_30_112_120 : OscLeaf 40 59 72 3086000000 4502000000 15 30 112 120 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_112_120, oscB_15_30_112_120, oscF_15_30_112_120⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[15, 30] × [120, 128]`. -/
theorem oscA_15_30_120_128 : legAOk (PBI 15 30) (TBI 120 128) ⟨5410654714, 5498367602, true⟩
    ⟨-14250419600, 10999665543, true⟩ ⟨-26384366278, 2015605211, true⟩
    ⟨1769932496, 2193927320, true⟩ ⟨124055766137, 142840200052, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[15, 30] × [120, 128]`. -/
theorem oscB_15_30_120_128 : legBOk (PBI 15 30) (TBI 120 128) ⟨5410654714, 5498367602, true⟩
    ⟨1769932496, 2193927320, true⟩ ⟨-61203608963, 13715172983, true⟩
    ⟨-48534255389, 33460781977, true⟩ ⟨3439209536, 4152394911, true⟩
    ⟨143117778854, 158860285198, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[15, 30] × [120, 128]`. -/
theorem oscF_15_30_120_128 : finalOk
    ⟨-14250419600, 10999665543, true⟩ ⟨-26384366278, 2015605211, true⟩
    ⟨-61203608963, 13715172983, true⟩ ⟨-48534255389, 33460781977, true⟩
    ⟨3439209536, 4152394911, true⟩ ⟨124055766137, 142840200052, true⟩
    ⟨143117778854, 158860285198, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[15, 30] × [120, 128]` is a leaf of the cover. -/
theorem oscLeaf_15_30_120_128 : OscLeaf 40 59 72 3086000000 4502000000 15 30 120 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_15_30_120_128, oscB_15_30_120_128, oscF_15_30_120_128⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [0, 4]`. -/
theorem oscA_30_45_0_4 : legAOk (PBI 30 45) (TBI 0 4) ⟨4531444312, 4609118781, true⟩
    ⟨5847408197, 32009012848, true⟩ ⟨-30358725334, -6955937900, true⟩
    ⟨1836864452, 2217746859, true⟩ ⟨119351667649, 136983320587, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [0, 4]`. -/
theorem oscB_30_45_0_4 : legBOk (PBI 30 45) (TBI 0 4) ⟨4531444312, 4609118781, true⟩
    ⟨1836864452, 2217746859, true⟩ ⟨-38929190488, 36644752650, true⟩
    ⟨-50922375327, 22027009017, true⟩ ⟨3673826350, 4376186096, true⟩
    ⟨142403245804, 160250273874, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [0, 4]`. -/
theorem oscF_30_45_0_4 : finalOk
    ⟨5847408197, 32009012848, true⟩ ⟨-30358725334, -6955937900, true⟩
    ⟨-38929190488, 36644752650, true⟩ ⟨-50922375327, 22027009017, true⟩
    ⟨3673826350, 4376186096, true⟩ ⟨119351667649, 136983320587, true⟩
    ⟨142403245804, 160250273874, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [0, 4]` is a leaf of the cover. -/
theorem oscLeaf_30_45_0_4 : OscLeaf 40 59 72 3086000000 4502000000 30 45 0 4 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_0_4, oscB_30_45_0_4, oscF_30_45_0_4⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [4, 8]`. -/
theorem oscA_30_45_4_8 : legAOk (PBI 30 45) (TBI 4 8) ⟨4564038978, 4640901716, true⟩
    ⟨5945469056, 30431402439, true⟩ ⟨-30001232194, -8788738732, true⟩
    ⟨1856314884, 2194284532, true⟩ ⟨120860739948, 135886569001, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [4, 8]`. -/
theorem oscB_30_45_4_8 : legBOk (PBI 30 45) (TBI 4 8) ⟨4564038978, 4640901716, true⟩
    ⟨1856314884, 2194284532, true⟩ ⟨-37509631998, 33378079913, true⟩
    ⟨-50027296689, 18997751328, true⟩ ⟨3672374805, 4330652392, true⟩
    ⟨141356592247, 159175112165, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [4, 8]`. -/
theorem oscF_30_45_4_8 : finalOk
    ⟨5945469056, 30431402439, true⟩ ⟨-30001232194, -8788738732, true⟩
    ⟨-37509631998, 33378079913, true⟩ ⟨-50027296689, 18997751328, true⟩
    ⟨3672374805, 4330652392, true⟩ ⟨120860739948, 135886569001, true⟩
    ⟨141356592247, 159175112165, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [4, 8]` is a leaf of the cover. -/
theorem oscLeaf_30_45_4_8 : OscLeaf 40 59 72 3086000000 4502000000 30 45 4 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_4_8, oscB_30_45_4_8, oscF_30_45_4_8⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [8, 12]`. -/
theorem oscA_30_45_8_12 : legAOk (PBI 30 45) (TBI 8 12) ⟨4596443909, 4672508594, true⟩
    ⟨4054426036, 30695607622, true⟩ ⟨-31268673755, -8343638005, true⟩
    ⟨1837732225, 2220711462, true⟩ ⟨120028598146, 137700380150, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [8, 12]`. -/
theorem oscB_30_45_8_12 : legBOk (PBI 30 45) (TBI 8 12) ⟨4596443909, 4672508594, true⟩
    ⟨1837732225, 2220711462, true⟩ ⟨-40570832441, 35775497452, true⟩
    ⟨-51861293482, 20831477274, true⟩ ⟨3662094335, 4366436673, true⟩
    ⟨142413207166, 160296318902, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [8, 12]`. -/
theorem oscF_30_45_8_12 : finalOk
    ⟨4054426036, 30695607622, true⟩ ⟨-31268673755, -8343638005, true⟩
    ⟨-40570832441, 35775497452, true⟩ ⟨-51861293482, 20831477274, true⟩
    ⟨3662094335, 4366436673, true⟩ ⟨120028598146, 137700380150, true⟩
    ⟨142413207166, 160296318902, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [8, 12]` is a leaf of the cover. -/
theorem oscLeaf_30_45_8_12 : OscLeaf 40 59 72 3086000000 4502000000 30 45 8 12 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_8_12, oscB_30_45_8_12, oscF_30_45_8_12⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [12, 16]`. -/
theorem oscA_30_45_12_16 : legAOk (PBI 30 45) (TBI 12 16) ⟨4628663546, 4703943405, true⟩
    ⟨4218894150, 29001346847, true⟩ ⟨-30848923999, -9970593545, true⟩
    ⟨1859102144, 2196318992, true⟩ ⟨121632572977, 136579752297, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [12, 16]`. -/
theorem oscB_30_45_12_16 : legBOk (PBI 30 45) (TBI 12 16) ⟨4628663546, 4703943405, true⟩
    ⟨1859102144, 2196318992, true⟩ ⟨-39061824359, 32185311933, true⟩
    ⟨-50766695356, 17912492432, true⟩ ⟨3664500114, 4320585562, true⟩
    ⟨141496176360, 159272644217, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [12, 16]`. -/
theorem oscF_30_45_12_16 : finalOk
    ⟨4218894150, 29001346847, true⟩ ⟨-30848923999, -9970593545, true⟩
    ⟨-39061824359, 32185311933, true⟩ ⟨-50766695356, 17912492432, true⟩
    ⟨3664500114, 4320585562, true⟩ ⟨121632572977, 136579752297, true⟩
    ⟨141496176360, 159272644217, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [12, 16]` is a leaf of the cover. -/
theorem oscLeaf_30_45_12_16 : OscLeaf 40 59 72 3086000000 4502000000 30 45 12 16 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_12_16, oscB_30_45_12_16, oscF_30_45_12_16⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
