/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 13

Leaves 96–103 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[75, 90] × [48, 56]`. -/
theorem oscA_75_90_48_56 : legAOk (PBI 75 90) (TBI 48 56) ⟨5022730519, 5114433029, true⟩
    ⟨-10519323105, 18694672834, true⟩ ⟨-35770990433, -7655648781, true⟩
    ⟨1713653654, 2092331136, true⟩ ⟨120544464134, 138578037856, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [48, 56]`. -/
theorem oscB_75_90_48_56 : legBOk (PBI 75 90) (TBI 48 56) ⟨5022730519, 5114433029, true⟩
    ⟨1713653654, 2092331136, true⟩ ⟨-58062449044, 22118134851, true⟩
    ⟨-55296583178, 27659569667, true⟩ ⟨3376426696, 4065743205, true⟩
    ⟨139723996544, 157691898141, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [48, 56]`. -/
theorem oscF_75_90_48_56 : finalOk
    ⟨-10519323105, 18694672834, true⟩ ⟨-35770990433, -7655648781, true⟩
    ⟨-58062449044, 22118134851, true⟩ ⟨-55296583178, 27659569667, true⟩
    ⟨3376426696, 4065743205, true⟩ ⟨120544464134, 138578037856, true⟩
    ⟨139723996544, 157691898141, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [48, 56]` is a leaf of the cover. -/
theorem oscLeaf_75_90_48_56 : OscLeaf 40 59 72 3086000000 4502000000 75 90 48 56 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_48_56, oscB_75_90_48_56, oscF_75_90_48_56⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [56, 64]`. -/
theorem oscA_75_90_56_64 : legAOk (PBI 75 90) (TBI 56 64) ⟨5080709576, 5171014903, true⟩
    ⟨-11626692666, 17239808531, true⟩ ⟨-35413613453, -6648530633, true⟩
    ⟨1716712750, 2100351254, true⟩ ⟨121400228924, 139619594052, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [56, 64]`. -/
theorem oscB_75_90_56_64 : legBOk (PBI 75 90) (TBI 56 64) ⟨5080709576, 5171014903, true⟩
    ⟨1716712750, 2100351254, true⟩ ⟨-59632263475, 18838378608, true⟩
    ⟨-54570425851, 27850068377, true⟩ ⟨3348980606, 4038111927, true⟩
    ⟨138295347423, 156017635971, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [56, 64]`. -/
theorem oscF_75_90_56_64 : finalOk
    ⟨-11626692666, 17239808531, true⟩ ⟨-35413613453, -6648530633, true⟩
    ⟨-59632263475, 18838378608, true⟩ ⟨-54570425851, 27850068377, true⟩
    ⟨3348980606, 4038111927, true⟩ ⟨121400228924, 139619594052, true⟩
    ⟨138295347423, 156017635971, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [56, 64]` is a leaf of the cover. -/
theorem oscLeaf_75_90_56_64 : OscLeaf 40 59 72 3086000000 4502000000 75 90 56 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_56_64, oscB_75_90_56_64, oscF_75_90_56_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [64, 80]`. -/
theorem oscA_75_90_64_80 : legAOk (PBI 75 90) (TBI 64 80) ⟨5138192441, 5282823473, true⟩
    ⟨-15196750464, 17542569403, true⟩ ⟨-36338271421, -1099852745, true⟩
    ⟨1677258644, 2119902082, true⟩ ⟨120247870216, 141346543480, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [64, 80]`. -/
theorem oscB_75_90_64_80 : legBOk (PBI 75 90) (TBI 64 80) ⟨5138192441, 5282823473, true⟩
    ⟨1677258644, 2119902082, true⟩ ⟨-68763533015, 25955220035, true⟩
    ⟨-62651223381, 41166462063, true⟩ ⟨3261148494, 4094921066, true⟩
    ⟨136335816451, 159619447510, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [64, 80]`. -/
theorem oscF_75_90_64_80 : finalOk
    ⟨-15196750464, 17542569403, true⟩ ⟨-36338271421, -1099852745, true⟩
    ⟨-68763533015, 25955220035, true⟩ ⟨-62651223381, 41166462063, true⟩
    ⟨3261148494, 4094921066, true⟩ ⟨120247870216, 141346543480, true⟩
    ⟨136335816451, 159619447510, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [64, 80]` is a leaf of the cover. -/
theorem oscLeaf_75_90_64_80 : OscLeaf 40 59 72 3086000000 4502000000 75 90 64 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_64_80, oscB_75_90_64_80, oscF_75_90_64_80⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [80, 88]`. -/
theorem oscA_75_90_80_88 : legAOk (PBI 75 90) (TBI 80 88) ⟨5251747752, 5338084964, true⟩
    ⟨-13929888386, 12527043429, true⟩ ⟨-31362250406, -1972852058, true⟩
    ⟨1692560137, 2073999439, true⟩ ⟨121847534770, 139872981933, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [80, 88]`. -/
theorem oscB_75_90_80_88 : legBOk (PBI 75 90) (TBI 80 88) ⟨5251747752, 5338084964, true⟩
    ⟨1692560137, 2073999439, true⟩ ⟨-62414481219, 14416097407, true⟩
    ⟨-51263038211, 33790356744, true⟩ ⟨3309678332, 3991717159, true⟩
    ⟨139728228397, 157164977489, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [80, 88]`. -/
theorem oscF_75_90_80_88 : finalOk
    ⟨-13929888386, 12527043429, true⟩ ⟨-31362250406, -1972852058, true⟩
    ⟨-62414481219, 14416097407, true⟩ ⟨-51263038211, 33790356744, true⟩
    ⟨3309678332, 3991717159, true⟩ ⟨121847534770, 139872981933, true⟩
    ⟨139728228397, 157164977489, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [80, 88]` is a leaf of the cover. -/
theorem oscLeaf_75_90_80_88 : OscLeaf 40 59 72 3086000000 4502000000 75 90 80 88 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_80_88, oscB_75_90_80_88, oscF_75_90_80_88⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [88, 96]`. -/
theorem oscA_75_90_88_96 : legAOk (PBI 75 90) (TBI 88 96) ⟨5307856980, 5392939831, true⟩
    ⟨-14740818178, 11904172053, true⟩ ⟨-30362994009, -746208150, true⟩
    ⟨1698346655, 2080309660, true⟩ ⟨122854433142, 140835772068, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [88, 96]`. -/
theorem oscB_75_90_88_96 : legBOk (PBI 75 90) (TBI 88 96) ⟨5307856980, 5392939831, true⟩
    ⟨1698346655, 2080309660, true⟩ ⟨-62287212254, 11274927115, true⟩
    ⟨-48587080102, 33441881862, true⟩ ⟨3312081510, 3961484341, true⟩
    ⟨140330089288, 155422645688, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [88, 96]`. -/
theorem oscF_75_90_88_96 : finalOk
    ⟨-14740818178, 11904172053, true⟩ ⟨-30362994009, -746208150, true⟩
    ⟨-62287212254, 11274927115, true⟩ ⟨-48587080102, 33441881862, true⟩
    ⟨3312081510, 3961484341, true⟩ ⟨122854433142, 140835772068, true⟩
    ⟨140330089288, 155422645688, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [88, 96]` is a leaf of the cover. -/
theorem oscLeaf_75_90_88_96 : OscLeaf 40 59 72 3086000000 4502000000 75 90 88 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_88_96, oscB_75_90_88_96, oscF_75_90_88_96⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [96, 112]`. -/
theorem oscA_75_90_96_112 : legAOk (PBI 75 90) (TBI 96 112) ⟨5363543709, 5501491182, true⟩
    ⟨-17878335414, 14321454574, true⟩ ⟨-30937353180, 5142585560, true⟩
    ⟨1659794627, 2102778775, true⟩ ⟨121836272158, 142748294685, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [96, 112]`. -/
theorem oscB_75_90_96_112 : legBOk (PBI 75 90) (TBI 96 112) ⟨5363543709, 5501491182, true⟩
    ⟨1659794627, 2102778775, true⟩ ⟨-72026559862, 21436402899, true⟩
    ⟨-57394294580, 48276932586, true⟩ ⟨3203017070, 4024484070, true⟩
    ⟨136706293669, 159274232981, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [96, 112]`. -/
theorem oscF_75_90_96_112 : finalOk
    ⟨-17878335414, 14321454574, true⟩ ⟨-30937353180, 5142585560, true⟩
    ⟨-72026559862, 21436402899, true⟩ ⟨-57394294580, 48276932586, true⟩
    ⟨3203017070, 4024484070, true⟩ ⟨121836272158, 142748294685, true⟩
    ⟨136706293669, 159274232981, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [96, 112]` is a leaf of the cover. -/
theorem oscLeaf_75_90_96_112 : OscLeaf 40 59 72 3086000000 4502000000 75 90 96 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_96_112, oscB_75_90_96_112, oscF_75_90_96_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[75, 90] × [112, 128]`. -/
theorem oscA_75_90_112_128 : legAOk (PBI 75 90) (TBI 112 128) ⟨5473714492, 5608594251, true⟩
    ⟨-18736191348, 14160610502, true⟩ ⟨-26777835534, 8703735372, true⟩
    ⟨1634518274, 2071565789, true⟩ ⟨121648049106, 142230046804, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[75, 90] × [112, 128]`. -/
theorem oscB_75_90_112_128 : legBOk (PBI 75 90) (TBI 112 128) ⟨5473714492, 5608594251, true⟩
    ⟨1634518274, 2071565789, true⟩ ⟨-71978656642, 19260898522, true⟩
    ⟨-51729790583, 50656105882, true⟩ ⟨3171338525, 3953333203, true⟩
    ⟨137953779495, 158156603878, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[75, 90] × [112, 128]`. -/
theorem oscF_75_90_112_128 : finalOk
    ⟨-18736191348, 14160610502, true⟩ ⟨-26777835534, 8703735372, true⟩
    ⟨-71978656642, 19260898522, true⟩ ⟨-51729790583, 50656105882, true⟩
    ⟨3171338525, 3953333203, true⟩ ⟨121648049106, 142230046804, true⟩
    ⟨137953779495, 158156603878, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[75, 90] × [112, 128]` is a leaf of the cover. -/
theorem oscLeaf_75_90_112_128 : OscLeaf 40 59 72 3086000000 4502000000 75 90 112 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_75_90_112_128, oscB_75_90_112_128, oscF_75_90_112_128⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[90, 105] × [0, 8]`. -/
theorem oscA_90_105_0_8 : legAOk (PBI 90 105) (TBI 0 8) ⟨4703815048, 4802361647, true⟩
    ⟨-2383934386, 28975433424, true⟩ ⟨-36663731646, -10503804276, true⟩
    ⟨1711431980, 2081752424, true⟩ ⟨118242152852, 136344396576, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[90, 105] × [0, 8]`. -/
theorem oscB_90_105_0_8 : legBOk (PBI 90 105) (TBI 0 8) ⟨4703815048, 4802361647, true⟩
    ⟨1711431980, 2081752424, true⟩ ⟨-50832961656, 34120982501, true⟩
    ⟨-57059539147, 26418131805, true⟩ ⟨3392484421, 4110793607, true⟩
    ⟨137378978832, 158102921714, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[90, 105] × [0, 8]`. -/
theorem oscF_90_105_0_8 : finalOk
    ⟨-2383934386, 28975433424, true⟩ ⟨-36663731646, -10503804276, true⟩
    ⟨-50832961656, 34120982501, true⟩ ⟨-57059539147, 26418131805, true⟩
    ⟨3392484421, 4110793607, true⟩ ⟨118242152852, 136344396576, true⟩
    ⟨137378978832, 158102921714, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[90, 105] × [0, 8]` is a leaf of the cover. -/
theorem oscLeaf_90_105_0_8 : OscLeaf 40 59 72 3086000000 4502000000 90 105 0 8 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_90_105_0_8, oscB_90_105_0_8, oscF_90_105_0_8⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
