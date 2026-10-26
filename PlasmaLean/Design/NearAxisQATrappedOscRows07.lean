/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Kernel checks of the oscillatory-kick cover, part 7

Leaves 48–55 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[30, 45] × [16, 24]`. -/
theorem oscA_30_45_16_24 : legAOk (PBI 30 45) (TBI 16 24) ⟨4660702191, 4766312185, true⟩
    ⟨-241482787, 30205047525, true⟩ ⟨-33234034270, -7931364924, true⟩
    ⟨1811494759, 2230850236, true⟩ ⟨119367761748, 138778184568, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [16, 24]`. -/
theorem oscB_30_45_16_24 : legBOk (PBI 30 45) (TBI 16 24) ⟨4660702191, 4766312185, true⟩
    ⟨1811494759, 2230850236, true⟩ ⟨-47191347008, 38145741978, true⟩
    ⟨-56318520975, 23692940076, true⟩ ⟨3601510642, 4370124345, true⟩
    ⟨141276859898, 160815647928, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [16, 24]`. -/
theorem oscF_30_45_16_24 : finalOk
    ⟨-241482787, 30205047525, true⟩ ⟨-33234034270, -7931364924, true⟩
    ⟨-47191347008, 38145741978, true⟩ ⟨-56318520975, 23692940076, true⟩
    ⟨3601510642, 4370124345, true⟩ ⟨119367761748, 138778184568, true⟩
    ⟨141276859898, 160815647928, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [16, 24]` is a leaf of the cover. -/
theorem oscLeaf_30_45_16_24 : OscLeaf 40 59 72 3086000000 4502000000 30 45 16 24 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_16_24, oscB_30_45_16_24, oscF_30_45_16_24⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [24, 32]`. -/
theorem oscA_30_45_24_32 : legAOk (PBI 30 45) (TBI 24 32) ⟨4724253041, 4828037635, true⟩
    ⟨-2058444160, 28665804639, true⟩ ⟨-33985737028, -8481536772, true⟩
    ⟨1814013003, 2234044749, true⟩ ⟨120150289242, 139529379880, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [24, 32]`. -/
theorem oscB_30_45_24_32 : legBOk (PBI 30 45) (TBI 24 32) ⟨4724253041, 4828037635, true⟩
    ⟨1814013003, 2234044749, true⟩ ⟨-48867335195, 36780738399, true⟩
    ⟨-56799687327, 23335956449, true⟩ ⟨3594169313, 4360776548, true⟩
    ⟨141475161130, 160875046764, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [24, 32]`. -/
theorem oscF_30_45_24_32 : finalOk
    ⟨-2058444160, 28665804639, true⟩ ⟨-33985737028, -8481536772, true⟩
    ⟨-48867335195, 36780738399, true⟩ ⟨-56799687327, 23335956449, true⟩
    ⟨3594169313, 4360776548, true⟩ ⟨120150289242, 139529379880, true⟩
    ⟨141475161130, 160875046764, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [24, 32]` is a leaf of the cover. -/
theorem oscLeaf_30_45_24_32 : OscLeaf 40 59 72 3086000000 4502000000 30 45 24 32 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_24_32, oscB_30_45_24_32, oscF_30_45_24_32⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [32, 40]`. -/
theorem oscA_30_45_32_40 : legAOk (PBI 30 45) (TBI 32 40) ⟨4787128249, 4889147629, true⟩
    ⟨-3799831020, 27057295630, true⟩ ⟨-34631819807, -8797548817, true⟩
    ⟨1818358416, 2236404708, true⟩ ⟨121036728947, 140251490429, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [32, 40]`. -/
theorem oscB_30_45_32_40 : legBOk (PBI 30 45) (TBI 32 40) ⟨4787128249, 4889147629, true⟩
    ⟨1818358416, 2236404708, true⟩ ⟨-50498219417, 35294529593, true⟩
    ⟨-57239515552, 23273578134, true⟩ ⟨3589018200, 4353001615, true⟩
    ⟨141701566927, 161095677834, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [32, 40]`. -/
theorem oscF_30_45_32_40 : finalOk
    ⟨-3799831020, 27057295630, true⟩ ⟨-34631819807, -8797548817, true⟩
    ⟨-50498219417, 35294529593, true⟩ ⟨-57239515552, 23273578134, true⟩
    ⟨3589018200, 4353001615, true⟩ ⟨121036728947, 140251490429, true⟩
    ⟨141701566927, 161095677834, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [32, 40]` is a leaf of the cover. -/
theorem oscLeaf_30_45_32_40 : OscLeaf 40 59 72 3086000000 4502000000 30 45 32 40 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_32_40, oscB_30_45_32_40, oscF_30_45_32_40⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [40, 48]`. -/
theorem oscA_30_45_40_48 : legAOk (PBI 30 45) (TBI 40 48) ⟨4849357722, 4949668465, true⟩
    ⟨-4723380587, 23700679427, true⟩ ⟨-33792144112, -9676666860, true⟩
    ⟨1820692761, 2190550950, true⟩ ⟨121827737192, 138224933926, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [40, 48]`. -/
theorem oscB_30_45_40_48 : legBOk (PBI 30 45) (TBI 40 48) ⟨4849357722, 4949668465, true⟩
    ⟨1820692761, 2190550950, true⟩ ⟨-51080174140, 31672598956, true⟩
    ⟨-56735540094, 22882139726, true⟩ ⟨3555537157, 4298098368, true⟩
    ⟨139998270071, 161399187933, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [40, 48]`. -/
theorem oscF_30_45_40_48 : finalOk
    ⟨-4723380587, 23700679427, true⟩ ⟨-33792144112, -9676666860, true⟩
    ⟨-51080174140, 31672598956, true⟩ ⟨-56735540094, 22882139726, true⟩
    ⟨3555537157, 4298098368, true⟩ ⟨121827737192, 138224933926, true⟩
    ⟨139998270071, 161399187933, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_30_45_40_48 : OscLeaf 40 59 72 3086000000 4502000000 30 45 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_40_48, oscB_30_45_40_48, oscF_30_45_40_48⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [48, 56]`. -/
theorem oscA_30_45_48_56 : legAOk (PBI 30 45) (TBI 48 56) ⟨4910969628, 5009625008, true⟩
    ⟨-7468147506, 22427811170, true⟩ ⟨-34436923152, -8198352144, true⟩
    ⟨1782761736, 2195782487, true⟩ ⟨120145335560, 139097842965, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [48, 56]`. -/
theorem oscB_30_45_48_56 : legBOk (PBI 30 45) (TBI 48 56) ⟨4910969628, 5009625008, true⟩
    ⟨1782761736, 2195782487, true⟩ ⟨-53911867281, 28615202566, true⟩
    ⟨-57022924150, 23383064416, true⟩ ⟨3511758693, 4258735170, true⟩
    ⟨140480910171, 159235012281, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [48, 56]`. -/
theorem oscF_30_45_48_56 : finalOk
    ⟨-7468147506, 22427811170, true⟩ ⟨-34436923152, -8198352144, true⟩
    ⟨-53911867281, 28615202566, true⟩ ⟨-57022924150, 23383064416, true⟩
    ⟨3511758693, 4258735170, true⟩ ⟨120145335560, 139097842965, true⟩
    ⟨140480910171, 159235012281, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [48, 56]` is a leaf of the cover. -/
theorem oscLeaf_30_45_48_56 : OscLeaf 40 59 72 3086000000 4502000000 30 45 48 56 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_48_56, oscB_30_45_48_56, oscF_30_45_48_56⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [56, 64]`. -/
theorem oscA_30_45_56_64 : legAOk (PBI 30 45) (TBI 56 64) ⟨4971990553, 5069040795, true⟩
    ⟨-8693631566, 20745772663, true⟩ ⟨-34446149833, -7788225623, true⟩
    ⟨1788881978, 2198736726, true⟩ ⟨121163927236, 139896733068, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [56, 64]`. -/
theorem oscB_30_45_56_64 : legBOk (PBI 30 45) (TBI 56 64) ⟨4971990553, 5069040795, true⟩
    ⟨1788881978, 2198736726, true⟩ ⟨-55078765558, 26817199887, true⟩
    ⟨-56702689609, 24086287248, true⟩ ⟨3509919855, 4251741948, true⟩
    ⟨140816348728, 159468627636, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [56, 64]`. -/
theorem oscF_30_45_56_64 : finalOk
    ⟨-8693631566, 20745772663, true⟩ ⟨-34446149833, -7788225623, true⟩
    ⟨-55078765558, 26817199887, true⟩ ⟨-56702689609, 24086287248, true⟩
    ⟨3509919855, 4251741948, true⟩ ⟨121163927236, 139896733068, true⟩
    ⟨140816348728, 159468627636, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [56, 64]` is a leaf of the cover. -/
theorem oscLeaf_30_45_56_64 : OscLeaf 40 59 72 3086000000 4502000000 30 45 56 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_56_64, oscB_30_45_56_64, oscF_30_45_56_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [64, 72]`. -/
theorem oscA_30_45_64_72 : legAOk (PBI 30 45) (TBI 64 72) ⟨5032445630, 5127938142, true⟩
    ⟨-9925843710, 19288464559, true⟩ ⟨-34451387974, -6990437744, true⟩
    ⟨1790547289, 2207584041, true⟩ ⟨121965713497, 140976966439, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [64, 72]`. -/
theorem oscB_30_45_64_72 : legBOk (PBI 30 45) (TBI 64 72) ⟨5032445630, 5127938142, true⟩
    ⟨1790547289, 2207584041, true⟩ ⟨-56495994016, 25520977678, true⟩
    ⟨-56627428846, 25462242598, true⟩ ⟨3504309099, 4251542057, true⟩
    ⟨141200704046, 159763172124, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [64, 72]`. -/
theorem oscF_30_45_64_72 : finalOk
    ⟨-9925843710, 19288464559, true⟩ ⟨-34451387974, -6990437744, true⟩
    ⟨-56495994016, 25520977678, true⟩ ⟨-56627428846, 25462242598, true⟩
    ⟨3504309099, 4251542057, true⟩ ⟨121965713497, 140976966439, true⟩
    ⟨141200704046, 159763172124, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [64, 72]` is a leaf of the cover. -/
theorem oscLeaf_30_45_64_72 : OscLeaf 40 59 72 3086000000 4502000000 30 45 64 72 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_64_72, oscB_30_45_64_72, oscF_30_45_64_72⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[30, 45] × [72, 80]`. -/
theorem oscA_30_45_72_80 : legAOk (PBI 30 45) (TBI 72 80) ⟨5092358648, 5186338251, true⟩
    ⟨-10943284686, 17764225128, true⟩ ⟨-34207720169, -6204658168, true⟩
    ⟨1794919335, 2213892321, true⟩ ⟨122898974703, 141932573869, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[30, 45] × [72, 80]`. -/
theorem oscB_30_45_72_80 : legBOk (PBI 30 45) (TBI 72 80) ⟨5092358648, 5186338251, true⟩
    ⟨1794919335, 2213892321, true⟩ ⟨-57521949029, 23993834518, true⟩
    ⟨-56175465425, 26729053139, true⟩ ⟨3503084612, 4249204078, true⟩
    ⟨141703143864, 160088067903, true⟩ = true := by
  fiv_cert

set_option maxRecDepth 100000 in
/-- Final check of the box `[30, 45] × [72, 80]`. -/
theorem oscF_30_45_72_80 : finalOk
    ⟨-10943284686, 17764225128, true⟩ ⟨-34207720169, -6204658168, true⟩
    ⟨-57521949029, 23993834518, true⟩ ⟨-56175465425, 26729053139, true⟩
    ⟨3503084612, 4249204078, true⟩ ⟨122898974703, 141932573869, true⟩
    ⟨141703143864, 160088067903, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  fiv_cert

/-- The box `[30, 45] × [72, 80]` is a leaf of the cover. -/
theorem oscLeaf_30_45_72_80 : OscLeaf 40 59 72 3086000000 4502000000 30 45 72 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_30_45_72_80, oscB_30_45_72_80, oscF_30_45_72_80⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
