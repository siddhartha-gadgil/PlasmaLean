/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells

/-!
# Kernel checks of the oscillatory-kick cover, part 16

Leaves 120–125 of the adaptive cover of the start window used by
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
/-- Inner-leg check of the box `[105, 120] × [40, 48]`. -/
theorem oscA_105_120_40_48 : legAOk (PBI 105 120) (TBI 40 48) ⟨5034116401, 5123122324, true⟩
    ⟨-11308097259, 17985917352, true⟩ ⟨-36630697866, -7717505606, true⟩
    ⟨1669309706, 2030096245, true⟩ ⟨119979178815, 137616134025, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [40, 48]`. -/
theorem oscB_105_120_40_48 : legBOk (PBI 105 120) (TBI 40 48) ⟨5034116401, 5123122324, true⟩
    ⟨1669309706, 2030096245, true⟩ ⟨-59878371382, 18120341613, true⟩
    ⟨-53794570386, 28314833715, true⟩ ⟨3276234215, 3932367293, true⟩
    ⟨137202141062, 154636290885, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [40, 48]`. -/
theorem oscF_105_120_40_48 : finalOk
    ⟨-11308097259, 17985917352, true⟩ ⟨-36630697866, -7717505606, true⟩
    ⟨-59878371382, 18120341613, true⟩ ⟨-53794570386, 28314833715, true⟩
    ⟨3276234215, 3932367293, true⟩ ⟨119979178815, 137616134025, true⟩
    ⟨137202141062, 154636290885, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[105, 120] × [40, 48]` is a leaf of the cover. -/
theorem oscLeaf_105_120_40_48 : OscLeaf 40 59 72 3086000000 4502000000 105 120 40 48 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_40_48, oscB_105_120_40_48, oscF_105_120_40_48⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [48, 64]`. -/
theorem oscA_105_120_48_64 : legAOk (PBI 105 120) (TBI 48 64) ⟨5090770952, 5233353415, true⟩
    ⟨-15142641850, 18384133155, true⟩ ⟨-37693197054, -2044447689, true⟩
    ⟨1629843126, 2050650764, true⟩ ⟨118728243748, 139405088596, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [48, 64]`. -/
theorem oscB_105_120_48_64 : legBOk (PBI 105 120) (TBI 48 64) ⟨5090770952, 5233353415, true⟩
    ⟨1629843126, 2050650764, true⟩ ⟨-69271715324, 25447878585, true⟩
    ⟨-62528181092, 41841608516, true⟩ ⟨3189683842, 3989986975, true⟩
    ⟨135217496342, 158224384210, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [48, 64]`. -/
theorem oscF_105_120_48_64 : finalOk
    ⟨-15142641850, 18384133155, true⟩ ⟨-37693197054, -2044447689, true⟩
    ⟨-69271715324, 25447878585, true⟩ ⟨-62528181092, 41841608516, true⟩
    ⟨3189683842, 3989986975, true⟩ ⟨118728243748, 139405088596, true⟩
    ⟨135217496342, 158224384210, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[105, 120] × [48, 64]` is a leaf of the cover. -/
theorem oscLeaf_105_120_48_64 : OscLeaf 40 59 72 3086000000 4502000000 105 120 48 64 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_48_64, oscB_105_120_48_64, oscF_105_120_48_64⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [64, 80]`. -/
theorem oscA_105_120_64_80 : legAOk (PBI 105 120) (TBI 64 80) ⟨5202669339, 5341888030, true⟩
    ⟨-17325233562, 16767048280, true⟩ ⟨-36458990992, 2025380398, true⟩
    ⟨1604161368, 2064766691, true⟩ ⟨118333802735, 141384468541, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [64, 80]`. -/
theorem oscB_105_120_64_80 : legBOk (PBI 105 120) (TBI 64 80) ⟨5202669339, 5341888030, true⟩
    ⟨1604161368, 2064766691, true⟩ ⟨-72248015589, 24939492749, true⟩
    ⟨-63041998749, 47970317188, true⟩ ⟨3155683180, 3992510796, true⟩
    ⟨136232289452, 159030821535, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [64, 80]`. -/
theorem oscF_105_120_64_80 : finalOk
    ⟨-17325233562, 16767048280, true⟩ ⟨-36458990992, 2025380398, true⟩
    ⟨-72248015589, 24939492749, true⟩ ⟨-63041998749, 47970317188, true⟩
    ⟨3155683180, 3992510796, true⟩ ⟨118333802735, 141384468541, true⟩
    ⟨136232289452, 159030821535, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[105, 120] × [64, 80]` is a leaf of the cover. -/
theorem oscLeaf_105_120_64_80 : OscLeaf 40 59 72 3086000000 4502000000 105 120 64 80 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_64_80, oscB_105_120_64_80, oscF_105_120_64_80⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [80, 96]`. -/
theorem oscA_105_120_80_96 : legAOk (PBI 105 120) (TBI 80 96) ⟨5312806093, 5448851500, true⟩
    ⟨-17894288248, 14426170403, true⟩ ⟨-32202796214, 4265291181, true⟩
    ⟨1615411599, 2032110632, true⟩ ⟨120374013821, 140651555407, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [80, 96]`. -/
theorem oscB_105_120_80_96 : legBOk (PBI 105 120) (TBI 80 96) ⟨5312806093, 5448851500, true⟩
    ⟨1615411599, 2032110632, true⟩ ⟨-72370264863, 20086268322, true⟩
    ⟨-56929096842, 48512995919, true⟩ ⟨3136400853, 3919646210, true⟩
    ⟨135528941183, 157773725578, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [80, 96]`. -/
theorem oscF_105_120_80_96 : finalOk
    ⟨-17894288248, 14426170403, true⟩ ⟨-32202796214, 4265291181, true⟩
    ⟨-72370264863, 20086268322, true⟩ ⟨-56929096842, 48512995919, true⟩
    ⟨3136400853, 3919646210, true⟩ ⟨120374013821, 140651555407, true⟩
    ⟨135528941183, 157773725578, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[105, 120] × [80, 96]` is a leaf of the cover. -/
theorem oscLeaf_105_120_80_96 : OscLeaf 40 59 72 3086000000 4502000000 105 120 80 96 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_80_96, oscB_105_120_80_96, oscF_105_120_80_96⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [96, 112]`. -/
theorem oscA_105_120_96_112 : legAOk (PBI 105 120) (TBI 96 112) ⟨5421313227, 5554358741, true⟩
    ⟨-19932963176, 15520753256, true⟩ ⟨-30327846544, 8476575616, true⟩
    ⟨1589064528, 2050785586, true⟩ ⟨120018117167, 142907234682, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [96, 112]`. -/
theorem oscB_105_120_96_112 : legBOk (PBI 105 120) (TBI 96 112) ⟨5421313227, 5554358741, true⟩
    ⟨1589064528, 2050785586, true⟩ ⟨-74055581522, 20189212344, true⟩
    ⟨-54462516829, 52969509905, true⟩ ⟨3103846879, 3900206961, true⟩
    ⟨136709086847, 156664114513, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [96, 112]`. -/
theorem oscF_105_120_96_112 : finalOk
    ⟨-19932963176, 15520753256, true⟩ ⟨-30327846544, 8476575616, true⟩
    ⟨-74055581522, 20189212344, true⟩ ⟨-54462516829, 52969509905, true⟩
    ⟨3103846879, 3900206961, true⟩ ⟨120018117167, 142907234682, true⟩
    ⟨136709086847, 156664114513, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[105, 120] × [96, 112]` is a leaf of the cover. -/
theorem oscLeaf_105_120_96_112 : OscLeaf 40 59 72 3086000000 4502000000 105 120 96 112 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_96_112, oscB_105_120_96_112, oscF_105_120_96_112⟩

set_option maxRecDepth 100000 in
/-- Inner-leg check of the box `[105, 120] × [112, 128]`. -/
theorem oscA_105_120_112_128 : legAOk (PBI 105 120) (TBI 112 128) ⟨5528311548, 5658515593, true⟩
    ⟨-19988665318, 14895353675, true⟩ ⟨-25703420305, 10239091533, true⟩
    ⟨1601967333, 2020705953, true⟩ ⟨122195732615, 142376101625, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Outer-leg check of the box `[105, 120] × [112, 128]`. -/
theorem oscB_105_120_112_128 : legBOk (PBI 105 120) (TBI 112 128) ⟨5528311548, 5658515593, true⟩
    ⟨1601967333, 2020705953, true⟩ ⟨-74153379011, 20569695216, true⟩
    ⟨-50189535155, 55350792085, true⟩ ⟨3087039409, 3864116451, true⟩
    ⟨136094767139, 157883659765, true⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Final check of the box `[105, 120] × [112, 128]`. -/
theorem oscF_105_120_112_128 : finalOk
    ⟨-19988665318, 14895353675, true⟩ ⟨-25703420305, 10239091533, true⟩
    ⟨-74153379011, 20569695216, true⟩ ⟨-50189535155, 55350792085, true⟩
    ⟨3087039409, 3864116451, true⟩ ⟨122195732615, 142376101625, true⟩
    ⟨136094767139, 157883659765, true⟩ 40 1 59 72
    3086000000 4502000000 = true := by
  decide +kernel

/-- The box `[105, 120] × [112, 128]` is a leaf of the cover. -/
theorem oscLeaf_105_120_112_128 : OscLeaf 40 59 72 3086000000 4502000000 105 120 112 128 :=
  ⟨_, _, _, _, _, _, _, _, _, oscA_105_120_112_128, oscB_105_120_112_128, oscF_105_120_112_128⟩

end PlasmaLean.Design.NearAxisQATrappedOsc
