/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscKick
public import PlasmaLean.Design.NearAxisQATrappedOscRows01
public import PlasmaLean.Design.NearAxisQATrappedOscRows02
public import PlasmaLean.Design.NearAxisQATrappedOscRows03
public import PlasmaLean.Design.NearAxisQATrappedOscRows04
public import PlasmaLean.Design.NearAxisQATrappedOscRows05
public import PlasmaLean.Design.NearAxisQATrappedOscRows06
public import PlasmaLean.Design.NearAxisQATrappedOscRows07
public import PlasmaLean.Design.NearAxisQATrappedOscRows08
public import PlasmaLean.Design.NearAxisQATrappedOscRows09
public import PlasmaLean.Design.NearAxisQATrappedOscRows10
public import PlasmaLean.Design.NearAxisQATrappedOscRows11
public import PlasmaLean.Design.NearAxisQATrappedOscRows12
public import PlasmaLean.Design.NearAxisQATrappedOscRows13
public import PlasmaLean.Design.NearAxisQATrappedOscRows14
public import PlasmaLean.Design.NearAxisQATrappedOscRows15
public import PlasmaLean.Design.NearAxisQATrappedOscRows16

/-!
# Certified oscillatory kick of exact-QA reference bounces (trapped alphas, start window)

Companion to `notes/theory/trapped-alpha-status.md` §6. Model only: the exactly
quasi-axisymmetric member `exactQA` of the reactor near-axis family, vacuum Boozer
guiding-centre equations; orbits are those of `NearAxisQATrappedResonance.Setup` (start window
`ψ₀ ∈ [4.75, 5.79] T m²`, tip field `B_t = E/μ ∈ [5.4, 5.5] T`, `T ≥ 1.6 ms`).

**The cover.** `osc_cover`: an adaptive binary subdivision of the index window
`[0, 120] × [0, 128]` (`ψ₀ ∈ [4.75, 5.8047]`, `B_t ∈ [5.4, 5.5]`) into `126` leaves, each passing
the split kernel checks of `NearAxisQATrappedOscRows01`–`16` (about `11 s` of kernel time per
leaf) with amplitude target `Kn = 40`, period range `[59, 72] μs` and precession range
`ι₀ Δ ∈ [3086000000, 4502000000] · 2⁻³²`.

**Results.**

* `exactQA_kick_osc`: every reference bounce of the window closes at `P ∈ [59, 72] μs` with
  `Δ = φ(P) − φ(0) ∈ [1.70, 2.49]`, `sin Δ ≥ 3/5`, and the normalised oscillatory kick integrals
  satisfy `√(Ĉ² + Ŝ²) ≤ 40 sin Δ` (`Ĉ = ∫₀ᴾ A w cos 2(φ − φ₀)`, RK4: about `9.3 / 0.87`);
* `reference_kick_osc`: for `reactorQA` (`b₁ = −4.3 × 10⁻⁴`) the reference kick
  `∫₀ᴾ g sin 2φ = C sin 2φ(0) + S cos 2φ(0)` has, in flux units,
  `√(C² + S²)/(q ι₀ sin Δ) ≤ M_eff = 0.0816 T m²` (`osc_amplitude_le`), against the previous
  certified `0.2364` and the simulated `0.023`. So `|C/(q ι₀ sin Δ)|, |S/(q ι₀ sin Δ)| ≤ 0.0816`:
  admissible data of the re-anchored scheme with `M = 0.0816 < 0.13`.

**Budget** (`osc_crude_shears_fail`, `osc_budget_requirement`, `osc_budget_simulated`): see the
docstrings and the status note; the shears `σ, γ` and remainders `R, e` are not proved.
-/
public section
noncomputable section

namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.NearAxisQATrappedCells
  PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedResonance PlasmaLean.Design.NearAxisQATrappedPeriodic
  Real Set

/-- **The adaptive cover of the start window** (126 leaves, kernel checks in
`NearAxisQATrappedOscRows01`–`16`). -/
theorem osc_cover : OscCover 40 59 72 3086000000 4502000000 0 120 0 128 :=
  (OscCover.splitP 0 60 120 0 128
    (OscCover.splitP 0 30 60 0 128
    (OscCover.splitP 0 15 30 0 128
    (OscCover.splitT 0 15 0 64 128
    (OscCover.splitT 0 15 0 32 64
    (OscCover.splitT 0 15 0 16 32
    (OscCover.splitT 0 15 0 8 16
    (OscCover.splitT 0 15 0 4 8
    (OscCover.splitP 0 7 15 0 4
    (OscCover.leaf 0 7 0 4 oscLeaf_0_7_0_4)
    (OscCover.leaf 7 15 0 4 oscLeaf_7_15_0_4))
    (OscCover.leaf 0 15 4 8 oscLeaf_0_15_4_8))
    (OscCover.splitT 0 15 8 12 16
    (OscCover.splitP 0 7 15 8 12
    (OscCover.leaf 0 7 8 12 oscLeaf_0_7_8_12)
    (OscCover.leaf 7 15 8 12 oscLeaf_7_15_8_12))
    (OscCover.leaf 0 15 12 16 oscLeaf_0_15_12_16)))
    (OscCover.splitT 0 15 16 24 32
    (OscCover.splitT 0 15 16 20 24
    (OscCover.leaf 0 15 16 20 oscLeaf_0_15_16_20)
    (OscCover.leaf 0 15 20 24 oscLeaf_0_15_20_24))
    (OscCover.splitT 0 15 24 28 32
    (OscCover.leaf 0 15 24 28 oscLeaf_0_15_24_28)
    (OscCover.leaf 0 15 28 32 oscLeaf_0_15_28_32))))
    (OscCover.splitT 0 15 32 48 64
    (OscCover.splitT 0 15 32 40 48
    (OscCover.splitT 0 15 32 36 40
    (OscCover.leaf 0 15 32 36 oscLeaf_0_15_32_36)
    (OscCover.leaf 0 15 36 40 oscLeaf_0_15_36_40))
    (OscCover.leaf 0 15 40 48 oscLeaf_0_15_40_48))
    (OscCover.splitT 0 15 48 56 64
    (OscCover.leaf 0 15 48 56 oscLeaf_0_15_48_56)
    (OscCover.leaf 0 15 56 64 oscLeaf_0_15_56_64))))
    (OscCover.splitT 0 15 64 96 128
    (OscCover.splitT 0 15 64 80 96
    (OscCover.splitT 0 15 64 72 80
    (OscCover.leaf 0 15 64 72 oscLeaf_0_15_64_72)
    (OscCover.leaf 0 15 72 80 oscLeaf_0_15_72_80))
    (OscCover.splitT 0 15 80 88 96
    (OscCover.leaf 0 15 80 88 oscLeaf_0_15_80_88)
    (OscCover.leaf 0 15 88 96 oscLeaf_0_15_88_96)))
    (OscCover.splitT 0 15 96 112 128
    (OscCover.splitT 0 15 96 104 112
    (OscCover.leaf 0 15 96 104 oscLeaf_0_15_96_104)
    (OscCover.leaf 0 15 104 112 oscLeaf_0_15_104_112))
    (OscCover.splitT 0 15 112 120 128
    (OscCover.leaf 0 15 112 120 oscLeaf_0_15_112_120)
    (OscCover.leaf 0 15 120 128 oscLeaf_0_15_120_128)))))
    (OscCover.splitT 15 30 0 64 128
    (OscCover.splitT 15 30 0 32 64
    (OscCover.splitT 15 30 0 16 32
    (OscCover.splitT 15 30 0 8 16
    (OscCover.splitT 15 30 0 4 8
    (OscCover.leaf 15 30 0 4 oscLeaf_15_30_0_4)
    (OscCover.leaf 15 30 4 8 oscLeaf_15_30_4_8))
    (OscCover.splitT 15 30 8 12 16
    (OscCover.leaf 15 30 8 12 oscLeaf_15_30_8_12)
    (OscCover.leaf 15 30 12 16 oscLeaf_15_30_12_16)))
    (OscCover.splitT 15 30 16 24 32
    (OscCover.splitT 15 30 16 20 24
    (OscCover.leaf 15 30 16 20 oscLeaf_15_30_16_20)
    (OscCover.leaf 15 30 20 24 oscLeaf_15_30_20_24))
    (OscCover.splitT 15 30 24 28 32
    (OscCover.leaf 15 30 24 28 oscLeaf_15_30_24_28)
    (OscCover.leaf 15 30 28 32 oscLeaf_15_30_28_32))))
    (OscCover.splitT 15 30 32 48 64
    (OscCover.splitT 15 30 32 40 48
    (OscCover.splitT 15 30 32 36 40
    (OscCover.leaf 15 30 32 36 oscLeaf_15_30_32_36)
    (OscCover.leaf 15 30 36 40 oscLeaf_15_30_36_40))
    (OscCover.leaf 15 30 40 48 oscLeaf_15_30_40_48))
    (OscCover.splitT 15 30 48 56 64
    (OscCover.leaf 15 30 48 56 oscLeaf_15_30_48_56)
    (OscCover.leaf 15 30 56 64 oscLeaf_15_30_56_64))))
    (OscCover.splitT 15 30 64 96 128
    (OscCover.splitT 15 30 64 80 96
    (OscCover.splitT 15 30 64 72 80
    (OscCover.leaf 15 30 64 72 oscLeaf_15_30_64_72)
    (OscCover.leaf 15 30 72 80 oscLeaf_15_30_72_80))
    (OscCover.splitT 15 30 80 88 96
    (OscCover.leaf 15 30 80 88 oscLeaf_15_30_80_88)
    (OscCover.leaf 15 30 88 96 oscLeaf_15_30_88_96)))
    (OscCover.splitT 15 30 96 112 128
    (OscCover.splitT 15 30 96 104 112
    (OscCover.leaf 15 30 96 104 oscLeaf_15_30_96_104)
    (OscCover.leaf 15 30 104 112 oscLeaf_15_30_104_112))
    (OscCover.splitT 15 30 112 120 128
    (OscCover.leaf 15 30 112 120 oscLeaf_15_30_112_120)
    (OscCover.leaf 15 30 120 128 oscLeaf_15_30_120_128))))))
    (OscCover.splitP 30 45 60 0 128
    (OscCover.splitT 30 45 0 64 128
    (OscCover.splitT 30 45 0 32 64
    (OscCover.splitT 30 45 0 16 32
    (OscCover.splitT 30 45 0 8 16
    (OscCover.splitT 30 45 0 4 8
    (OscCover.leaf 30 45 0 4 oscLeaf_30_45_0_4)
    (OscCover.leaf 30 45 4 8 oscLeaf_30_45_4_8))
    (OscCover.splitT 30 45 8 12 16
    (OscCover.leaf 30 45 8 12 oscLeaf_30_45_8_12)
    (OscCover.leaf 30 45 12 16 oscLeaf_30_45_12_16)))
    (OscCover.splitT 30 45 16 24 32
    (OscCover.leaf 30 45 16 24 oscLeaf_30_45_16_24)
    (OscCover.leaf 30 45 24 32 oscLeaf_30_45_24_32)))
    (OscCover.splitT 30 45 32 48 64
    (OscCover.splitT 30 45 32 40 48
    (OscCover.leaf 30 45 32 40 oscLeaf_30_45_32_40)
    (OscCover.leaf 30 45 40 48 oscLeaf_30_45_40_48))
    (OscCover.splitT 30 45 48 56 64
    (OscCover.leaf 30 45 48 56 oscLeaf_30_45_48_56)
    (OscCover.leaf 30 45 56 64 oscLeaf_30_45_56_64))))
    (OscCover.splitT 30 45 64 96 128
    (OscCover.splitT 30 45 64 80 96
    (OscCover.splitT 30 45 64 72 80
    (OscCover.leaf 30 45 64 72 oscLeaf_30_45_64_72)
    (OscCover.leaf 30 45 72 80 oscLeaf_30_45_72_80))
    (OscCover.splitT 30 45 80 88 96
    (OscCover.leaf 30 45 80 88 oscLeaf_30_45_80_88)
    (OscCover.leaf 30 45 88 96 oscLeaf_30_45_88_96)))
    (OscCover.splitT 30 45 96 112 128
    (OscCover.splitT 30 45 96 104 112
    (OscCover.leaf 30 45 96 104 oscLeaf_30_45_96_104)
    (OscCover.leaf 30 45 104 112 oscLeaf_30_45_104_112))
    (OscCover.splitT 30 45 112 120 128
    (OscCover.leaf 30 45 112 120 oscLeaf_30_45_112_120)
    (OscCover.leaf 30 45 120 128 oscLeaf_30_45_120_128)))))
    (OscCover.splitT 45 60 0 64 128
    (OscCover.splitT 45 60 0 32 64
    (OscCover.splitT 45 60 0 16 32
    (OscCover.splitT 45 60 0 8 16
    (OscCover.leaf 45 60 0 8 oscLeaf_45_60_0_8)
    (OscCover.leaf 45 60 8 16 oscLeaf_45_60_8_16))
    (OscCover.splitT 45 60 16 24 32
    (OscCover.leaf 45 60 16 24 oscLeaf_45_60_16_24)
    (OscCover.leaf 45 60 24 32 oscLeaf_45_60_24_32)))
    (OscCover.splitT 45 60 32 48 64
    (OscCover.splitT 45 60 32 40 48
    (OscCover.leaf 45 60 32 40 oscLeaf_45_60_32_40)
    (OscCover.leaf 45 60 40 48 oscLeaf_45_60_40_48))
    (OscCover.splitT 45 60 48 56 64
    (OscCover.leaf 45 60 48 56 oscLeaf_45_60_48_56)
    (OscCover.leaf 45 60 56 64 oscLeaf_45_60_56_64))))
    (OscCover.splitT 45 60 64 96 128
    (OscCover.splitT 45 60 64 80 96
    (OscCover.splitT 45 60 64 72 80
    (OscCover.leaf 45 60 64 72 oscLeaf_45_60_64_72)
    (OscCover.leaf 45 60 72 80 oscLeaf_45_60_72_80))
    (OscCover.splitT 45 60 80 88 96
    (OscCover.leaf 45 60 80 88 oscLeaf_45_60_80_88)
    (OscCover.leaf 45 60 88 96 oscLeaf_45_60_88_96)))
    (OscCover.splitT 45 60 96 112 128
    (OscCover.leaf 45 60 96 112 oscLeaf_45_60_96_112)
    (OscCover.leaf 45 60 112 128 oscLeaf_45_60_112_128))))))
    (OscCover.splitP 60 90 120 0 128
    (OscCover.splitP 60 75 90 0 128
    (OscCover.splitT 60 75 0 64 128
    (OscCover.splitT 60 75 0 32 64
    (OscCover.splitT 60 75 0 16 32
    (OscCover.splitT 60 75 0 8 16
    (OscCover.leaf 60 75 0 8 oscLeaf_60_75_0_8)
    (OscCover.leaf 60 75 8 16 oscLeaf_60_75_8_16))
    (OscCover.splitT 60 75 16 24 32
    (OscCover.leaf 60 75 16 24 oscLeaf_60_75_16_24)
    (OscCover.leaf 60 75 24 32 oscLeaf_60_75_24_32)))
    (OscCover.splitT 60 75 32 48 64
    (OscCover.splitT 60 75 32 40 48
    (OscCover.leaf 60 75 32 40 oscLeaf_60_75_32_40)
    (OscCover.leaf 60 75 40 48 oscLeaf_60_75_40_48))
    (OscCover.splitT 60 75 48 56 64
    (OscCover.leaf 60 75 48 56 oscLeaf_60_75_48_56)
    (OscCover.leaf 60 75 56 64 oscLeaf_60_75_56_64))))
    (OscCover.splitT 60 75 64 96 128
    (OscCover.splitT 60 75 64 80 96
    (OscCover.splitT 60 75 64 72 80
    (OscCover.leaf 60 75 64 72 oscLeaf_60_75_64_72)
    (OscCover.leaf 60 75 72 80 oscLeaf_60_75_72_80))
    (OscCover.splitT 60 75 80 88 96
    (OscCover.leaf 60 75 80 88 oscLeaf_60_75_80_88)
    (OscCover.leaf 60 75 88 96 oscLeaf_60_75_88_96)))
    (OscCover.splitT 60 75 96 112 128
    (OscCover.leaf 60 75 96 112 oscLeaf_60_75_96_112)
    (OscCover.leaf 60 75 112 128 oscLeaf_60_75_112_128))))
    (OscCover.splitT 75 90 0 64 128
    (OscCover.splitT 75 90 0 32 64
    (OscCover.splitT 75 90 0 16 32
    (OscCover.splitT 75 90 0 8 16
    (OscCover.leaf 75 90 0 8 oscLeaf_75_90_0_8)
    (OscCover.leaf 75 90 8 16 oscLeaf_75_90_8_16))
    (OscCover.splitT 75 90 16 24 32
    (OscCover.leaf 75 90 16 24 oscLeaf_75_90_16_24)
    (OscCover.leaf 75 90 24 32 oscLeaf_75_90_24_32)))
    (OscCover.splitT 75 90 32 48 64
    (OscCover.splitT 75 90 32 40 48
    (OscCover.leaf 75 90 32 40 oscLeaf_75_90_32_40)
    (OscCover.leaf 75 90 40 48 oscLeaf_75_90_40_48))
    (OscCover.splitT 75 90 48 56 64
    (OscCover.leaf 75 90 48 56 oscLeaf_75_90_48_56)
    (OscCover.leaf 75 90 56 64 oscLeaf_75_90_56_64))))
    (OscCover.splitT 75 90 64 96 128
    (OscCover.splitT 75 90 64 80 96
    (OscCover.leaf 75 90 64 80 oscLeaf_75_90_64_80)
    (OscCover.splitT 75 90 80 88 96
    (OscCover.leaf 75 90 80 88 oscLeaf_75_90_80_88)
    (OscCover.leaf 75 90 88 96 oscLeaf_75_90_88_96)))
    (OscCover.splitT 75 90 96 112 128
    (OscCover.leaf 75 90 96 112 oscLeaf_75_90_96_112)
    (OscCover.leaf 75 90 112 128 oscLeaf_75_90_112_128)))))
    (OscCover.splitP 90 105 120 0 128
    (OscCover.splitT 90 105 0 64 128
    (OscCover.splitT 90 105 0 32 64
    (OscCover.splitT 90 105 0 16 32
    (OscCover.splitT 90 105 0 8 16
    (OscCover.leaf 90 105 0 8 oscLeaf_90_105_0_8)
    (OscCover.leaf 90 105 8 16 oscLeaf_90_105_8_16))
    (OscCover.splitT 90 105 16 24 32
    (OscCover.leaf 90 105 16 24 oscLeaf_90_105_16_24)
    (OscCover.leaf 90 105 24 32 oscLeaf_90_105_24_32)))
    (OscCover.splitT 90 105 32 48 64
    (OscCover.splitT 90 105 32 40 48
    (OscCover.leaf 90 105 32 40 oscLeaf_90_105_32_40)
    (OscCover.leaf 90 105 40 48 oscLeaf_90_105_40_48))
    (OscCover.splitT 90 105 48 56 64
    (OscCover.leaf 90 105 48 56 oscLeaf_90_105_48_56)
    (OscCover.leaf 90 105 56 64 oscLeaf_90_105_56_64))))
    (OscCover.splitT 90 105 64 96 128
    (OscCover.splitT 90 105 64 80 96
    (OscCover.leaf 90 105 64 80 oscLeaf_90_105_64_80)
    (OscCover.leaf 90 105 80 96 oscLeaf_90_105_80_96))
    (OscCover.splitT 90 105 96 112 128
    (OscCover.leaf 90 105 96 112 oscLeaf_90_105_96_112)
    (OscCover.leaf 90 105 112 128 oscLeaf_90_105_112_128))))
    (OscCover.splitT 105 120 0 64 128
    (OscCover.splitT 105 120 0 32 64
    (OscCover.splitT 105 120 0 16 32
    (OscCover.splitT 105 120 0 8 16
    (OscCover.leaf 105 120 0 8 oscLeaf_105_120_0_8)
    (OscCover.leaf 105 120 8 16 oscLeaf_105_120_8_16))
    (OscCover.splitT 105 120 16 24 32
    (OscCover.leaf 105 120 16 24 oscLeaf_105_120_16_24)
    (OscCover.leaf 105 120 24 32 oscLeaf_105_120_24_32)))
    (OscCover.splitT 105 120 32 48 64
    (OscCover.splitT 105 120 32 40 48
    (OscCover.leaf 105 120 32 40 oscLeaf_105_120_32_40)
    (OscCover.leaf 105 120 40 48 oscLeaf_105_120_40_48))
    (OscCover.leaf 105 120 48 64 oscLeaf_105_120_48_64)))
    (OscCover.splitT 105 120 64 96 128
    (OscCover.splitT 105 120 64 80 96
    (OscCover.leaf 105 120 64 80 oscLeaf_105_120_64_80)
    (OscCover.leaf 105 120 80 96 oscLeaf_105_120_80_96))
    (OscCover.splitT 105 120 96 112 128
    (OscCover.leaf 105 120 96 112 oscLeaf_105_120_96_112)
    (OscCover.leaf 105 120 112 128 oscLeaf_105_120_112_128)))))))

/-! ## Main results -/

/-- `sin Δ ≥ 3/5` on `[1.70, 2.49]`. -/
theorem sin_ge_of_mem {Δ : ℝ} (h1 : 170 / 100 ≤ Δ) (h2 : Δ ≤ 249 / 100) : 3 / 5 ≤ sin Δ := by
  have hpi1 := pi_gt_d6
  have hpi2 := pi_lt_d2
  rw [← sin_pi_sub]
  have hle : sin (6515 / 10000) ≤ sin (π - Δ) :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have := sin_ge_sub_cube (x := 6515 / 10000) (by norm_num)
  norm_num at this
  linarith

/-- **Certified oscillatory kick integrals of exact-QA reference bounces.** Every orbit of the
setting `Setup` (start window `ψ₀ ∈ [4.75, 5.79]`, pitch window `E/μ ∈ [5.4, 5.5]`, `T ≥ 1.6 ms`)
closes its bounce at a time `P ∈ [59, 72] μs` (RK4: `63.6–66.6`) with `ρ(P) = 0`,
`(ψ, θ)(P) = (ψ, θ)(0)`, precession `Δ = φ(P) − φ(0) ∈ [1.70, 2.49]` (RK4: `1.88–2.31`),
`sin Δ ≥ 3/5`, and the normalised kick integrals `Ĉ = ∫₀ᴾ A w cos 2(φ − φ₀)`,
`Ŝ = ∫₀ᴾ A w sin 2(φ − φ₀)` (`A = μ/q + qρ²B/m`, `w = 2ψ/B₀`) satisfy `√(Ĉ² + Ŝ²) ≤ 40 sin Δ`
(RK4: `√(Ĉ² + Ŝ²)/sin Δ ≈ 11`; the previous bound `2 ∫ A w ≤ 116` ignored the oscillation). -/
theorem exactQA_kick_osc {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 59 / 10 ^ 6 ≤ P ∧ P ≤ 72 / 10 ^ 6 ∧ ρ P = 0 ∧ ψ P = ψ 0 ∧ θ P = θ 0 ∧
      φ P - φ 0 ∈ Icc (170 / 100 : ℝ) (249 / 100) ∧ 3 / 5 ≤ sin (φ P - φ 0) ∧
      √((∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (20 / 57 * ψ t) * cos (2 * (φ t - φ 0))) ^ 2 +
        (∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (20 / 57 * ψ t) * sin (2 * (φ t - φ 0))) ^ 2) ≤ 40 * sin (φ P - φ 0) := by
  obtain ⟨P, -, hPmin, hPmax, -, hρP, hψP, hθP, -, hD1, hD2, hK⟩ :=
    exactQA_kick_osc_of_cover osc_cover S hT
  have hΔ : φ P - φ 0 ∈ Icc (170 / 100 : ℝ) (249 / 100) := by
    simp only [fxVal, fxScale] at hD1 hD2
    constructor <;> norm_num at hD1 hD2 ⊢ <;> linarith
  have hPmin' : (59 : ℝ) / 10 ^ 6 ≤ P := by push_cast at hPmin; exact hPmin
  have hPmax' : P ≤ (72 : ℝ) / 10 ^ 6 := by push_cast at hPmax; exact hPmax
  refine ⟨P, hPmin', hPmax', hρP, hψP, hθP, hΔ, sin_ge_of_mem hΔ.1 hΔ.2, by exact_mod_cast hK⟩

/-- **The oscillatory amplitude constant** of `reactorQA` (`|b₁| = 4.3 × 10⁻⁴`) in flux units:
`2 |b₁| · 40/ι₀ ≤ 0.0816 T m²`. -/
theorem osc_amplitude_le : 2 * (43 / 100000 : ℝ) * 40 / (211 / 500) ≤ 816 / 10000 := by
  norm_num

/-- **Reference kick data of `reactorQA` with the certified oscillatory amplitude.** For every
exact-QA reference orbit of the start window (`Setup`, `T ≥ 1.6 ms`) and the symmetry-breaking
coefficient `b₁ = −4.3 × 10⁻⁴` of `reactorQA`, the bounce closes at `P ∈ [59, 72] μs` with
`Δ = φ(P) − φ(0) ∈ [1.70, 2.49]`, `sin Δ ≥ 3/5`, the reference kick decomposes as
`∫₀ᴾ g sin 2φ = C sin 2φ(0) + S cos 2φ(0)` (`g = refAmp b₁`), and in flux units
`√(C² + S²)/(q ι₀ sin Δ) ≤ 0.0816 T m²`; in particular `|C/(q ι₀ sin Δ)|, |S/(q ι₀ sin Δ)| ≤ 0.0816`
(previously certified: `0.2364`; RK4: `0.023`). -/
theorem reference_kick_osc {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 59 / 10 ^ 6 ≤ P ∧ P ≤ 72 / 10 ^ 6 ∧ ρ P = 0 ∧ ψ P = ψ 0 ∧ θ P = θ 0 ∧
      φ P - φ 0 ∈ Icc (170 / 100 : ℝ) (249 / 100) ∧ 3 / 5 ≤ sin (φ P - φ 0) ∧
      (∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * sin (2 * φ t)) =
        (∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * cos (2 * (φ t - φ 0))) *
            sin (2 * φ 0) +
          (∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * sin (2 * (φ t - φ 0))) *
            cos (2 * φ 0) ∧
      √((∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * cos (2 * (φ t - φ 0))) ^ 2 +
        (∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * sin (2 * (φ t - φ 0))) ^ 2) /
          (qα * (211 / 500) * sin (φ P - φ 0)) ≤ 816 / 10000 ∧
      |(∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * cos (2 * (φ t - φ 0))) /
          (qα * (211 / 500) * sin (φ P - φ 0))| ≤ 816 / 10000 ∧
      |(∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * sin (2 * (φ t - φ 0))) /
          (qα * (211 / 500) * sin (φ P - φ 0))| ≤ 816 / 10000 := by
  obtain ⟨P, -, hPmin, hPmax, -, hρP, hψP, hθP, -, hD1, hD2, hdec, hK⟩ :=
    reference_kick_osc_of_cover osc_cover (-43 / 100000) S hT
  have hΔ : φ P - φ 0 ∈ Icc (170 / 100 : ℝ) (249 / 100) := by
    simp only [fxVal, fxScale] at hD1 hD2
    constructor <;> norm_num at hD1 hD2 ⊢ <;> linarith
  have hs := sin_ge_of_mem hΔ.1 hΔ.2
  set Cr := ∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * cos (2 * (φ t - φ 0))
  set Sr := ∫ t in (0 : ℝ)..P, refAmp (-43 / 100000) μ ψ θ ρ t * sin (2 * (φ t - φ 0))
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hden : 0 < qα * (211 / 500) * sin (φ P - φ 0) := by positivity
  have hmain : √(Cr ^ 2 + Sr ^ 2) / (qα * (211 / 500) * sin (φ P - φ 0)) ≤ 816 / 10000 := by
    rw [div_le_iff₀ hden]
    have hK' : √(Cr ^ 2 + Sr ^ 2) ≤ 2 * (43 / 100000) * qα * 40 * sin (φ P - φ 0) := by
      have := hK; rw [abs_of_neg (by norm_num : (-43 / 100000 : ℝ) < 0)] at this
      norm_num at this ⊢; linarith
    have : 2 * (43 / 100000) * qα * 40 * sin (φ P - φ 0) ≤
        816 / 10000 * (qα * (211 / 500) * sin (φ P - φ 0)) := by
      have h0 : 0 ≤ qα * sin (φ P - φ 0) := by positivity
      nlinarith
    linarith
  have hCle : |Cr| ≤ √(Cr ^ 2 + Sr ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Sr])
  have hSle : |Sr| ≤ √(Cr ^ 2 + Sr ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Cr])
  have hPmin' : (59 : ℝ) / 10 ^ 6 ≤ P := by push_cast at hPmin; exact hPmin
  have hPmax' : P ≤ (72 : ℝ) / 10 ^ 6 := by push_cast at hPmax; exact hPmax
  refine ⟨P, hPmin', hPmax', hρP, hψP, hθP, hΔ, hs, hdec, hmain, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hden]
    exact (div_le_div_of_nonneg_right hCle hden.le).trans hmain
  · rw [abs_div, abs_of_pos hden]
    exact (div_le_div_of_nonneg_right hSle hden.le).trans hmain

/-! ## The re-anchored budget with the certified amplitude -/

/-- **With crude shears the re-anchored gap fails for every `N ≥ 1`.** With the certified
amplitude `M = 0.0816`, the crude precession shear `σ = 2.49 − 1.70 = 0.79` (any two anchors of
the window, `exactQA_kick_osc`) and the crude amplitude shear `γ = 2M`, the hypothesis of
`reactorQA_trapped_reanchored` fails for every `N ≥ 1`, all `R, e ≥ 0` and every start `ψ₀`:
`4M + γ + Mσ = 0.554 > 0.52`. -/
theorem osc_crude_shears_fail {ψ₀ R e : ℝ} {N : ℕ} (hN : 1 ≤ N) (hR : 0 ≤ R) (he : 0 ≤ e) :
    ¬ (2 * (816 / 10000) + N * (R + 2 * (816 / 10000) + 816 / 10000 * (e + 79 / 100)) +
      (2 * (816 / 10000) + R) ≤ min (ψ₀ - 475 / 100) (579 / 100 - ψ₀)) := by
  intro h
  have hmin : min (ψ₀ - 475 / 100) (579 / 100 - ψ₀) ≤ 52 / 100 := by
    rcases le_total (ψ₀ - 475 / 100) (579 / 100 - ψ₀) with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : 0 ≤ R + 2 * (816 / 10000) + 816 / 10000 * (e + 79 / 100) := by positivity
  nlinarith

/-- **The exact requirement on the one-bounce remainders** (from `ψ₀ = 5.27`, gap `0.52`): with
`M = 0.0816` the hypothesis `hgap` of `reactorQA_trapped_reanchored` for `N` bounces reads
`0.3264 + R + N (R + γ + 0.0816 (e + σ)) ≤ 0.52`. With the simulated shears
`σ = 0.0076`, `γ = 7 × 10⁻⁴` (RK4) and the simulated remainders `R = 2.1 × 10⁻⁴`,
`e = 0.0141`, it closes for `N = 72` bounces; with the certified period floor `59 μs` this is a
reference-time span of at least `72 · 59 μs = 4.2 ms` (the actual inter-tip times differ from the
reference periods by a further one-bounce remainder). -/
theorem osc_budget_simulated :
    2 * (816 / 10000 : ℝ) + 72 * (21 / 100000 + 7 / 10000 + 816 / 10000 * (141 / 10000 +
      76 / 10000)) + (2 * (816 / 10000) + 21 / 100000) ≤
      min ((527 : ℝ) / 100 - 475 / 100) (579 / 100 - 527 / 100) ∧
    (72 : ℝ) * (59 / 10 ^ 6) ≥ 42 / 10000 := by
  norm_num

/-- **The conserved-quantity comparison is far too weak for `R`.** Over one bounce
(`P ≤ 72 μs`) the worst-case drift of the helical momentum of a `reactorQA` orbit
(`helicalMomentum_drift_le`, `ε_QS = 0.0024854 T`, `B ≥ 4.93 T`) bounds the change of the tip flux
only by `(2E/(q B_min)) ε_QS P/ι₀ ≥ 0.30 T m²`, while `N = 72` bounces (with the simulated shears)
need `R ≤ 0.0027`; even `N = 1` needs `R ≤ 0.096`. -/
theorem conserved_quantity_insufficient :
    (3 / 10 : ℝ) ≤ 2 * Eα / (qα * (493 / 100)) * 0.0024854 * (72 / 10 ^ 6) / (211 / 500) ∧
      (52 / 100 - 2 * (2 * (816 / 10000)) : ℝ) / 73 < 27 / 10000 ∧
      (52 / 100 - 2 * (2 * (816 / 10000)) : ℝ) / 2 < 97 / 1000 := by
  norm_num [Eα, qα]

end PlasmaLean.Design.NearAxisQATrappedOsc
