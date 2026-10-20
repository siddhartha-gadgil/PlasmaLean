/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.BurnWindowScaling
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Model rung M1 for a Stellaris-scale stellarator under ISS04

This module is the stellarator counterpart of `Design.BurnWindowScaling`. It gives a 0-D burn
window for a **synthetic, Stellaris-scale** quasi-isodynamic stellarator. The confinement time
follows the **ISS04** scaling (H. Yamada et al., *Characterization of energy confinement in
net-current free plasmas using the extended International Stellarator Database*, Nucl. Fusion
**45** (2005) 1684):
`τ_E = f_ren · 0.134 a^2.28 R^0.64 P^−0.61 n̄₁₉^0.54 B^0.84 ι_{2/3}^0.41`.
The configuration-dependent renormalization factor `f_ren` plays the role of the enhancement
factor `H` in `SteadyScaling`/`LossScaling`.

## Machine (*synthetic data at Stellaris scale*)

Geometry is from the Stellaris design: A. Lion et al., Fusion Eng. Des. **214** (2025) 114868,
with parameters as quoted in arXiv:2507.12681. See `notes/theory/stellarator-burn-parameters.md`.

* `a = 1.3 m`, `R = 12.7 m`, `B = 9 T`.
* `ι_{2/3} = 0.9` is an **explicit assumption**. It is not a published Stellaris value.
* `n̄ = 1.5 × 10²⁰ m⁻³` (`n₁₉ = 15`) with flat profiles, so line average = volume average.
* `V = 425 m³` (`stellarisPlasma`). `stellaris_torus_volume` proves that `2π²Ra²` lies in
  `[423.6, 423.7]` m³, which is within 0.4 % of 425.
* Carbon impurity with `Z_eff = 1.7`. The kernel's single-impurity model gives `f_fuel = 0.86`
  and `r_i = 53/60` (`stellarisPlasma_carbon`).
* The ISS04 coefficient is enclosed as `32.45 ≤ C ≤ 32.46` s·MW^0.61
  (`stellaris_coeff_bounds`).

## Confinement assumption (read this first)

The window theorems assume **`f_ren ∈ [1.55, 1.75]`**. This is **above** every value measured on
W7-X:
* `f_ren ≈ 1` in OP1.1 (Fuchert et al., NF 2018);
* transiently about 1.3–1.4 after pellet injection (Bozhenkov et al., NF 60 (2020) 066011) and
  in OP2.

It is also above the 1-D predictive extrapolation to reactor size (`f_ren ≈ 1.1–1.3`, Warmer et
al., FST 68 (2015)). So it is an **assumption that confinement improves** (QI optimization,
high field). It is not an extrapolation of data. The flat 0-D model also understates the fusion
power at 10 keV by about 1.6× compared with peaked profiles. A 1-D (M2) version should therefore
need less (this is a numerical observation from the note, not a theorem).

## Results

For every trajectory satisfying the kernel balance law, the supplied Bosch–Hale facts and the
ISS04 law (no other `τ_E` hypothesis):

* `stellaris_window_steady`, `stellaris_window_loss`: assume `50 MW ≤ P_aux ≤ 70 MW` and
  `f_ren(t) ∈ [1.55, 1.75]`. Then `T(0) ∈ [10, 22]` keV implies `T(t) ∈ [10, 22]` keV for all
  `t ≥ 0`. The two crossing certificates are:
  * `lower_numeric`: at 10 keV, heating power `161.4 MW` and `f_ren = 1.55` give net heating
    `≈ +6.4 MW`;
  * `upper_numeric`: at 22 keV, heating power `560.4 MW` and `f_ren = 1.75` give net heating
    `≈ −11 MW`.
* `stellaris_fusion_yield`: the fusion energy over `[0, t_b]` is at least `5.6 × 10⁸ W · t_b`.
* `stellaris_measured_fren_no_access_steady` / `_loss` (**obstruction, proved**): at the
  measured confinement level `f_ren ≤ 1.3` with `0 ≤ P_aux ≤ 70 MW`, the net heating at
  10 keV is negative (`≈ −8 MW` at heating power 184 MW). So `T(0) ≤ 10 keV` implies
  `T(t) ≤ 10 keV`: the window cannot be reached from below.
* `stellaris_satisfiable`: for **every** supplied Bosch–Hale reactivity, a constant 18 keV
  state with `P_aux = 60 MW` and an explicit `f_ren* ∈ [1.55, 1.75]` (in fact
  `1.61 ≤ f_ren* ≤ 1.68`) satisfies the balance law and both scaling classes. **The crossing
  hypotheses are vacuous for this witness**, because it never reaches 10 or 22 keV.

The value `P_fus(22 keV) ≈ 2.46 GW` and `β(22 keV) ≈ 3.1 %` come from a floating-point
evaluation (numerical observation, not a Lean theorem).
-/

public section
noncomputable section

namespace PlasmaLean.Design.BurnWindowStellarator

open PlasmaLean.Fusion DTPlasma PlasmaLean.Design.BurnWindow PlasmaLean.Design.BurnWindowScaling

/-- Stellaris-scale ISS04 parameters (synthetic): `a = 1.3 m`, `R = 12.7 m`, `B = 9 T`,
`n₁₉ = 15`, and **assumed** `ι_{2/3} = 0.9`. -/
@[expose] def stellarisParams : StellaratorParams := ⟨1.3, 12.7, 9, 15, 0.9⟩

/-- The ISS04 law (Yamada et al., Nucl. Fusion 45 (2005) 1684) for `stellarisParams`.
Its enhancement factor `H` is the renormalization factor `f_ren`. -/
@[expose] def stellarisLaw : ConfinementLaw := stellarisParams.iss04

/-- The Stellaris-scale ISS04 law is admissible (`C > 0`, `α = 0.61`). -/
instance stellarisLaw_admissible : stellarisLaw.Admissible :=
  stellarisParams.iss04_admissible (by norm_num [stellarisParams])
    (by norm_num [stellarisParams]) (by norm_num [stellarisParams])
    (by norm_num [stellarisParams]) (by norm_num [stellarisParams])

/-- The ISS04 power exponent. -/
theorem stellarisLaw_α : stellarisLaw.α = 0.61 := rfl

/-- **Enclosure of the ISS04 coefficient** for `stellarisParams`:
`32.45 ≤ C ≤ 32.46` (s · MW^0.61). -/
theorem stellaris_coeff_bounds : 32.45 ≤ stellarisLaw.C ∧ stellarisLaw.C ≤ 32.46 := by
  have hC : stellarisLaw.C = 0.134 * (1.3 : ℝ) ^ (2.28 : ℝ) * (12.7 : ℝ) ^ (0.64 : ℝ) *
      (15 : ℝ) ^ (0.54 : ℝ) * (9 : ℝ) ^ (0.84 : ℝ) * (0.9 : ℝ) ^ (0.41 : ℝ) := rfl
  have l1 : (1.81882 : ℝ) ≤ (1.3 : ℝ) ^ (2.28 : ℝ) :=
    rpow_lb 228 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u1 : (1.3 : ℝ) ^ (2.28 : ℝ) ≤ 1.81883 :=
    rpow_ub 228 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l2 : (5.08667 : ℝ) ≤ (12.7 : ℝ) ^ (0.64 : ℝ) :=
    rpow_lb 64 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u2 : (12.7 : ℝ) ^ (0.64 : ℝ) ≤ 5.08668 :=
    rpow_ub 64 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l3 : (4.31607 : ℝ) ≤ (15 : ℝ) ^ (0.54 : ℝ) :=
    rpow_lb 54 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u3 : (15 : ℝ) ^ (0.54 : ℝ) ≤ 4.31608 :=
    rpow_ub 54 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l4 : (6.33233 : ℝ) ≤ (9 : ℝ) ^ (0.84 : ℝ) :=
    rpow_lb 84 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u4 : (9 : ℝ) ^ (0.84 : ℝ) ≤ 6.33234 :=
    rpow_ub 84 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l5 : (0.95772 : ℝ) ≤ (0.9 : ℝ) ^ (0.41 : ℝ) :=
    rpow_lb 41 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u5 : (0.9 : ℝ) ^ (0.41 : ℝ) ≤ 0.95773 :=
    rpow_ub 41 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hC]
  constructor
  · calc (32.45 : ℝ) ≤ 0.134 * 1.81882 * 5.08667 * 4.31607 * 6.33233 * 0.95772 := by norm_num
      _ ≤ _ := by gcongr
  · calc _ ≤ (0.134 : ℝ) * 1.81883 * 5.08668 * 4.31608 * 6.33234 * 0.95773 := by gcongr
      _ ≤ 32.46 := by norm_num

/-- **Torus volume.** For `R = 12.7 m` and `a = 1.3 m` (circular cross-section),
`2π²Ra² ∈ [423.6, 423.7]` m³. This justifies the rounded `V = 425 m³` to within 0.4 %. -/
theorem stellaris_torus_volume :
    423.6 ≤ 2 * Real.pi ^ 2 * 12.7 * (1.3 : ℝ) ^ 2 ∧
      2 * Real.pi ^ 2 * 12.7 * (1.3 : ℝ) ^ 2 ≤ 423.7 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  constructor <;> nlinarith

/-- The Stellaris-scale 0-D plasma: `n_e = 1.5 × 10²⁰ m⁻³`, `V = 425 m³`, `Z_eff = 1.7` from a
carbon impurity, hence `f_fuel = 0.86` and `r_i = 53/60`. -/
@[expose] def stellarisPlasma : DTPlasma := ⟨1.5e20, 425, 1.7, 0.86, 53 / 60⟩

/-- The fuel fraction and ion ratio are the single-carbon-impurity (`Z = 6`) values of the
kernel impurity model. -/
theorem stellarisPlasma_carbon :
    stellarisPlasma.fuelFraction = impurityFuelFraction 1.7 6 ∧
      stellarisPlasma.ionRatio = impurityIonRatio 1.7 6 := by
  constructor <;> norm_num [stellarisPlasma, impurityIonRatio, impurityFuelFraction]

/-- The plasma density matches the ISS04 density parameter: `n = n₁₉ · 10¹⁹`. -/
theorem stellarisPlasma_density : stellarisPlasma.n = stellarisParams.n19 * 1e19 := by
  norm_num [stellarisPlasma, stellarisParams]

/-- The Stellaris-scale data are physical. -/
instance : PhysicalPlasma stellarisPlasma where
  n_pos := by norm_num [stellarisPlasma]
  V_pos := by norm_num [stellarisPlasma]
  Zeff_ge_one := by norm_num [stellarisPlasma]
  fuel_pos := by norm_num [stellarisPlasma]
  fuel_le_ions := by norm_num [stellarisPlasma]
  ions_le_one := by norm_num [stellarisPlasma]

/-- Explicit thermal energy (J) at `x` keV. -/
theorem st_W (x : ℝ) :
    stellarisPlasma.thermalEnergy x =
      3 / 2 * 1.5e20 * (1 + 53 / 60) * (x * 1.602176634e-16) * 425 := by
  simp only [thermalEnergy, stellarisPlasma, keV]

/-- Explicit bremsstrahlung (W) at `x` keV. -/
theorem st_brems (x : ℝ) :
    stellarisPlasma.bremsPower x = 5.35e-37 * (1.5e20 : ℝ) ^ 2 * 1.7 * Real.sqrt x * 425 := by
  simp only [bremsPower, stellarisPlasma, bremsCoeff]

/-- Explicit alpha power (W) at `x` keV. -/
theorem st_alpha (sv : ℝ → ℝ) (x : ℝ) :
    stellarisPlasma.alphaPower sv x =
      3500 * 1.602176634e-16 / 4 * (0.86 * 1.5e20 : ℝ) ^ 2 * sv x * 425 := by
  simp only [alphaPower, stellarisPlasma, alphaEnergy, keV]

/-- **Lower-crossing certificate at 10 keV.** With heating power `161.4 MW` and
`f_ren = 1.55`, `161.4 MW − P_br(10) − W(10)/τ_ISS04 > 0` (≈ +6.4 MW). Uses
`161.4^0.61 ≤ 22.224` and `C ≥ 32.45`. -/
theorem lower_numeric :
    0 < 161.4e6 - stellarisPlasma.bremsPower 10 -
      stellarisPlasma.lossPower (stellarisLaw.tau 1.55 161.4e6) 10 := by
  have hu : ((161.4e6 : ℝ) / 1e6) ^ stellarisLaw.α ≤ 22.224 :=
    rpow_ub 61 _ (by norm_num [stellarisLaw_α]) (by norm_num) (by norm_num) (by norm_num)
  have hC := stellaris_coeff_bounds.1
  have hW : 0 ≤ stellarisPlasma.thermalEnergy 10 := thermalEnergy_nonneg _ (by norm_num)
  have h1 := loss_le_of_rpow_le (C := stellarisLaw.C) hW (by norm_num : (0 : ℝ) < 1.55)
    (by linarith) (by norm_num : (0 : ℝ) < 161.4e6 / 1e6) hu
  have h2 : stellarisPlasma.thermalEnergy 10 * 22.224 / (1.55 * stellarisLaw.C) ≤
      stellarisPlasma.thermalEnergy 10 * 22.224 / (1.55 * 32.45) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hs : Real.sqrt 10 ≤ 3.1623 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hX : stellarisPlasma.lossPower (stellarisLaw.tau 1.55 161.4e6) 10 ≤
      stellarisPlasma.thermalEnergy 10 * 22.224 / (1.55 * 32.45) := by
    unfold lossPower ConfinementLaw.tau; exact h1.trans h2
  have hb : stellarisPlasma.bremsPower 10 ≤ 27.51e6 := by rw [st_brems]; norm_num; nlinarith
  rw [st_W] at hX; norm_num at hX; linarith

/-- **Upper-crossing certificate at 22 keV.** With heating power `560.4 MW` and
`f_ren = 1.75`, `560.4 MW − P_br(22) − W(22)/τ_ISS04 < 0` (≈ −11 MW). Uses
`560.4^0.61 ≥ 47.487` and `C ≤ 32.46`. -/
theorem upper_numeric :
    560.4e6 - stellarisPlasma.bremsPower 22 -
      stellarisPlasma.lossPower (stellarisLaw.tau 1.75 560.4e6) 22 < 0 := by
  have hl : (47.487 : ℝ) ≤ ((560.4e6 : ℝ) / 1e6) ^ stellarisLaw.α :=
    rpow_lb 61 _ (by norm_num [stellarisLaw_α]) (by norm_num) (by norm_num) (by norm_num)
  have hC := stellaris_coeff_bounds
  have hW : 0 ≤ stellarisPlasma.thermalEnergy 22 := thermalEnergy_nonneg _ (by norm_num)
  have h1 := le_loss_of_le_rpow (C := stellarisLaw.C) hW (by norm_num : (0 : ℝ) < 1.75)
    (by linarith) (by norm_num : (0 : ℝ) < 560.4e6 / 1e6) hl
  have h2 : stellarisPlasma.thermalEnergy 22 * 47.487 / (1.75 * 32.46) ≤
      stellarisPlasma.thermalEnergy 22 * 47.487 / (1.75 * stellarisLaw.C) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hs : 4.690 ≤ Real.sqrt 22 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hX : stellarisPlasma.thermalEnergy 22 * 47.487 / (1.75 * 32.46) ≤
      stellarisPlasma.lossPower (stellarisLaw.tau 1.75 560.4e6) 22 := by
    unfold lossPower ConfinementLaw.tau; exact h2.trans h1
  have hb : 40.78e6 ≤ stellarisPlasma.bremsPower 22 := by rw [st_brems]; norm_num; nlinarith
  rw [st_W] at hX; norm_num at hX; linarith

/-- **Measured-confinement certificate at 10 keV.** With heating power `184 MW` and
`f_ren = 1.3`, `184 MW − P_br(10) − W(10)/τ_ISS04 < 0` (≈ −8 MW). Uses
`184^0.61 ≥ 24.073` and `C ≤ 32.46`. -/
theorem measured_numeric :
    184e6 - stellarisPlasma.bremsPower 10 -
      stellarisPlasma.lossPower (stellarisLaw.tau 1.3 184e6) 10 < 0 := by
  have hl : (24.073 : ℝ) ≤ ((184e6 : ℝ) / 1e6) ^ stellarisLaw.α :=
    rpow_lb 61 _ (by norm_num [stellarisLaw_α]) (by norm_num) (by norm_num) (by norm_num)
  have hC := stellaris_coeff_bounds
  have hW : 0 ≤ stellarisPlasma.thermalEnergy 10 := thermalEnergy_nonneg _ (by norm_num)
  have h1 := le_loss_of_le_rpow (C := stellarisLaw.C) hW (by norm_num : (0 : ℝ) < 1.3)
    (by linarith) (by norm_num : (0 : ℝ) < 184e6 / 1e6) hl
  have h2 : stellarisPlasma.thermalEnergy 10 * 24.073 / (1.3 * 32.46) ≤
      stellarisPlasma.thermalEnergy 10 * 24.073 / (1.3 * stellarisLaw.C) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hs : 3.162 ≤ Real.sqrt 10 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hX : stellarisPlasma.thermalEnergy 10 * 24.073 / (1.3 * 32.46) ≤
      stellarisPlasma.lossPower (stellarisLaw.tau 1.3 184e6) 10 := by
    unfold lossPower ConfinementLaw.tau; exact h2.trans h1
  have hb : 27.49e6 ≤ stellarisPlasma.bremsPower 10 := by rw [st_brems]; norm_num; nlinarith
  rw [st_W] at hX; norm_num at hX; linarith

/-- Supplied reactivity at 22 keV: `⟨σv⟩(22) ≤ 4.946e-22 m³/s` (window `[21, 22]`). -/
theorem sv_twentytwo_le (sv : ℝ → ℝ) [BoschHaleDT sv] : sv 22 ≤ (4.946e-22 : ℝ) := by
  have := (BoschHaleDT.windows (sv := sv) ⟨21, 22, 4.573e-22, 4.946e-22⟩
    (by simp [boschHaleWindows]) 22 (by norm_num) (by norm_num)).2
  norm_num at this ⊢; exact this

/-- Supplied reactivity at 18 keV: `⟨σv⟩(18) ≥ 3.681e-22 m³/s` (window `[18, 19]`). -/
theorem sv_eighteen_ge (sv : ℝ → ℝ) [BoschHaleDT sv] : (3.681e-22 : ℝ) ≤ sv 18 := by
  have := (BoschHaleDT.windows (sv := sv) ⟨18, 19, 3.681e-22, 4.071e-22⟩
    (by simp [boschHaleWindows]) 18 (by norm_num) (by norm_num)).1
  norm_num at this ⊢; exact this

/-- Supplied reactivity at 18 keV: `⟨σv⟩(18) ≤ 3.757e-22 m³/s` (window `[17, 18]`). -/
theorem sv_eighteen_le (sv : ℝ → ℝ) [BoschHaleDT sv] : sv 18 ≤ (3.757e-22 : ℝ) := by
  have := (BoschHaleDT.windows (sv := sv) ⟨17, 18, 3.365e-22, 3.757e-22⟩
    (by simp [boschHaleWindows]) 18 (by norm_num) (by norm_num)).2
  norm_num at this ⊢; exact this

variable {sv Paux τE T H PL : ℝ → ℝ}

/-- Alpha power is nonnegative at nonnegative temperature. -/
theorem st_alpha_nonneg (sv : ℝ → ℝ) [BoschHaleDT sv] {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ stellarisPlasma.alphaPower sv x := by
  have := BoschHaleDT.nonneg (sv := sv) x hx
  rw [st_alpha]; positivity

/-- Heating power at 10 keV with `P_aux ≥ 50 MW` is at least `161.4 MW`. -/
theorem st_heat_ten_ge (sv : ℝ → ℝ) [BoschHaleDT sv] {P : ℝ} (hP : 50e6 ≤ P) :
    161.4e6 ≤ stellarisPlasma.alphaPower sv 10 + P := by
  have := sv_ten_ge sv
  rw [st_alpha]; norm_num; linarith

/-- Heating power at 10 keV with `P_aux ≤ 70 MW` is at most `184 MW`. -/
theorem st_heat_ten_le (sv : ℝ → ℝ) [BoschHaleDT sv] {P : ℝ} (hP : P ≤ 70e6) :
    stellarisPlasma.alphaPower sv 10 + P ≤ 184e6 := by
  have := sv_ten_le sv
  rw [st_alpha]; norm_num; linarith

/-- Heating power at 22 keV with `P_aux ≤ 70 MW` is at most `560.4 MW`. -/
theorem st_heat_twentytwo_le (sv : ℝ → ℝ) [BoschHaleDT sv] {P : ℝ} (hP : P ≤ 70e6) :
    stellarisPlasma.alphaPower sv 22 + P ≤ 560.4e6 := by
  have := sv_twentytwo_le sv
  rw [st_alpha]; norm_num; linarith

/-- **Stellaris-scale burn window from ISS04, steady (heating-power) form.** Consider any
trajectory satisfying the balance law, the supplied Bosch–Hale facts and the ISS04 law with
`P = P_α + P_aux` and **assumed** renormalization `f_ren(t) ∈ [1.55, 1.75]`. If
`50 MW ≤ P_aux ≤ 70 MW`, then `T(0) ∈ [10, 22]` keV implies `T(t) ∈ [10, 22]` keV for all
`t ≥ 0`.

Caveat: `f_ren ∈ [1.55, 1.75]` exceeds the values measured on W7-X (`≈ 1`; transiently
1.3–1.4). It is an assumption of improved (QI, high-field) confinement. Sources: Yamada et
al., NF 45 (2005) 1684 (ISS04); Lion et al., Fusion Eng. Des. 214 (2025) 114868 (Stellaris
geometry); `ι_{2/3} = 0.9` is assumed. -/
theorem stellaris_window_steady [BoschHaleDT sv] [PowerBalance stellarisPlasma sv Paux τE T]
    [SteadyScaling stellarisLaw 1.55 1.75 stellarisPlasma sv Paux τE T H]
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) (h0 : T 0 ∈ Set.Icc 10 22) :
    ∀ t, 0 ≤ t → T t ∈ Set.Icc 10 22 :=
  SteadyScaling.window (L := stellarisLaw) (sv := sv) (Paux := Paux) (τE := τE) (T := T)
    (H := H) (Pmin := 161.4e6) (Pmax := 560.4e6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t ht _ => st_heat_ten_ge sv (hP t ht).1)
    (fun t ht _ => by
      have := st_alpha_nonneg sv (by norm_num : (0 : ℝ) ≤ 22)
      linarith [(hP t ht).1])
    (fun t ht _ => st_heat_twentytwo_le sv (hP t ht).2) lower_numeric upper_numeric h0

/-- **Stellaris-scale burn window from ISS04, loss-power form** (`P = P_α + P_aux − dW/dt`).
Same conclusion, data and caveats as `stellaris_window_steady`. In particular
`f_ren ∈ [1.55, 1.75]` is an assumption above the W7-X measured range. -/
theorem stellaris_window_loss [BoschHaleDT sv] [PowerBalance stellarisPlasma sv Paux τE T]
    [LossScaling stellarisLaw 1.55 1.75 stellarisPlasma sv Paux τE T H PL]
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) (h0 : T 0 ∈ Set.Icc 10 22) :
    ∀ t, 0 ≤ t → T t ∈ Set.Icc 10 22 :=
  LossScaling.window (L := stellarisLaw) (sv := sv) (Paux := Paux) (τE := τE) (T := T)
    (H := H) (PL := PL) (Pmin := 161.4e6) (Pmax := 560.4e6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t ht _ => st_heat_ten_ge sv (hP t ht).1)
    (fun t ht _ => st_heat_twentytwo_le sv (hP t ht).2) lower_numeric upper_numeric h0

/-- **Stellaris-scale burn yield under ISS04** (steady form, assumed
`f_ren ∈ [1.55, 1.75]`): the fusion energy over `[0, t_b]` is at least `5.6 × 10⁸ W · t_b`. -/
theorem stellaris_fusion_yield [BoschHaleDT sv] [PowerBalance stellarisPlasma sv Paux τE T]
    [SteadyScaling stellarisLaw 1.55 1.75 stellarisPlasma sv Paux τE T H]
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) (h0 : T 0 ∈ Set.Icc 10 22) {tb : ℝ}
    (htb : 0 ≤ tb) :
    5.6e8 * tb ≤ ∫ t in (0 : ℝ)..tb, stellarisPlasma.fusionPower sv (T t) := by
  have hwin := stellaris_window_steady (sv := sv) (Paux := Paux) (τE := τE) (T := T) (H := H)
    hP h0
  have hy := PowerBalance.fusion_yield_ge (p := stellarisPlasma) (sv := sv) (Paux := Paux)
    (τE := τE) (T := T) htb (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (22 : ℝ) ≤ 60)
    (fun t ht => hwin t ht.1)
  have hf : 5.6e8 ≤ stellarisPlasma.fusionPower sv 10 := by
    have := sv_ten_ge sv
    simp only [fusionPower, stellarisPlasma, fusionEnergy, keV]
    norm_num; linarith
  nlinarith

/-- Alpha heating at 10 keV is positive. -/
theorem st_alpha_ten_pos (sv : ℝ → ℝ) [BoschHaleDT sv] :
    0 < stellarisPlasma.alphaPower sv 10 := by
  have := sv_ten_ge sv
  rw [st_alpha]; norm_num; linarith

/-- **Obstruction at measured confinement (steady form).** Take the ISS04 law with
`f_ren(t) ∈ [f_lo, 1.3]` (any `f_lo > 0`). This covers the W7-X measured level `f_ren ≈ 1`
and its transient ceiling of about 1.3. With `0 ≤ P_aux ≤ 70 MW`, the net heating at every
crossing of 10 keV is negative. So `T(0) ≤ 10 keV` implies `T(t) ≤ 10 keV` for all `t ≥ 0`:
in this flat 0-D model the 10 keV window cannot be reached at measured confinement. -/
theorem stellaris_measured_fren_no_access_steady [BoschHaleDT sv]
    [PowerBalance stellarisPlasma sv Paux τE T] {flo : ℝ}
    [SteadyScaling stellarisLaw flo 1.3 stellarisPlasma sv Paux τE T H] (hflo : 0 < flo)
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 0 70e6) (h0 : T 0 ≤ 10) :
    ∀ t, 0 ≤ t → T t ≤ 10 :=
  PowerBalance.upper_barrier h0
    (SteadyScaling.upper_crossing (L := stellarisLaw) (Hlo := flo) (Hhi := 1.3) (H := H)
      (τE := τE) (Pmax := 184e6) (by norm_num) hflo
      (fun t ht _ => by linarith [st_alpha_ten_pos sv, (hP t ht).1])
      (fun t ht _ => st_heat_ten_le sv (hP t ht).2) measured_numeric)

/-- **Obstruction at measured confinement (loss-power form).** Same statement as
`stellaris_measured_fren_no_access_steady` for the loss-power convention of ISS04. -/
theorem stellaris_measured_fren_no_access_loss [BoschHaleDT sv]
    [PowerBalance stellarisPlasma sv Paux τE T] {flo : ℝ}
    [LossScaling stellarisLaw flo 1.3 stellarisPlasma sv Paux τE T H PL] (hflo : 0 < flo)
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 0 70e6) (h0 : T 0 ≤ 10) :
    ∀ t, 0 ≤ t → T t ≤ 10 :=
  PowerBalance.upper_barrier h0
    (LossScaling.upper_crossing (L := stellarisLaw) (Hlo := flo) (Hhi := 1.3) (H := H)
      (PL := PL) (τE := τE) (Pmax := 184e6) (by norm_num) hflo
      (fun t ht _ => st_heat_ten_le sv (hP t ht).2) measured_numeric)

/-- Heating power of the steady witness: `P* = P_α(18 keV) + 60 MW`. -/
@[expose] def witP (sv : ℝ → ℝ) : ℝ := stellarisPlasma.alphaPower sv 18 + 60e6

/-- Renormalization factor balancing the steady witness:
`f_ren* = W(18) (P*/1 MW)^α / (C (P* − P_br(18)))`. -/
@[expose] def witF (sv : ℝ → ℝ) : ℝ :=
  stellarisPlasma.thermalEnergy 18 * (witP sv / 1e6) ^ stellarisLaw.α /
    (stellarisLaw.C * (witP sv - stellarisPlasma.bremsPower 18))

/-- **Non-vacuity of the scaling hypotheses.** For every reactivity satisfying the supplied
Bosch–Hale facts, take the constant 18 keV state with `P_aux = 60 MW`, `f_ren = f_ren*`,
`τ_E = τ_ISS04(f_ren*, P*)` and `P_L = P*`. It satisfies the balance law, both scaling classes
with `f_ren ∈ [1.55, 1.75]` (in fact `1.61 ≤ f_ren* ≤ 1.68`), and every hypothesis of
`stellaris_window_steady`/`_loss`. **The crossing conditions are vacuous for this witness**,
because it never reaches 10 or 22 keV. -/
theorem stellaris_satisfiable (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ∃ Paux τE T H PL : ℝ → ℝ, PowerBalance stellarisPlasma sv Paux τE T ∧
      SteadyScaling stellarisLaw 1.55 1.75 stellarisPlasma sv Paux τE T H ∧
      LossScaling stellarisLaw 1.55 1.75 stellarisPlasma sv Paux τE T H PL ∧
      (∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) ∧ T 0 ∈ Set.Icc 10 22 := by
  have hs1 := sv_eighteen_ge sv
  have hs2 := sv_eighteen_le sv
  have hC := stellaris_coeff_bounds
  have hP1 : 424e6 ≤ witP sv := by unfold witP; rw [st_alpha]; norm_num; linarith
  have hP2 : witP sv ≤ 433e6 := by unfold witP; rw [st_alpha]; norm_num; linarith
  have hq1 : 4.2426 ≤ Real.sqrt 18 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hq2 : Real.sqrt 18 ≤ 4.2427 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb1 : 36.89e6 ≤ stellarisPlasma.bremsPower 18 := by rw [st_brems]; norm_num; nlinarith
  have hb2 : stellarisPlasma.bremsPower 18 ≤ 36.91e6 := by rw [st_brems]; norm_num; nlinarith
  have hy0 : 0 < witP sv / 1e6 := by
    have : (0 : ℝ) < witP sv := by linarith
    positivity
  have hy1 : (424e6 : ℝ) / 1e6 ≤ witP sv / 1e6 := div_le_div_of_nonneg_right hP1 (by norm_num)
  have hA1 : (40.05 : ℝ) ≤ (witP sv / 1e6) ^ stellarisLaw.α :=
    (rpow_lb 61 _ (by norm_num [stellarisLaw_α]) (by norm_num) (by norm_num) (by norm_num) :
      (40.05 : ℝ) ≤ ((424e6 : ℝ) / 1e6) ^ stellarisLaw.α).trans
      (Real.rpow_le_rpow (by norm_num) hy1 (by norm_num [stellarisLaw_α]))
  have hA2 : (witP sv / 1e6) ^ stellarisLaw.α ≤ 40.58 :=
    (Real.rpow_le_rpow hy0.le (div_le_div_of_nonneg_right hP2 (by norm_num))
      (by norm_num [stellarisLaw_α])).trans
      (rpow_ub 61 _ (by norm_num [stellarisLaw_α]) (by norm_num) (by norm_num) (by norm_num) :
        ((433e6 : ℝ) / 1e6) ^ stellarisLaw.α ≤ 40.58)
  have hW : stellarisPlasma.thermalEnergy 18 =
      3 / 2 * 1.5e20 * (1 + 53 / 60) * (18 * 1.602176634e-16) * 425 := st_W 18
  have hWpos : 0 < stellarisPlasma.thermalEnergy 18 := by rw [hW]; norm_num
  have hD : 0 < witP sv - stellarisPlasma.bremsPower 18 := by linarith
  have hCpos : 0 < stellarisLaw.C := by linarith
  -- bounds on `f_ren*`
  have hF1 : 1.55 ≤ witF sv := by
    unfold witF
    rw [le_div_iff₀ (by positivity)]
    have e1 : 1.55 * (stellarisLaw.C * (witP sv - stellarisPlasma.bremsPower 18)) ≤
        1.55 * (32.46 * (433e6 - 36.89e6)) := by gcongr; linarith
    have e2 : stellarisPlasma.thermalEnergy 18 * 40.05 ≤
        stellarisPlasma.thermalEnergy 18 * (witP sv / 1e6) ^ stellarisLaw.α := by gcongr
    rw [hW] at e2 ⊢
    norm_num at e1 e2 ⊢
    linarith
  have hF2 : witF sv ≤ 1.75 := by
    unfold witF
    rw [div_le_iff₀ (by positivity)]
    have e1 : 1.75 * (32.45 * (424e6 - 36.91e6)) ≤
        1.75 * (stellarisLaw.C * (witP sv - stellarisPlasma.bremsPower 18)) := by
      gcongr; linarith
    have e2 : stellarisPlasma.thermalEnergy 18 * (witP sv / 1e6) ^ stellarisLaw.α ≤
        stellarisPlasma.thermalEnergy 18 * 40.58 := by gcongr
    rw [hW] at e2 ⊢
    norm_num at e1 e2 ⊢
    linarith
  have hFpos : 0 < witF sv := by linarith
  -- the witness is an exact steady state
  have hτ : 0 < stellarisLaw.tau (witF sv) (witP sv) :=
    stellarisLaw.tau_pos hFpos (by linarith)
  have hnet : stellarisPlasma.netHeating sv 60e6 (stellarisLaw.tau (witF sv) (witP sv)) 18 = 0 := by
    have := steadyNet_eq stellarisLaw (b := stellarisPlasma.bremsPower 18)
      (W := stellarisPlasma.thermalEnergy 18) (by linarith : 0 < witP sv) hFpos
    have hz : scalingMargin stellarisLaw.α (stellarisPlasma.bremsPower 18) (witP sv / 1e6) -
        stellarisPlasma.thermalEnergy 18 / (witF sv * stellarisLaw.C) = 0 := by
      have hA : 0 < (witP sv / 1e6) ^ stellarisLaw.α := Real.rpow_pos_of_pos hy0 _
      unfold scalingMargin witF
      rw [Real.rpow_neg hy0.le, Real.rpow_sub hy0, Real.rpow_one]
      field_simp
      ring
    rw [hz, mul_zero] at this
    unfold netHeating lossPower
    unfold witP at this ⊢
    linarith
  refine ⟨fun _ => 60e6, fun _ => stellarisLaw.tau (witF sv) (witP sv), fun _ => 18,
    fun _ => witF sv, fun _ => witP sv, ⟨fun _ _ => hτ, fun t _ => ?_⟩,
    ⟨fun _ _ => ⟨hF1, hF2⟩, fun _ _ => rfl, fun _ _ => by unfold witP at hP1; linarith⟩,
    ⟨fun _ _ => ⟨hF1, hF2⟩, fun t _ => ?_, fun _ _ => rfl, fun _ _ => by linarith⟩,
    fun _ _ => ⟨by norm_num, by norm_num⟩, by norm_num⟩
  · simpa [hnet] using (hasDerivAt_const t (stellarisPlasma.thermalEnergy 18)).hasDerivWithinAt
  · have h0 : stellarisPlasma.alphaPower sv 18 + 60e6 - witP sv = 0 := by unfold witP; ring
    simpa [h0] using (hasDerivAt_const t (stellarisPlasma.thermalEnergy 18)).hasDerivWithinAt

end PlasmaLean.Design.BurnWindowStellarator
