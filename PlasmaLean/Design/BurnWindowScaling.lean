/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.ConfinementScaling
public import PlasmaLean.Design.BurnWindow

/-!
# Model rung M1 with a supplied IPB98(y,2) confinement scaling

This module replaces the ad-hoc state-dependent `τ_E` hypotheses of `Design.BurnWindow`
(`τ_E ≥ 3.5 s` at `T ≤ 10 keV`, `τ_E ≤ 1.8 s` at `T ≥ 30 keV`) by the empirical
**IPB98(y,2)** scaling (ITER Physics Basis, Nucl. Fusion 39 (1999) 2175) with an uncertain
enhancement factor `H ∈ [1.25, 2]`, in either convention for the power `P` (steady heating
power `P_α + P_aux`, or loss power `P_α + P_aux − dW/dt`; see
`Theory.Transport.ConfinementScaling`).

## Machine (ITER-like tokamak, *synthetic reactor-scale data*)

`I_p = 15 MA`, `B = 5.3 T`, `n₁₉ = 10`, `M = 2.5`, `R = 6.2 m`, `ε = a/R = 2/6.2 = 10/31`,
`κ_a = 1.7` (`iterParams`); then `V = 2π²Ra²κ ≈ 832 m³`, consistent with the M1 plasma
`m1Plasma` (`n = 10²⁰ m⁻³`, `V = 830 m³`, carbon `Z_eff = 1.7`). The IPB98 machine
coefficient is enclosed as `78.25 ≤ C ≤ 78.26` s·MW^0.69 (`iter_coeff_bounds`), with each
real power `x^(a/100)` bracketed by an integer-power inequality checked exactly.

The ISS04 stellarator alternative (a = 1.8 m, R = 22 m, B = 5.5 T, ι = 0.9) was
**rejected on the basis of a floating-point Python scan (a numerical observation, not a
Lean theorem)**: in this 0-D model it needs `H_ISS04 ≈ 1.9`
just to hold 10 keV with 50 MW of auxiliary power (and ≈ 2.4 without it), so no useful
`H` range near 1 exists.

## Results (for every trajectory satisfying the kernel balance law, the supplied Bosch–Hale
facts and the scaling law; no other `τ_E` hypothesis)

* `m1_scaling_window_steady`, `m1_scaling_window_loss`: with
  `50 MW ≤ P_aux ≤ 70 MW` and `H(t) ∈ [1.25, 2]`, `T(0) ∈ [10, 30] keV` implies
  `T(t) ∈ [10, 30] keV` for all `t ≥ 0`. Certificates: at 10 keV with heating power
  `≥ 146.6 MW` and `H = 1.25`, the steady-form net heating is `≥ +2.7 MW`
  (`lower_numeric`). At 30 keV with heating power `≤ 651 MW` and `H = 2`, it is
  `≤ −19 MW` (`upper_numeric`).
* `m1_scaling_fusion_yield`: fusion energy `≥ 4.8 × 10⁸ W · t_b` over `[0, t_b]`.
* `m1_nominal_H_no_access` (**honest negative result**): at the nominal `H ≤ 1` and
  `P_aux ≤ 73 MW`, net heating at 10 keV is `≤ −19 MW`, so `T(0) ≤ 10 keV ⇒ T(t) ≤ 10 keV`.
  In this 0-D model (flat profiles, no radiation subtracted from `P`) the ITER-like
  machine needs `H ≳ 1.22` to hold 10 keV. This threshold is a floating-point
  numerical observation; Lean proves only failure at `H ≤ 1` and success at `H ≥ 1.25`.
  Real ITER Q = 10 scenarios at `H = 1`
  rely on peaked profiles and lower average temperature (≈ 8.5 keV), which M1 does not model.
* `m1_scaling_satisfiable`: for **every** Bosch–Hale reactivity, a steady 20 keV state with
  `P_aux = 60 MW` and an explicit `H* ∈ [1.25, 2]` satisfies the balance law and both
  scaling classes. The crossing hypotheses are vacuous for this witness (it never reaches
  10 or 30 keV).
* `m1_ignition_bracket`, `m1_ignition_root`, `m1_ignition_unstable`: (d) with **constant**
  `τ_E = 3.5 s` and no auxiliary power, the net heating is `< 0` at 12 keV and `> 0` at
  13 keV. So an ignition temperature `T_ign ∈ (12, 13)` with zero net heating exists
  (intermediate value theorem). It is unstable: trajectories starting below 12 keV stay
  below 12 keV, and those starting above 13 keV stay above 13 keV.
-/

public section
noncomputable section

namespace PlasmaLean.Design.BurnWindowScaling

open PlasmaLean.Fusion DTPlasma PlasmaLean.Design.BurnWindow

/-- ITER-like tokamak parameters for IPB98(y,2): `I_p = 15 MA`, `B = 5.3 T`, `n₁₉ = 10`,
`M = 2.5`, `R = 6.2 m`, `ε = 10/31`, `κ_a = 1.7`. -/
@[expose] def iterParams : TokamakParams := ⟨15, 5.3, 10, 2.5, 6.2, 10 / 31, 1.7⟩

/-- The IPB98(y,2) law for `iterParams`. -/
@[expose] def iterLaw : ConfinementLaw := iterParams.ipb98

/-- The ITER-like IPB98(y,2) law is admissible (`C > 0`, `α = 0.69`). -/
instance iterLaw_admissible : iterLaw.Admissible :=
  iterParams.ipb98_admissible (by norm_num [iterParams]) (by norm_num [iterParams])
    (by norm_num [iterParams]) (by norm_num [iterParams]) (by norm_num [iterParams])
    (by norm_num [iterParams]) (by norm_num [iterParams])

/-- The IPB98(y,2) power exponent. -/
theorem iterLaw_α : iterLaw.α = 0.69 := rfl

/-- Bracketing a real power with exponent `a/100` from below. -/
theorem rpow_lb {x l : ℝ} (a : ℕ) (e : ℝ) (he : e = (a : ℝ) / (100 : ℕ)) (hl : 0 ≤ l)
    (hx : 0 ≤ x) (h : l ^ 100 ≤ x ^ a) : l ≤ x ^ e := by
  rw [he]; exact le_rpow_of_pow_le (by norm_num) hl hx h

/-- Bracketing a real power with exponent `a/100` from above. -/
theorem rpow_ub {x u : ℝ} (a : ℕ) (e : ℝ) (he : e = (a : ℝ) / (100 : ℕ)) (hu : 0 ≤ u)
    (hx : 0 ≤ x) (h : x ^ a ≤ u ^ 100) : x ^ e ≤ u := by
  rw [he]; exact rpow_le_of_le_pow (by norm_num) hu hx h

/-- **Enclosure of the IPB98(y,2) coefficient** for `iterParams`:
`78.25 ≤ C ≤ 78.26` (s · MW^0.69). -/
theorem iter_coeff_bounds : 78.25 ≤ iterLaw.C ∧ iterLaw.C ≤ 78.26 := by
  have hC : iterLaw.C = 0.0562 * (15 : ℝ) ^ (0.93 : ℝ) * (5.3 : ℝ) ^ (0.15 : ℝ) *
      (10 : ℝ) ^ (0.41 : ℝ) * (2.5 : ℝ) ^ (0.19 : ℝ) * (6.2 : ℝ) ^ (1.97 : ℝ) *
      (10 / 31 : ℝ) ^ (0.58 : ℝ) * (1.7 : ℝ) ^ (0.78 : ℝ) := rfl
  have l1 : (12.4098 : ℝ) ≤ (15 : ℝ) ^ (0.93 : ℝ) :=
    rpow_lb 93 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u1 : (15 : ℝ) ^ (0.93 : ℝ) ≤ 12.40981 :=
    rpow_ub 93 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l2 : (1.28422 : ℝ) ≤ (5.3 : ℝ) ^ (0.15 : ℝ) :=
    rpow_lb 15 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u2 : (5.3 : ℝ) ^ (0.15 : ℝ) ≤ 1.28423 :=
    rpow_ub 15 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l3 : (2.57039 : ℝ) ≤ (10 : ℝ) ^ (0.41 : ℝ) :=
    rpow_lb 41 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u3 : (10 : ℝ) ^ (0.41 : ℝ) ≤ 2.5704 :=
    rpow_ub 41 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l4 : (1.19016 : ℝ) ≤ (2.5 : ℝ) ^ (0.19 : ℝ) :=
    rpow_lb 19 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u4 : (2.5 : ℝ) ^ (0.19 : ℝ) ≤ 1.19017 :=
    rpow_ub 19 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l5 : (36.39247 : ℝ) ≤ (6.2 : ℝ) ^ (1.97 : ℝ) :=
    rpow_lb 197 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u5 : (6.2 : ℝ) ^ (1.97 : ℝ) ≤ 36.39248 :=
    rpow_ub 197 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l6 : (0.51881 : ℝ) ≤ (10 / 31 : ℝ) ^ (0.58 : ℝ) :=
    rpow_lb 58 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u6 : (10 / 31 : ℝ) ^ (0.58 : ℝ) ≤ 0.51882 :=
    rpow_ub 58 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l7 : (1.51269 : ℝ) ≤ (1.7 : ℝ) ^ (0.78 : ℝ) :=
    rpow_lb 78 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u7 : (1.7 : ℝ) ^ (0.78 : ℝ) ≤ 1.5127 :=
    rpow_ub 78 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hC]
  constructor
  · calc (78.25 : ℝ) ≤ 0.0562 * 12.4098 * 1.28422 * 2.57039 * 1.19016 * 36.39247 * 0.51881 *
          1.51269 := by norm_num
      _ ≤ _ := by gcongr
  · calc _ ≤ (0.0562 : ℝ) * 12.40981 * 1.28423 * 2.5704 * 1.19017 * 36.39248 * 0.51882 *
          1.5127 := by gcongr
      _ ≤ 78.26 := by norm_num

/-- Transport loss with the scaling law, upper bound: if `y^α ≤ u` then
`W / (h C y^(−α)) ≤ W u / (h C)`. -/
theorem loss_le_of_rpow_le {W h C y α u : ℝ} (hW : 0 ≤ W) (hh : 0 < h) (hC : 0 < C)
    (hy : 0 < y) (hu : y ^ α ≤ u) : W / (h * C * y ^ (-α)) ≤ W * u / (h * C) := by
  have hA : 0 < y ^ α := Real.rpow_pos_of_pos hy _
  rw [Real.rpow_neg hy.le, div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hu hW]

/-- Transport loss with the scaling law, lower bound: if `ℓ ≤ y^α` then
`W ℓ / (h C) ≤ W / (h C y^(−α))`. -/
theorem le_loss_of_le_rpow {W h C y α l : ℝ} (hW : 0 ≤ W) (hh : 0 < h) (hC : 0 < C)
    (hy : 0 < y) (hl : l ≤ y ^ α) : W * l / (h * C) ≤ W / (h * C * y ^ (-α)) := by
  have hA : 0 < y ^ α := Real.rpow_pos_of_pos hy _
  rw [Real.rpow_neg hy.le, div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hl hW]

/-- Explicit M1 thermal energy (J) at `x` keV. -/
theorem m1_W (x : ℝ) :
    m1Plasma.thermalEnergy x = 3 / 2 * 1e20 * (1 + 53 / 60) * (x * 1.602176634e-16) * 830 := by
  simp only [thermalEnergy, m1Plasma, keV]

/-- Explicit M1 bremsstrahlung (W) at `x` keV. -/
theorem m1_brems (x : ℝ) :
    m1Plasma.bremsPower x = 5.35e-37 * (1e20 : ℝ) ^ 2 * 1.7 * Real.sqrt x * 830 := by
  simp only [bremsPower, m1Plasma, bremsCoeff]

/-- Explicit M1 alpha power (W) at `x` keV. -/
theorem m1_alpha (sv : ℝ → ℝ) (x : ℝ) :
    m1Plasma.alphaPower sv x = 3500 * 1.602176634e-16 / 4 * (0.86 * 1e20 : ℝ) ^ 2 * sv x * 830 := by
  simp only [alphaPower, m1Plasma, alphaEnergy, keV]

/-- **Lower-crossing certificate at 10 keV.** Heating power `146.6 MW`, `H = 1.25`:
`146.6 MW − P_br(10) − W(10)/τ_IPB98 > 0` (≈ +2.7 MW). Uses
`146.6^0.69 ≤ 31.235` and `C ≥ 78.25`. -/
theorem lower_numeric :
    0 < 146.6e6 - m1Plasma.bremsPower 10 - m1Plasma.lossPower (iterLaw.tau 1.25 146.6e6) 10 := by
  have hu : ((146.6e6 : ℝ) / 1e6) ^ iterLaw.α ≤ 31.235 :=
    rpow_ub 69 _ (by norm_num [iterLaw_α]) (by norm_num) (by norm_num) (by norm_num)
  have hC := iter_coeff_bounds.1
  have hW : 0 ≤ m1Plasma.thermalEnergy 10 := thermalEnergy_nonneg _ (by norm_num)
  have h1 := loss_le_of_rpow_le (C := iterLaw.C) hW (by norm_num : (0 : ℝ) < 1.25) (by linarith)
    (by norm_num : (0 : ℝ) < 146.6e6 / 1e6) hu
  have h2 : m1Plasma.thermalEnergy 10 * 31.235 / (1.25 * iterLaw.C) ≤
      m1Plasma.thermalEnergy 10 * 31.235 / (1.25 * 78.25) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hs : Real.sqrt 10 ≤ 3.1623 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hX : m1Plasma.lossPower (iterLaw.tau 1.25 146.6e6) 10 ≤
      m1Plasma.thermalEnergy 10 * 31.235 / (1.25 * 78.25) := by
    unfold lossPower ConfinementLaw.tau; exact h1.trans h2
  have hb : m1Plasma.bremsPower 10 ≤ 23.88e6 := by rw [m1_brems]; norm_num; nlinarith
  rw [m1_W] at hX; norm_num at hX; linarith

/-- **Upper-crossing certificate at 30 keV.** Heating power `651 MW`, `H = 2`:
`651 MW − P_br(30) − W(30)/τ_IPB98 < 0` (≈ −19 MW). Uses `651^0.69 ≥ 87.37`, `C ≤ 78.26`. -/
theorem upper_numeric :
    651e6 - m1Plasma.bremsPower 30 - m1Plasma.lossPower (iterLaw.tau 2 651e6) 30 < 0 := by
  have hl : (87.37 : ℝ) ≤ ((651e6 : ℝ) / 1e6) ^ iterLaw.α :=
    rpow_lb 69 _ (by norm_num [iterLaw_α]) (by norm_num) (by norm_num) (by norm_num)
  have hC := iter_coeff_bounds
  have hW : 0 ≤ m1Plasma.thermalEnergy 30 := thermalEnergy_nonneg _ (by norm_num)
  have h1 := le_loss_of_le_rpow (C := iterLaw.C) hW (by norm_num : (0 : ℝ) < 2) (by linarith)
    (by norm_num : (0 : ℝ) < 651e6 / 1e6) hl
  have h2 : m1Plasma.thermalEnergy 30 * 87.37 / (2 * 78.26) ≤
      m1Plasma.thermalEnergy 30 * 87.37 / (2 * iterLaw.C) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hs : 5.477 ≤ Real.sqrt 30 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hX : m1Plasma.thermalEnergy 30 * 87.37 / (2 * 78.26) ≤
      m1Plasma.lossPower (iterLaw.tau 2 651e6) 30 := by
    unfold lossPower ConfinementLaw.tau; exact h2.trans h1
  have hb : 41.34e6 ≤ m1Plasma.bremsPower 30 := by rw [m1_brems]; norm_num; nlinarith
  rw [m1_W] at hX; norm_num at hX; linarith

/-- **Nominal-confinement certificate at 10 keV.** Heating power `172 MW`, `H = 1`:
`172 MW − P_br(10) − W(10)/τ_IPB98 < 0` (≈ −19 MW). Uses `172^0.69 ≥ 34.87`, `C ≤ 78.26`. -/
theorem nominal_numeric :
    172e6 - m1Plasma.bremsPower 10 - m1Plasma.lossPower (iterLaw.tau 1 172e6) 10 < 0 := by
  have hl : (34.87 : ℝ) ≤ ((172e6 : ℝ) / 1e6) ^ iterLaw.α :=
    rpow_lb 69 _ (by norm_num [iterLaw_α]) (by norm_num) (by norm_num) (by norm_num)
  have hC := iter_coeff_bounds
  have hW : 0 ≤ m1Plasma.thermalEnergy 10 := thermalEnergy_nonneg _ (by norm_num)
  have h1 := le_loss_of_le_rpow (C := iterLaw.C) hW (by norm_num : (0 : ℝ) < 1) (by linarith)
    (by norm_num : (0 : ℝ) < 172e6 / 1e6) hl
  have h2 : m1Plasma.thermalEnergy 10 * 34.87 / (1 * 78.26) ≤
      m1Plasma.thermalEnergy 10 * 34.87 / (1 * iterLaw.C) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hs : 3.162 ≤ Real.sqrt 10 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hX : m1Plasma.thermalEnergy 10 * 34.87 / (1 * 78.26) ≤
      m1Plasma.lossPower (iterLaw.tau 1 172e6) 10 := by
    unfold lossPower ConfinementLaw.tau; exact h2.trans h1
  have hb : 23.86e6 ≤ m1Plasma.bremsPower 10 := by rw [m1_brems]; norm_num; nlinarith
  rw [m1_W] at hX; norm_num at hX; linarith

variable {sv Paux τE T H PL : ℝ → ℝ}

/-- Heating power at 10 keV with `P_aux ≥ 50 MW` is at least `146.6 MW`. -/
theorem heat_ten_ge (sv : ℝ → ℝ) [BoschHaleDT sv] {P : ℝ} (hP : 50e6 ≤ P) :
    146.6e6 ≤ m1Plasma.alphaPower sv 10 + P := by
  have := sv_ten_ge sv
  rw [m1_alpha]; norm_num; linarith

/-- Heating power at 10 keV with `P_aux ≤ 73 MW` is at most `172 MW`. -/
theorem heat_ten_le (sv : ℝ → ℝ) [BoschHaleDT sv] {P : ℝ} (hP : P ≤ 73e6) :
    m1Plasma.alphaPower sv 10 + P ≤ 172e6 := by
  have := sv_ten_le sv
  rw [m1_alpha]; norm_num; linarith

/-- Heating power at 30 keV with `P_aux ≤ 70 MW` is at most `651 MW`. -/
theorem heat_thirty_le (sv : ℝ → ℝ) [BoschHaleDT sv] {P : ℝ} (hP : P ≤ 70e6) :
    m1Plasma.alphaPower sv 30 + P ≤ 651e6 := by
  have := sv_thirty_le sv
  rw [m1_alpha]; norm_num; linarith

/-- Alpha power is nonnegative at nonnegative temperature. -/
theorem alpha_nonneg (sv : ℝ → ℝ) [BoschHaleDT sv] {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ m1Plasma.alphaPower sv x := by
  have := BoschHaleDT.nonneg (sv := sv) x hx
  rw [m1_alpha]; positivity

/-- **M1 burn window from IPB98(y,2), steady (heating-power) form.** For every trajectory
satisfying the balance law, the supplied Bosch–Hale facts and the IPB98(y,2) law with
`P = P_α + P_aux` and `H(t) ∈ [1.25, 2]`, if `50 MW ≤ P_aux ≤ 70 MW` then
`T(0) ∈ [10, 30]` keV implies `T(t) ∈ [10, 30]` keV for all `t ≥ 0`. -/
theorem m1_scaling_window_steady [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    [SteadyScaling iterLaw 1.25 2 m1Plasma sv Paux τE T H]
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) (h0 : T 0 ∈ Set.Icc 10 30) :
    ∀ t, 0 ≤ t → T t ∈ Set.Icc 10 30 :=
  SteadyScaling.window (L := iterLaw) (sv := sv) (Paux := Paux) (τE := τE) (T := T) (H := H)
    (Pmin := 146.6e6) (Pmax := 651e6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t ht _ => heat_ten_ge sv (hP t ht).1)
    (fun t ht _ => by
      have := alpha_nonneg sv (by norm_num : (0 : ℝ) ≤ 30)
      linarith [(hP t ht).1])
    (fun t ht _ => heat_thirty_le sv (hP t ht).2) lower_numeric upper_numeric h0

/-- **M1 burn window from IPB98(y,2), loss-power form** (`P = P_α + P_aux − dW/dt`,
ITER database convention). Same conclusion and data as `m1_scaling_window_steady`. -/
theorem m1_scaling_window_loss [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    [LossScaling iterLaw 1.25 2 m1Plasma sv Paux τE T H PL]
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) (h0 : T 0 ∈ Set.Icc 10 30) :
    ∀ t, 0 ≤ t → T t ∈ Set.Icc 10 30 :=
  LossScaling.window (L := iterLaw) (sv := sv) (Paux := Paux) (τE := τE) (T := T) (H := H)
    (PL := PL) (Pmin := 146.6e6) (Pmax := 651e6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t ht _ => heat_ten_ge sv (hP t ht).1)
    (fun t ht _ => heat_thirty_le sv (hP t ht).2) lower_numeric upper_numeric h0

/-- **M1 burn yield under IPB98(y,2)** (steady form): fusion energy over `[0, t_b]` is at
least `4.8 × 10⁸ W · t_b`. -/
theorem m1_scaling_fusion_yield [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    [SteadyScaling iterLaw 1.25 2 m1Plasma sv Paux τE T H]
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) (h0 : T 0 ∈ Set.Icc 10 30) {tb : ℝ}
    (htb : 0 ≤ tb) : 4.8e8 * tb ≤ ∫ t in (0 : ℝ)..tb, m1Plasma.fusionPower sv (T t) := by
  have hwin := m1_scaling_window_steady (sv := sv) (Paux := Paux) (τE := τE) (T := T) (H := H)
    hP h0
  have hy := PowerBalance.fusion_yield_ge (p := m1Plasma) (sv := sv) (Paux := Paux)
    (τE := τE) (T := T) htb (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (30 : ℝ) ≤ 60)
    (fun t ht => hwin t ht.1)
  have hf : 4.8e8 ≤ m1Plasma.fusionPower sv 10 := by
    have := sv_ten_ge sv
    simp only [fusionPower, m1Plasma, fusionEnergy, keV]
    norm_num; linarith
  nlinarith

/-- **Honest negative result: nominal confinement cannot hold 10 keV.** With the
IPB98(y,2) law at `H(t) ∈ [H_lo, 1]` (any `H_lo > 0`) and `0 ≤ P_aux ≤ 73 MW`, the net
heating at every crossing of 10 keV is negative, so `T(0) ≤ 10 keV` implies
`T(t) ≤ 10 keV` for all `t ≥ 0`. -/
theorem m1_nominal_H_no_access [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    {Hlo : ℝ} [SteadyScaling iterLaw Hlo 1 m1Plasma sv Paux τE T H] (hHlo : 0 < Hlo)
    (hP : ∀ t, 0 ≤ t → Paux t ∈ Set.Icc 0 73e6) (h0 : T 0 ≤ 10) :
    ∀ t, 0 ≤ t → T t ≤ 10 :=
  PowerBalance.upper_barrier h0
    (SteadyScaling.upper_crossing (L := iterLaw) (Hlo := Hlo) (Hhi := 1) (H := H) (τE := τE)
      (Pmax := 172e6) (by norm_num) hHlo
      (fun t ht _ => by
        have := sv_ten_ge sv
        have h1 : 0 < m1Plasma.alphaPower sv 10 := by rw [m1_alpha]; norm_num; linarith
        linarith [(hP t ht).1])
      (fun t ht _ => heat_ten_le sv (hP t ht).2) nominal_numeric)

/-- Supplied reactivity at 20 keV: `⟨σv⟩(20) ≤ 4.374e-22 m³/s` (window `[19, 20]`). -/
theorem sv_twenty_le (sv : ℝ → ℝ) [BoschHaleDT sv] : sv 20 ≤ (4.374e-22 : ℝ) := by
  have := (BoschHaleDT.windows (sv := sv) ⟨19, 20, 3.989e-22, 4.374e-22⟩
    (by simp [boschHaleWindows]) 20 (by norm_num) (by norm_num)).2
  norm_num at this ⊢; exact this

/-- Heating power of the steady witness: `P* = P_α(20 keV) + 60 MW`. -/
@[expose] def witP (sv : ℝ → ℝ) : ℝ := m1Plasma.alphaPower sv 20 + 60e6

/-- Enhancement factor balancing the steady witness:
`H* = W(20) (P*/1 MW)^α / (C (P* − P_br(20)))`. -/
@[expose] def witH (sv : ℝ → ℝ) : ℝ :=
  m1Plasma.thermalEnergy 20 * (witP sv / 1e6) ^ iterLaw.α /
    (iterLaw.C * (witP sv - m1Plasma.bremsPower 20))

/-- **Non-vacuity of the scaling hypotheses.** For every reactivity satisfying the
supplied Bosch–Hale facts, the constant 20 keV state with `P_aux = 60 MW`, `H = H*`,
`τ_E = τ_IPB98(H*, P*)` and `P_L = P*` satisfies the balance law, both scaling classes with
`H ∈ [1.25, 2]` (indeed `1.56 ≤ H* ≤ 1.62`), and every hypothesis of
`m1_scaling_window_steady`/`_loss`. The crossing conditions are vacuous for this witness. -/
theorem m1_scaling_satisfiable (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ∃ Paux τE T H PL : ℝ → ℝ, PowerBalance m1Plasma sv Paux τE T ∧
      SteadyScaling iterLaw 1.25 2 m1Plasma sv Paux τE T H ∧
      LossScaling iterLaw 1.25 2 m1Plasma sv Paux τE T H PL ∧
      (∀ t, 0 ≤ t → Paux t ∈ Set.Icc 50e6 70e6) ∧ T 0 ∈ Set.Icc 10 30 := by
  have hs1 := sv_twenty_ge sv
  have hs2 := sv_twenty_le sv
  have hC := iter_coeff_bounds
  have hP1 : 428.8e6 ≤ witP sv := by unfold witP; rw [m1_alpha]; norm_num; linarith
  have hP2 : witP sv ≤ 436.5e6 := by unfold witP; rw [m1_alpha]; norm_num; linarith
  have hq1 : 4.472 ≤ Real.sqrt 20 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hq2 : Real.sqrt 20 ≤ 4.4722 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb1 : 33.75e6 ≤ m1Plasma.bremsPower 20 := by rw [m1_brems]; norm_num; nlinarith
  have hb2 : m1Plasma.bremsPower 20 ≤ 33.77e6 := by rw [m1_brems]; norm_num; nlinarith
  have hy0 : 0 < witP sv / 1e6 := by have : (0 : ℝ) < witP sv := by linarith
                                     positivity
  have hy1 : (428.8e6 : ℝ) / 1e6 ≤ witP sv / 1e6 := div_le_div_of_nonneg_right hP1 (by norm_num)
  have hA1 : (65.50 : ℝ) ≤ (witP sv / 1e6) ^ iterLaw.α :=
    (rpow_lb 69 _ (by norm_num [iterLaw_α]) (by norm_num) (by norm_num) (by norm_num) :
      (65.50 : ℝ) ≤ ((428.8e6 : ℝ) / 1e6) ^ iterLaw.α).trans
      (Real.rpow_le_rpow (by norm_num) hy1 (by norm_num [iterLaw_α]))
  have hA2 : (witP sv / 1e6) ^ iterLaw.α ≤ 66.32 :=
    (Real.rpow_le_rpow hy0.le (div_le_div_of_nonneg_right hP2 (by norm_num))
      (by norm_num [iterLaw_α])).trans
      (rpow_ub 69 _ (by norm_num [iterLaw_α]) (by norm_num) (by norm_num) (by norm_num) :
        ((436.5e6 : ℝ) / 1e6) ^ iterLaw.α ≤ 66.32)
  have hW : m1Plasma.thermalEnergy 20 = 3 / 2 * 1e20 * (1 + 53 / 60) * (20 * 1.602176634e-16)
      * 830 := m1_W 20
  have hWpos : 0 < m1Plasma.thermalEnergy 20 := by rw [hW]; norm_num
  have hD : 0 < witP sv - m1Plasma.bremsPower 20 := by linarith
  have hCpos : 0 < iterLaw.C := by linarith
  -- bounds on `H*`
  have hH1 : 1.25 ≤ witH sv := by
    unfold witH
    rw [le_div_iff₀ (by positivity)]
    have e1 : 1.25 * (iterLaw.C * (witP sv - m1Plasma.bremsPower 20)) ≤
        1.25 * (78.26 * (436.5e6 - 33.75e6)) := by gcongr; linarith
    have e2 : m1Plasma.thermalEnergy 20 * 65.50 ≤
        m1Plasma.thermalEnergy 20 * (witP sv / 1e6) ^ iterLaw.α := by gcongr
    rw [hW] at e2 ⊢
    norm_num at e1 e2 ⊢
    linarith
  have hH2 : witH sv ≤ 2 := by
    unfold witH
    rw [div_le_iff₀ (by positivity)]
    have e1 : 2 * (78.25 * (428.8e6 - 33.77e6)) ≤
        2 * (iterLaw.C * (witP sv - m1Plasma.bremsPower 20)) := by gcongr; linarith
    have e2 : m1Plasma.thermalEnergy 20 * (witP sv / 1e6) ^ iterLaw.α ≤
        m1Plasma.thermalEnergy 20 * 66.32 := by gcongr
    rw [hW] at e2 ⊢
    norm_num at e1 e2 ⊢
    linarith
  have hHpos : 0 < witH sv := by linarith
  -- the witness is an exact steady state
  have hτ : 0 < iterLaw.tau (witH sv) (witP sv) :=
    iterLaw.tau_pos hHpos (by linarith)
  have hnet : m1Plasma.netHeating sv 60e6 (iterLaw.tau (witH sv) (witP sv)) 20 = 0 := by
    have := steadyNet_eq iterLaw (b := m1Plasma.bremsPower 20)
      (W := m1Plasma.thermalEnergy 20) (by linarith : 0 < witP sv) hHpos
    have hz : scalingMargin iterLaw.α (m1Plasma.bremsPower 20) (witP sv / 1e6) -
        m1Plasma.thermalEnergy 20 / (witH sv * iterLaw.C) = 0 := by
      have hA : 0 < (witP sv / 1e6) ^ iterLaw.α := Real.rpow_pos_of_pos hy0 _
      unfold scalingMargin witH
      rw [Real.rpow_neg hy0.le, Real.rpow_sub hy0, Real.rpow_one]
      field_simp
      ring
    rw [hz, mul_zero] at this
    unfold netHeating lossPower
    unfold witP at this ⊢
    linarith
  refine ⟨fun _ => 60e6, fun _ => iterLaw.tau (witH sv) (witP sv), fun _ => 20,
    fun _ => witH sv, fun _ => witP sv, ⟨fun _ _ => hτ, fun t _ => ?_⟩,
    ⟨fun _ _ => ⟨hH1, hH2⟩, fun _ _ => rfl, fun _ _ => by unfold witP at hP1; linarith⟩,
    ⟨fun _ _ => ⟨hH1, hH2⟩, fun t _ => ?_, fun _ _ => rfl, fun _ _ => by linarith⟩,
    fun _ _ => ⟨by norm_num, by norm_num⟩, by norm_num⟩
  · simpa [hnet] using (hasDerivAt_const t (m1Plasma.thermalEnergy 20)).hasDerivWithinAt
  · have h0 : m1Plasma.alphaPower sv 20 + 60e6 - witP sv = 0 := by unfold witP; ring
    simpa [h0] using (hasDerivAt_const t (m1Plasma.thermalEnergy 20)).hasDerivWithinAt

/-! ### (d) Ignition point under constant confinement -/

/-- Supplied reactivity at 12 keV: `⟨σv⟩(12) ≤ 1.765e-22 m³/s` (window `[11, 12]`). -/
theorem sv_twelve_le (sv : ℝ → ℝ) [BoschHaleDT sv] : sv 12 ≤ (1.765e-22 : ℝ) := by
  have := (BoschHaleDT.windows (sv := sv) ⟨11, 12, 1.418e-22, 1.765e-22⟩
    (by simp [boschHaleWindows]) 12 (by norm_num) (by norm_num)).2
  norm_num at this ⊢; exact this

/-- Supplied reactivity at 13 keV: `⟨σv⟩(13) ≥ 2.052e-22 m³/s` (window `[13, 14]`). -/
theorem sv_thirteen_ge (sv : ℝ → ℝ) [BoschHaleDT sv] : (2.052e-22 : ℝ) ≤ sv 13 := by
  have := (BoschHaleDT.windows (sv := sv) ⟨13, 14, 2.052e-22, 2.430e-22⟩
    (by simp [boschHaleWindows]) 13 (by norm_num) (by norm_num)).1
  norm_num at this ⊢; exact this

/-- **Ignition bracket (constant `τ_E = 3.5 s`, `P_aux = 0`).** Net heating is negative at
12 keV (≤ −3.0 MW) and positive at 13 keV (≥ +9.8 MW). -/
theorem m1_ignition_bracket (sv : ℝ → ℝ) [BoschHaleDT sv] :
    m1Plasma.netHeating sv 0 3.5 12 < 0 ∧ 0 < m1Plasma.netHeating sv 0 3.5 13 := by
  constructor
  · have h := netHeating_le (p := m1Plasma) (sv := sv) (by norm_num : (0 : ℝ) ≤ 12)
      (sv_twelve_le sv) (le_refl 0) (by norm_num : (0 : ℝ) < 3.5) le_rfl
    have hq : 3.4641 ≤ Real.sqrt 12 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    refine h.trans_lt ?_
    rw [m1_netHeating_const]; norm_num; linarith
  · have h := netHeating_ge (p := m1Plasma) (sv := sv) (by norm_num : (0 : ℝ) ≤ 13)
      (sv_thirteen_ge sv) (le_refl 0) (by norm_num : (0 : ℝ) < 3.5) le_rfl
    have hq : Real.sqrt 13 ≤ 3.6056 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    refine lt_of_lt_of_le ?_ h
    rw [m1_netHeating_const]; norm_num; linarith

/-- **Root isolation.** Under constant `τ_E = 3.5 s` and no auxiliary power, some ignition
temperature `T_ign ∈ (12, 13)` keV has zero net heating (intermediate value theorem,
using continuity of the supplied reactivity). -/
theorem m1_ignition_root (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ∃ Tign ∈ Set.Ioo (12 : ℝ) 13, m1Plasma.netHeating sv 0 3.5 Tign = 0 := by
  obtain ⟨h12, h13⟩ := m1_ignition_bracket sv
  have hcont : ContinuousOn (fun x => m1Plasma.netHeating sv 0 3.5 x) (Set.Icc 12 13) := by
    have hsv : ContinuousOn sv (Set.Icc 12 13) :=
      BoschHaleDT.continuousOn.mono fun x hx => show (0 : ℝ) < x by linarith [hx.1]
    unfold netHeating alphaPower bremsPower lossPower thermalEnergy
    fun_prop
  obtain ⟨T, hT, he⟩ := intermediate_value_Ioo (by norm_num) hcont ⟨h12, h13⟩
  exact ⟨T, hT, he⟩

/-- **Instability of the ignition point.** For a trajectory with constant `τ_E = 3.5 s` and
no auxiliary power: starting at or below 12 keV it stays at or below 12 keV for all
`t ≥ 0` (it cannot climb through the ignition point), and starting at or above 13 keV it
stays at or above 13 keV (it cannot fall back). -/
theorem m1_ignition_unstable [BoschHaleDT sv]
    [PowerBalance m1Plasma sv (fun _ => 0) (fun _ => 3.5) T] :
    (T 0 ≤ 12 → ∀ t, 0 ≤ t → T t ≤ 12) ∧ (13 ≤ T 0 → ∀ t, 0 ≤ t → 13 ≤ T t) :=
  ⟨fun h0 => PowerBalance.upper_barrier (sv := sv) (Paux := fun _ => 0)
      (τE := fun _ => 3.5) h0 fun _ _ _ => (m1_ignition_bracket sv).1,
    fun h0 => PowerBalance.lower_barrier (sv := sv) (Paux := fun _ => 0)
      (τE := fun _ => 3.5) h0 fun _ _ _ => (m1_ignition_bracket sv).2⟩

end PlasmaLean.Design.BurnWindowScaling
