/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.PowerBalance
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Model rung M1: a reactor-scale 0-D D-T burn window

Data (labelled *synthetic reactor-scale data*, ITER-like): electron density
`n_e = 10²⁰ m⁻³`, plasma volume `V = 830 m³`, `Z_eff = 1.7` produced by a single carbon
impurity (`Z = 6`). Quasineutrality then fixes the fuel fraction `f_fuel = 0.86` and the
ion ratio `r_i = 53/60` (`carbon_fixture` in `Sanity/Fusion`), so the alpha power is
diluted by `f_fuel² ≈ 0.74` relative to a pure plasma. The reactivity is any `sv`
satisfying the supplied Bosch–Hale enclosures `BoschHaleDT` (kernel); the trajectory is
any `T(t)` satisfying the kernel law `PowerBalance`. No solution existence is proved.

Results (for every such trajectory, for all `t ≥ 0`, under the `PowerBalance`
hypotheses):

* `m1_sustained_burn`: if `P_aux ≥ 40 MW` and `τ_E ≥ 3.5 s` whenever `T ≤ 10 keV`,
  then `T(0) ≥ 10 keV ⇒ T(t) ≥ 10 keV`. At 10 keV: heating `P_α + P_aux ≥ 136.7 MW`,
  bremsstrahlung `≤ 23.9 MW`, transport loss `≤ 107.3 MW`; margin `≥ +5.5 MW`.
* `m1_ignited_burn`: pure self-heating (`P_aux ≥ 0`) with `τ_E ≥ 5.5 s` at `T ≤ 10 keV`
  (margin `≥ +4.5 MW`).
* `m1_constant_tau_runaway` (**honest negative result**): with `τ_E ≥ 2.5 s` and
  `P_aux ≥ 0`, net heating at 30 keV is positive (`≥ +77 MW`), so `T = 30 keV` is
  crossed upward: with undegraded confinement there is **no upper barrier at
  `T_hi = 30 keV`**. The hot stable equilibrium of the constant-`τ_E` model lies beyond
  the peak of `⟨σv⟩/T`, at several tens of keV. (Below the unstable ignition point,
  crossings are downward instead.)
* `m1_burn_window`: an upper barrier at `T_hi = 30 keV` **requires confinement
  degradation**, supplied as an explicit hypothesis: `τ_E ≤ 1.8 s` whenever
  `T ≥ 30 keV`, together with `40 MW ≤ P_aux ≤ 50 MW`. Under IPB98(y,2)-type power
  degradation `τ_E ∝ P^{-0.69}`, raising the heating power from ≈ 137 MW (at 10 keV)
  to ≈ 631 MW (at 30 keV) multiplies `τ_E` by ≈ 0.35 (3.5 s → ≈ 1.2 s), which makes
  the hypothesis *plausible*; it is not derived here. Margin at 30 keV: `≤ −36.7 MW`.
  Then `T(0) ∈ [10, 30] ⇒ T(t) ∈ [10, 30]`.
* `m1_fusion_yield`: inside the window, fusion energy over `[0, t_b]` is
  `≥ 4.8 × 10⁸ W · t_b` (≥ 486 MW of D-T fusion power at all times).
* `m1_hypotheses_satisfiable`: a constant 20 keV state satisfies every hypothesis (the
  `τ_E` crossing hypotheses are vacuous for it). `m1_crossing_witness`: a trajectory
  `T(t) = 10 + (1 − e^{−t})/2` starting exactly at `T_lo` with `P_aux = 40 MW` and an
  explicit `τ_E(t)` satisfies all hypotheses, the lower `τ_E` hypothesis being active
  at `t = 0` (`τ_E(0) ≥ 3.5 s`).

Square roots are enclosed by rational bounds; the remaining side conditions are exact
rational arithmetic (`norm_num`, `linarith`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.BurnWindow

open PlasmaLean.Fusion DTPlasma
/-- The M1 reactor-scale plasma: `n_e = 10²⁰ m⁻³`, `V = 830 m³`, `Z_eff = 1.7` from a
carbon impurity (`Z = 6`), hence `f_fuel = 0.86` and `r_i = 53/60`. -/
@[expose] def m1Plasma : DTPlasma := ⟨1e20, 830, 1.7, 0.86, 53 / 60⟩

/-- The M1 fuel fraction and ion ratio are the single-carbon-impurity values. -/
theorem m1Plasma_carbon :
    m1Plasma.fuelFraction = impurityFuelFraction 1.7 6 ∧
      m1Plasma.ionRatio = impurityIonRatio 1.7 6 := by
  constructor <;> norm_num [m1Plasma, impurityIonRatio, impurityFuelFraction]

/-- The M1 data are physical. -/
instance : PhysicalPlasma m1Plasma :=
  physicalPlasma_of_impurity (Z := 6) (by norm_num [m1Plasma]) (by norm_num [m1Plasma])
    (by norm_num [m1Plasma]) (by norm_num [m1Plasma]) m1Plasma_carbon.1 m1Plasma_carbon.2

/-- Explicit form of the M1 net heating with a constant reactivity value `s`. -/
theorem m1_netHeating_const (s P τ x : ℝ) :
    m1Plasma.netHeating (fun _ => s) P τ x =
      3500 * 1.602176634e-16 / 4 * (0.86 * 1e20 : ℝ) ^ 2 * s * 830 + P
        - 5.35e-37 * (1e20 : ℝ) ^ 2 * 1.7 * Real.sqrt x * 830
        - 3 / 2 * 1e20 * (1 + 53 / 60) * (x * 1.602176634e-16) * 830 / τ := by
  simp only [netHeating, alphaPower, bremsPower, lossPower, thermalEnergy, m1Plasma,
    alphaEnergy, keV, bremsCoeff]

/-- Numeric lower-crossing check at 10 keV (`P_aux = 40 MW`, `τ_E = 3.5 s`,
`⟨σv⟩ ≥ 1.124e-22 m³/s`): net heating is positive (≈ +5.5 MW). -/
theorem m1_lower_numeric : 0 < m1Plasma.netHeating (fun _ => 1.124e-22) 40e6 3.5 10 := by
  have h : Real.sqrt 10 ≤ 3.1623 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [m1_netHeating_const]; norm_num; linarith

/-- Numeric lower-crossing check for pure ignition at 10 keV (`P_aux = 0`, `τ_E = 5.5 s`;
≈ +4.5 MW). -/
theorem m1_ignited_numeric : 0 < m1Plasma.netHeating (fun _ => 1.124e-22) 0 5.5 10 := by
  have h : Real.sqrt 10 ≤ 3.1623 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [m1_netHeating_const]; norm_num; linarith

/-- Numeric upper-crossing check at 30 keV (`P_aux = 50 MW`, `τ_E = 1.8 s`,
`⟨σv⟩ ≤ 6.748e-22 m³/s`): net heating is negative (≈ −36.7 MW). -/
theorem m1_upper_numeric : m1Plasma.netHeating (fun _ => 6.748e-22) 50e6 1.8 30 < 0 := by
  have h : 5.477 ≤ Real.sqrt 30 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [m1_netHeating_const]; norm_num; linarith

/-- Numeric runaway check at 30 keV (`P_aux = 0`, `τ_E = 2.5 s`, `⟨σv⟩ ≥ 6.613e-22`):
net heating is positive (≈ +77 MW). -/
theorem m1_runaway_numeric : 0 < m1Plasma.netHeating (fun _ => 6.613e-22) 0 2.5 30 := by
  have h : Real.sqrt 30 ≤ 5.4773 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [m1_netHeating_const]; norm_num; linarith

theorem sv_ten_ge (sv : ℝ → ℝ) [BoschHaleDT sv] : (1.124e-22 : ℝ) ≤ sv 10 := by
  have := (BoschHaleDT.windows (sv := sv) ⟨10, 11, 1.124e-22, 1.448e-22⟩
    (by simp [boschHaleWindows]) 10 (by norm_num) (by norm_num)).1
  norm_num at this ⊢; exact this

/-- Supplied reactivity at 30 keV: `⟨σv⟩(30) ≤ 6.748e-22 m³/s` (window `[29, 30]`). -/
theorem sv_thirty_le (sv : ℝ → ℝ) [BoschHaleDT sv] : sv 30 ≤ (6.748e-22 : ℝ) := by
  have := (BoschHaleDT.windows (sv := sv) ⟨29, 30, 6.433e-22, 6.748e-22⟩
    (by simp [boschHaleWindows]) 30 (by norm_num) (by norm_num)).2
  norm_num at this ⊢; exact this

/-- Supplied reactivity at 30 keV: `⟨σv⟩(30) ≥ 6.613e-22 m³/s` (window `[30, 31]`). -/
theorem sv_thirty_ge (sv : ℝ → ℝ) [BoschHaleDT sv] : (6.613e-22 : ℝ) ≤ sv 30 := by
  have := (BoschHaleDT.windows (sv := sv) ⟨30, 31, 6.613e-22, 6.922e-22⟩
    (by simp [boschHaleWindows]) 30 (by norm_num) (by norm_num)).1
  norm_num at this ⊢; exact this

/-- Supplied reactivity at 20 keV: `⟨σv⟩(20) ≥ 4.286e-22 m³/s` (window `[20, 21]`). -/
theorem sv_twenty_ge (sv : ℝ → ℝ) [BoschHaleDT sv] : (4.286e-22 : ℝ) ≤ sv 20 := by
  have := (BoschHaleDT.windows (sv := sv) ⟨20, 21, 4.286e-22, 4.666e-22⟩
    (by simp [boschHaleWindows]) 20 (by norm_num) (by norm_num)).1
  norm_num at this ⊢; exact this


/-- Supplied reactivity at 10 keV: `⟨σv⟩(10) ≤ 1.148e-22 m³/s` (window `[9, 10]`). -/
theorem sv_ten_le (sv : ℝ → ℝ) [BoschHaleDT sv] : sv 10 ≤ (1.148e-22 : ℝ) := by
  have := (BoschHaleDT.windows (sv := sv) ⟨9, 10, 8.550e-23, 1.148e-22⟩
    (by simp [boschHaleWindows]) 10 (by norm_num) (by norm_num)).2
  norm_num at this ⊢; exact this

/-- Supplied reactivity on `[10, 11]` keV: `⟨σv⟩ ≥ 1.124e-22 m³/s`. -/
theorem sv_ge_on_ten_eleven (sv : ℝ → ℝ) [BoschHaleDT sv] {x : ℝ} (h1 : 10 ≤ x)
    (h2 : x ≤ 11) : (1.124e-22 : ℝ) ≤ sv x := by
  have := (BoschHaleDT.windows (sv := sv) ⟨10, 11, 1.124e-22, 1.448e-22⟩
    (by simp [boschHaleWindows]) x (by norm_num; exact h1) (by norm_num; exact h2)).1
  norm_num at this ⊢; exact this

variable {sv Paux τE T : ℝ → ℝ}

/-- **M1 sustained burn.** For every trajectory of the M1 plasma satisfying the balance
law with supplied Bosch–Hale reactivity, if `P_aux ≥ 40 MW` always and `τ_E ≥ 3.5 s`
whenever `T ≤ 10 keV`, then `T(0) ≥ 10 keV` implies `T(t) ≥ 10 keV` for all `t ≥ 0`. -/
theorem m1_sustained_burn [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    (hP : ∀ t, 0 ≤ t → 40e6 ≤ Paux t) (hτ : ∀ t, 0 ≤ t → T t ≤ 10 → 3.5 ≤ τE t)
    (h0 : 10 ≤ T 0) : ∀ t, 0 ≤ t → 10 ≤ T t :=
  PowerBalance.lower_barrier_of_bounds (by norm_num) (sv_ten_ge sv) (by norm_num)
    (fun t ht _ => hP t ht) (fun t ht he => hτ t ht he.le) m1_lower_numeric h0

/-- **M1 ignited burn.** With no auxiliary-power floor (`P_aux ≥ 0`) but `τ_E ≥ 5.5 s`
whenever `T ≤ 10 keV`, `T(t) ≥ 10 keV` for all `t ≥ 0` (under the `PowerBalance`
hypotheses). -/
theorem m1_ignited_burn [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    (hP : ∀ t, 0 ≤ t → 0 ≤ Paux t) (hτ : ∀ t, 0 ≤ t → T t ≤ 10 → 5.5 ≤ τE t)
    (h0 : 10 ≤ T 0) : ∀ t, 0 ≤ t → 10 ≤ T t :=
  PowerBalance.lower_barrier_of_bounds (by norm_num) (sv_ten_ge sv) (by norm_num)
    (fun t ht _ => hP t ht) (fun t ht he => hτ t ht he.le) m1_ignited_numeric h0

/-- **Honest negative result (no upper barrier at `T_hi = 30 keV` with undegraded
confinement).** If `P_aux ≥ 0` and `τ_E ≥ 2.5 s` at a time when `T = 30 keV`, the net
heating there is positive. -/
theorem m1_constant_tau_runaway [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    {t : ℝ} (hP : 0 ≤ Paux t) (hτ : 2.5 ≤ τE t) (hT : T t = 30) :
    0 < m1Plasma.netHeating sv (Paux t) (τE t) (T t) := by
  rw [hT]
  exact m1_runaway_numeric.trans_le
    (netHeating_ge (by norm_num) (sv_thirty_ge sv) hP (by norm_num) hτ)

/-- Under the runaway hypotheses at a time `t > 0`, `dT/dt > 0` at `T = 30 keV`. -/
theorem m1_constant_tau_runaway_deriv [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    {t : ℝ} (ht : 0 < t) (hP : 0 ≤ Paux t) (hτ : 2.5 ≤ τE t) (hT : T t = 30) :
    0 < deriv T t := by
  rw [(PowerBalance.temperature_hasDerivAt_of_pos (p := m1Plasma) (sv := sv) (Paux := Paux)
    (τE := τE) ht).deriv]
  exact div_pos (m1_constant_tau_runaway hP hτ hT) (heatCapacity_pos m1Plasma)

/-- **M1 burn window `[10, 30]` keV under supplied confinement degradation.** Hypotheses:
`40 MW ≤ P_aux ≤ 50 MW`; `τ_E ≥ 3.5 s` whenever `T ≤ 10 keV`; `τ_E ≤ 1.8 s` whenever
`T ≥ 30 keV` (supplied degradation, see module doc). Then `T(0) ∈ [10, 30]` implies
`T(t) ∈ [10, 30]` keV for all `t ≥ 0`. -/
theorem m1_burn_window [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    (hPlo : ∀ t, 0 ≤ t → 40e6 ≤ Paux t) (hPhi : ∀ t, 0 ≤ t → Paux t ≤ 50e6)
    (hτlo : ∀ t, 0 ≤ t → T t ≤ 10 → 3.5 ≤ τE t)
    (hτhi : ∀ t, 0 ≤ t → 30 ≤ T t → τE t ≤ 1.8)
    (h0 : T 0 ∈ Set.Icc 10 30) : ∀ t, 0 ≤ t → T t ∈ Set.Icc 10 30 := fun t ht =>
  ⟨m1_sustained_burn (sv := sv) hPlo hτlo h0.1 t ht,
    PowerBalance.upper_barrier_of_bounds (p := m1Plasma) (sv := sv) (Paux := Paux)
      (τE := τE) (T := T) (by norm_num) (sv_thirty_le sv)
      (fun t ht _ => hPhi t ht) (fun t ht he => hτhi t ht he.ge) m1_upper_numeric h0.2 t ht⟩

/-- **M1 burn yield.** Under the hypotheses of `m1_burn_window`, the D-T fusion energy
released during `[0, t_b]` is at least `4.8 × 10⁸ W · t_b`. -/
theorem m1_fusion_yield [BoschHaleDT sv] [PowerBalance m1Plasma sv Paux τE T]
    (hPlo : ∀ t, 0 ≤ t → 40e6 ≤ Paux t) (hPhi : ∀ t, 0 ≤ t → Paux t ≤ 50e6)
    (hτlo : ∀ t, 0 ≤ t → T t ≤ 10 → 3.5 ≤ τE t)
    (hτhi : ∀ t, 0 ≤ t → 30 ≤ T t → τE t ≤ 1.8)
    (h0 : T 0 ∈ Set.Icc 10 30) {tb : ℝ} (htb : 0 ≤ tb) :
    4.8e8 * tb ≤ ∫ t in (0 : ℝ)..tb, m1Plasma.fusionPower sv (T t) := by
  have hwin := m1_burn_window (sv := sv) hPlo hPhi hτlo hτhi h0
  have hy := PowerBalance.fusion_yield_ge (p := m1Plasma) (sv := sv) (Paux := Paux)
    (τE := τE) (T := T) htb (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (30 : ℝ) ≤ 60)
    (fun t ht => hwin t ht.1)
  have hf : 4.8e8 ≤ m1Plasma.fusionPower sv 10 := by
    have := sv_ten_ge sv
    simp only [fusionPower, m1Plasma, fusionEnergy, keV]
    norm_num; linarith
  nlinarith

/-- **Non-vacuity (steady witness).** For any reactivity satisfying the supplied
Bosch–Hale facts, the hypotheses of `m1_burn_window` are jointly satisfiable by a
constant 20 keV trajectory with `P_aux = 45 MW` and a constant balancing `τ_E > 0`.
For this witness both `τ_E` crossing hypotheses are **vacuous** (the temperature never
reaches 10 or 30 keV); see `m1_crossing_witness` for a witness that uses the lower one. -/
theorem m1_hypotheses_satisfiable (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ∃ Paux τE T : ℝ → ℝ, PowerBalance m1Plasma sv Paux τE T ∧
      (∀ t, 0 ≤ t → 40e6 ≤ Paux t) ∧ (∀ t, 0 ≤ t → Paux t ≤ 50e6) ∧
      (∀ t, 0 ≤ t → T t ≤ 10 → 3.5 ≤ τE t) ∧ (∀ t, 0 ≤ t → 30 ≤ T t → τE t ≤ 1.8) ∧
      T 0 ∈ Set.Icc 10 30 := by
  set D := m1Plasma.alphaPower sv 20 + 45e6 - m1Plasma.bremsPower 20 with hD
  have hDpos : 0 < D := by
    have h1 := sv_twenty_ge sv
    have h2 : Real.sqrt 20 ≤ 4.4722 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    simp only [hD, alphaPower, bremsPower, m1Plasma, alphaEnergy, keV, bremsCoeff]
    norm_num; nlinarith
  have hW : 0 < m1Plasma.thermalEnergy 20 := by
    simp only [thermalEnergy, m1Plasma, keV]; norm_num
  refine ⟨fun _ => 45e6, fun _ => m1Plasma.thermalEnergy 20 / D, fun _ => 20,
    ⟨fun _ _ => div_pos hW hDpos, fun t _ => ?_⟩, fun _ _ => by norm_num,
    fun _ _ => by norm_num, fun _ _ h => by norm_num at h, fun _ _ h => by norm_num at h,
    by norm_num⟩
  have h0 : m1Plasma.netHeating sv 45e6 (m1Plasma.thermalEnergy 20 / D) 20 = 0 := by
    simp only [netHeating, lossPower, div_div_eq_mul_div, mul_div_cancel_left₀ _ hW.ne']
    linarith
  simpa [h0] using (hasDerivAt_const t (m1Plasma.thermalEnergy 20)).hasDerivWithinAt

/-- Crossing-witness trajectory: `T(t) = 10 + (1 − e^{−t})/2` keV, starting at `T_lo`. -/
@[expose] def crossT (t : ℝ) : ℝ := 10 + 1 / 2 * (1 - Real.exp (-t))

/-- Net heating demanded by `crossT`, before transport loss: `P_α + 40 MW − P_br − dW/dt`. -/
@[expose] def crossDen (sv : ℝ → ℝ) (t : ℝ) : ℝ :=
  m1Plasma.alphaPower sv (crossT t) + 40e6 - m1Plasma.bremsPower (crossT t)
    - heatCapacity m1Plasma * (1 / 2 * Real.exp (-t))

/-- Confinement time making `crossT` an exact solution: `τ_E = W / crossDen`. -/
@[expose] def crossTau (sv : ℝ → ℝ) (t : ℝ) : ℝ :=
  m1Plasma.thermalEnergy (crossT t) / crossDen sv t

/-- `crossT` stays in `[10, 10.5]` keV for `t ≥ 0`. -/
theorem crossT_mem {t : ℝ} (ht : 0 ≤ t) : 10 ≤ crossT t ∧ crossT t ≤ 10.5 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.exp_pos (-t)
  unfold crossT; constructor <;> norm_num <;> linarith

/-- The witness denominator is positive (≥ ≈ 93 MW) for `t ≥ 0`. -/
theorem crossDen_pos (sv : ℝ → ℝ) [BoschHaleDT sv] {t : ℝ} (ht : 0 ≤ t) :
    0 < crossDen sv t := by
  obtain ⟨h1, h2⟩ := crossT_mem ht
  have hs := sv_ge_on_ten_eleven sv h1 (by linarith)
  have hq : Real.sqrt (crossT t) ≤ 3.2404 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simp only [crossDen, alphaPower, bremsPower, heatCapacity, m1Plasma, alphaEnergy, keV,
    bremsCoeff]
  norm_num; linarith

/-- **Non-vacuity with an active crossing hypothesis.** For any reactivity satisfying the
supplied Bosch–Hale facts, the trajectory `crossT` (starting exactly at `T_lo = 10 keV`)
with `P_aux = 40 MW` and `τ_E = crossTau` satisfies `PowerBalance` and every hypothesis
of `m1_burn_window`; the lower `τ_E` hypothesis is used at `t = 0`, where `T = T_lo`. -/
theorem m1_crossing_witness (sv : ℝ → ℝ) [BoschHaleDT sv] :
    PowerBalance m1Plasma sv (fun _ => 40e6) (crossTau sv) crossT ∧
      (∀ t, 0 ≤ t → crossT t ≤ 10 → 3.5 ≤ crossTau sv t) ∧
      (∀ t, 0 ≤ t → 30 ≤ crossT t → crossTau sv t ≤ 1.8) ∧
      crossT 0 = 10 := by
  have hc := heatCapacity_pos m1Plasma
  have hW : ∀ t, 0 ≤ t → 0 < m1Plasma.thermalEnergy (crossT t) := fun t ht => by
    rw [thermalEnergy_eq]; exact mul_pos hc (by linarith [(crossT_mem ht).1])
  have h00 : crossT 0 = 10 := by simp [crossT]
  refine ⟨⟨fun t ht => div_pos (hW t ht) (crossDen_pos sv ht), fun t ht => ?_⟩, ?_, ?_, h00⟩
  · have hT : HasDerivAt crossT (1 / 2 * Real.exp (-t)) t := by
      have := ((((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1).const_mul
        (1 / 2)).const_add 10
      convert this using 1
      · funext s; rfl
      · ring
    have hE : HasDerivAt (fun s => m1Plasma.thermalEnergy (crossT s))
        (heatCapacity m1Plasma * (1 / 2 * Real.exp (-t))) t := by
      simp only [thermalEnergy_eq]; exact hT.const_mul _
    convert hE.hasDerivWithinAt using 1
    simp only [netHeating, lossPower, crossTau,
      div_div_cancel₀ (hW t ht).ne', crossDen]
    ring
  · intro t ht hle
    have ht0 : t = 0 := by
      have := (crossT_mem ht).1
      have he : Real.exp (-t) = 1 := by unfold crossT at hle this; linarith
      have := Real.exp_eq_one_iff (-t) |>.mp he
      linarith
    subst ht0
    rw [crossTau, le_div_iff₀ (crossDen_pos sv le_rfl), h00]
    have hs := sv_ten_le sv
    have hq : 3.162 ≤ Real.sqrt 10 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    simp only [crossDen, h00, alphaPower, bremsPower, heatCapacity, thermalEnergy, m1Plasma,
      alphaEnergy, keV, bremsCoeff, neg_zero, Real.exp_zero]
    norm_num; linarith
  · intro t ht h30
    linarith [(crossT_mem ht).2]

end PlasmaLean.Design.BurnWindow
