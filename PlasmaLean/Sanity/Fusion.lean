/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Fusion
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Sanity checks for the 0-D D-T fusion kernel

Checks of `PlasmaLean.Kernel.Fusion` using only the kernel definitions and classes:

* zero density gives zero thermal energy and zero alpha, fusion and bremsstrahlung power;
* `P_α ≥ 0`, `P_br ≥ 0`, and `P_α` is monotone on `[1, 60]` keV (supplied monotonicity);
* the supplied Bosch–Hale table is internally consistent (`lo ≤ hi`, `svLo ≤ svHi`,
  `0 ≤ svLo`), a necessary condition for `BoschHaleDT` to be satisfiable;
* fuel dilution: `f_fuel = 1` / `r_i = 1` recover the undiluted formulas, `P_α` is
  monotone in `f_fuel`, and the single-impurity formulas
  `f_fuel = 1 − (Z_eff − 1)/(Z − 1)`, `r_i = f + (1 − f)/Z` follow from quasineutrality
  and the definition of `Z_eff` (carbon fixture: `Z_eff = 1.7 ⇒ f_fuel = 0.86`);
* a constant-temperature trajectory satisfies `PowerBalance` exactly when the net
  heating vanishes;
* Lawson-type ignition criterion: with `P_aux = 0`, net heating is positive iff
  `n τ_E > (3/2)(1 + r_i) T keV / ((E_α/4) f_fuel² ⟨σv⟩ − C_br Z_eff √T)`, and an ignited
  steady state exists iff equality holds;
* degenerate case: without alpha heating and auxiliary power the temperature strictly
  decreases while positive.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.Fusion

open PlasmaLean.Fusion DTPlasma

/-- Zero density: zero thermal energy. -/
theorem thermalEnergy_zero_density (p : DTPlasma) (h : p.n = 0) (T : ℝ) :
    p.thermalEnergy T = 0 := by simp [thermalEnergy, h]

/-- Zero density: zero alpha power. -/
theorem alphaPower_zero_density (p : DTPlasma) (h : p.n = 0) (sv : ℝ → ℝ) (T : ℝ) :
    p.alphaPower sv T = 0 := by simp [alphaPower, h]

/-- Zero density: zero fusion power. -/
theorem fusionPower_zero_density (p : DTPlasma) (h : p.n = 0) (sv : ℝ → ℝ) (T : ℝ) :
    p.fusionPower sv T = 0 := by simp [fusionPower, h]

/-- Zero density: zero bremsstrahlung. -/
theorem bremsPower_zero_density (p : DTPlasma) (h : p.n = 0) (T : ℝ) :
    p.bremsPower T = 0 := by simp [bremsPower, h]

/-- Zero density: the net heating is just the auxiliary power. -/
theorem netHeating_zero_density (p : DTPlasma) (h : p.n = 0) (sv : ℝ → ℝ) (P τ T : ℝ) :
    p.netHeating sv P τ T = P := by
  simp [netHeating, alphaPower, bremsPower, lossPower, thermalEnergy, h]

/-- Alpha heating is nonnegative at nonnegative temperature. -/
theorem alphaPower_nonneg (p : DTPlasma) [PhysicalPlasma p] (sv : ℝ → ℝ) [BoschHaleDT sv]
    {T : ℝ} (hT : 0 ≤ T) : 0 ≤ p.alphaPower sv T := by
  have := PhysicalPlasma.V_pos (p := p)
  have := BoschHaleDT.nonneg (sv := sv) T hT
  unfold alphaPower alphaEnergy keV; positivity

/-- Bremsstrahlung is nonnegative. -/
theorem bremsPower_nonneg (p : DTPlasma) [PhysicalPlasma p] (T : ℝ) : 0 ≤ p.bremsPower T := by
  have := PhysicalPlasma.V_pos (p := p)
  have := PhysicalPlasma.Zeff_ge_one (p := p)
  unfold bremsPower bremsCoeff; positivity

/-- Fusion power is `E_fus/E_α = 17589/3500` times the alpha power. -/
theorem fusionPower_eq (p : DTPlasma) (sv : ℝ → ℝ) (T : ℝ) :
    p.fusionPower sv T = 17589 / 3500 * p.alphaPower sv T := by
  unfold fusionPower alphaPower fusionEnergy alphaEnergy; ring

/-- Alpha power increases with temperature on `[1, 60]` keV. -/
theorem alphaPower_monotoneOn (p : DTPlasma) [PhysicalPlasma p] (sv : ℝ → ℝ)
    [BoschHaleDT sv] : MonotoneOn (p.alphaPower sv) (Set.Icc 1 60) := by
  intro x hx y hy hxy
  have := PhysicalPlasma.V_pos (p := p)
  have := BoschHaleDT.monotoneOn (sv := sv) hx hy hxy
  unfold alphaPower alphaEnergy keV; gcongr

/-- The supplied table has 61 windows. -/
theorem boschHaleWindows_length : boschHaleWindows.length = 61 := rfl

/-- Consistency of the supplied table: every window is a nonempty keV interval with a
nonempty, nonnegative reactivity enclosure. -/
theorem boschHaleWindows_consistent :
    ∀ w ∈ boschHaleWindows, w.lo ≤ w.hi ∧ 0 ≤ w.svLo ∧ w.svLo ≤ w.svHi := by
  simp only [boschHaleWindows, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

/-- Rejected fixture: a claimed reactivity of `2e-22 m³/s` at 10 keV contradicts the
supplied enclosure (`⟨σv⟩(10 keV) ≤ 1.448e-22`). -/
theorem boschHale_rejects_large_value (sv : ℝ → ℝ) [BoschHaleDT sv] : sv 10 ≠ 2e-22 := by
  have h := (BoschHaleDT.windows (sv := sv) ⟨10, 11, 1.124e-22, 1.448e-22⟩
    (by simp [boschHaleWindows]) 10 (by norm_num) (by norm_num)).2
  intro he; rw [he] at h; norm_num at h

/-- Undiluted idealization: with `f_fuel = 1` the alpha power is `(E_α/4) n² ⟨σv⟩ V`. -/
theorem alphaPower_undiluted (p : DTPlasma) (h : p.fuelFraction = 1) (sv : ℝ → ℝ) (T : ℝ) :
    p.alphaPower sv T = alphaEnergy / 4 * p.n ^ 2 * sv T * p.V := by
  simp [alphaPower, h]

/-- Pure plasma: with `r_i = 1` the thermal energy is `3 n T V`. -/
theorem thermalEnergy_pure (p : DTPlasma) (h : p.ionRatio = 1) (T : ℝ) :
    p.thermalEnergy T = 3 * p.n * (T * keV) * p.V := by
  simp only [thermalEnergy, h]; ring

/-- Dilution lowers alpha heating: `P_α` is monotone in the fuel fraction. -/
theorem alphaPower_mono_fuel (p : DTPlasma) [PhysicalPlasma p] (sv : ℝ → ℝ) [BoschHaleDT sv]
    {T f₁ f₂ : ℝ} (hT : 0 ≤ T) (hf₁ : 0 ≤ f₁) (hf : f₁ ≤ f₂) :
    ({ p with fuelFraction := f₁ } : DTPlasma).alphaPower sv T ≤
      ({ p with fuelFraction := f₂ } : DTPlasma).alphaPower sv T := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  have := BoschHaleDT.nonneg (sv := sv) T hT
  simp only [alphaPower, alphaEnergy, keV]; gcongr

/-- **Single-impurity consistency.** If `n_e = n_fuel + Z n_imp` (quasineutrality) and
`Z_eff n_e = n_fuel + Z² n_imp`, with `Z ≠ 0, 1`, then
`n_fuel/n_e = 1 − (Z_eff − 1)/(Z − 1)` and `(n_fuel + n_imp)/n_e = f + (1 − f)/Z`. -/
theorem impurity_consistency {ne nf ni Z Zeff : ℝ} (hne : ne ≠ 0) (hZ : Z ≠ 0) (hZ1 : Z ≠ 1)
    (hq : ne = nf + Z * ni) (hz : Zeff * ne = nf + Z ^ 2 * ni) :
    nf / ne = impurityFuelFraction Zeff Z ∧ (nf + ni) / ne = impurityIonRatio Zeff Z := by
  have hZ1' : Z - 1 ≠ 0 := sub_ne_zero.mpr hZ1
  have hf : nf / ne = impurityFuelFraction Zeff Z := by
    unfold impurityFuelFraction
    field_simp
    linear_combination hz - Z * hq
  refine ⟨hf, ?_⟩
  unfold impurityIonRatio
  rw [← hf]
  field_simp
  linear_combination (-1 : ℝ) * hq

/-- The single-impurity parameters are physical when `1 ≤ Z_eff < Z`. -/
theorem impurity_physical {n V Zeff Z : ℝ} (hn : 0 < n) (hV : 0 < V) (h1 : 1 ≤ Zeff)
    (hZ : Zeff < Z) :
    PhysicalPlasma ⟨n, V, Zeff, impurityFuelFraction Zeff Z, impurityIonRatio Zeff Z⟩ :=
  physicalPlasma_of_impurity hn hV h1 hZ rfl rfl

/-- Carbon fixture: `Z_eff = 1.7`, `Z = 6` gives `f_fuel = 0.86`, `r_i = 53/60`. -/
theorem carbon_fixture :
    impurityFuelFraction 1.7 6 = 0.86 ∧ impurityIonRatio 1.7 6 = 53 / 60 := by
  constructor <;> norm_num [impurityIonRatio, impurityFuelFraction]

/-- **Steady states.** A constant temperature `T₀` with constant `P_aux`, `τ_E` satisfies
the balance law exactly when `τ_E > 0` and the net heating vanishes. -/
theorem steady_state_iff (p : DTPlasma) (sv : ℝ → ℝ) (P τ T₀ : ℝ) :
    PowerBalance p sv (fun _ => P) (fun _ => τ) (fun _ => T₀) ↔
      0 < τ ∧ p.netHeating sv P τ T₀ = 0 := by
  constructor
  · intro h
    exact ⟨h.tauE_pos 0 le_rfl, (((h.balance 1 zero_le_one).hasDerivAt
      (Ici_mem_nhds one_pos)).unique (hasDerivAt_const 1 _)).trans rfl⟩
  · rintro ⟨hτ, h0⟩
    exact ⟨fun _ _ => hτ, fun t _ => by
      simpa [h0] using (hasDerivAt_const t (p.thermalEnergy T₀)).hasDerivWithinAt⟩

/-- Alpha-minus-bremsstrahlung coefficient
`D(T) = (E_α/4) f_fuel² ⟨σv⟩(T) − C_br Z_eff √T` (W m³), so that
`P_α − P_br = n² D(T) V`. -/
@[expose] def burnCoefficient (p : DTPlasma) (sv : ℝ → ℝ) (T : ℝ) : ℝ :=
  alphaEnergy / 4 * p.fuelFraction ^ 2 * sv T - bremsCoeff * p.Zeff * Real.sqrt T

/-- Lawson-type ignition threshold for `n τ_E` (m⁻³ s): `(3/2)(1 + r_i) T keV / D(T)`. -/
@[expose] def lawsonThreshold (p : DTPlasma) (sv : ℝ → ℝ) (T : ℝ) : ℝ :=
  3 / 2 * (1 + p.ionRatio) * T * keV / burnCoefficient p sv T

/-- Factorization: with `P_aux = 0`,
`P_net = (n V / τ)(n τ D(T) − (3/2)(1 + r_i) T keV)`. -/
theorem netHeating_ignited_eq (p : DTPlasma) (sv : ℝ → ℝ) {τ : ℝ} (hτ : τ ≠ 0) (T : ℝ) :
    p.netHeating sv 0 τ T = p.n * p.V / τ *
      (p.n * τ * burnCoefficient p sv T - 3 / 2 * (1 + p.ionRatio) * T * keV) := by
  unfold netHeating alphaPower bremsPower lossPower thermalEnergy burnCoefficient
  field_simp
  ring

/-- **Lawson criterion recovered.** For a physical plasma with `τ_E > 0` and `D(T) > 0`,
the self-heated (no `P_aux`) net heating is positive iff `n τ_E` exceeds the threshold. -/
theorem lawson_ignition_iff (p : DTPlasma) [PhysicalPlasma p] (sv : ℝ → ℝ) {τ T : ℝ}
    (hτ : 0 < τ) (hD : 0 < burnCoefficient p sv T) :
    0 < p.netHeating sv 0 τ T ↔ lawsonThreshold p sv T < p.n * τ := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  rw [netHeating_ignited_eq p sv hτ.ne', mul_pos_iff_of_pos_left (by positivity),
    lawsonThreshold, div_lt_iff₀ hD]
  constructor <;> intro h <;> linarith

/-- **Ignited steady state.** With `P_aux = 0`, a constant temperature `T₀` solves the
balance law iff `n τ_E` equals the Lawson threshold (when `D(T₀) > 0`, `τ_E > 0`). -/
theorem ignited_steady_state_iff (p : DTPlasma) [PhysicalPlasma p] (sv : ℝ → ℝ) {τ T₀ : ℝ}
    (hτ : 0 < τ) (hD : 0 < burnCoefficient p sv T₀) :
    PowerBalance p sv (fun _ => 0) (fun _ => τ) (fun _ => T₀) ↔
      p.n * τ = lawsonThreshold p sv T₀ := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  rw [steady_state_iff, netHeating_ignited_eq p sv hτ.ne', lawsonThreshold,
    eq_div_iff hD.ne']
  constructor
  · rintro ⟨-, h⟩
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by positivity)
    · linarith
  · intro h
    refine ⟨hτ, ?_⟩
    rw [show p.n * τ * burnCoefficient p sv T₀ - 3 / 2 * (1 + p.ionRatio) * T₀ * keV = 0
      by linarith, mul_zero]

/-- Heat capacity positivity used below: `(3/2) n (1 + r_i) keV V > 0`. -/
theorem heatCap_pos (p : DTPlasma) [PhysicalPlasma p] :
    0 < 3 / 2 * p.n * (1 + p.ionRatio) * keV * p.V := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  have : 0 < 1 + p.ionRatio := by
    linarith [PhysicalPlasma.fuel_pos (p := p), PhysicalPlasma.fuel_le_ions (p := p)]
  unfold keV; positivity

/-- **Degenerate case (no alpha heating, no auxiliary power).** The net heating is
negative whenever the temperature is positive. -/
theorem noAlpha_energy_deriv_neg (p : DTPlasma) [PhysicalPlasma p] {τE T : ℝ → ℝ}
    [h : PowerBalance p (fun _ => 0) (fun _ => 0) τE T] {t : ℝ} (ht : 0 ≤ t) (hT : 0 < T t) :
    p.netHeating (fun _ => 0) 0 (τE t) (T t) < 0 := by
  have := h.tauE_pos t ht
  have hb := bremsPower_nonneg p (T t)
  have hc := heatCap_pos p
  have hl : 0 < p.lossPower (τE t) (T t) := by
    unfold lossPower
    have : p.thermalEnergy (T t) = 3 / 2 * p.n * (1 + p.ionRatio) * keV * p.V * T t := by
      unfold thermalEnergy; ring
    rw [this]; positivity
  unfold netHeating alphaPower at *; simp only [mul_zero, zero_mul, add_zero, zero_sub]
  linarith

/-- **Degenerate case.** Without alpha heating and auxiliary power, a trajectory that
stays positive is strictly decreasing on `[0, ∞)`. -/
theorem noAlpha_strictAnti (p : DTPlasma) [PhysicalPlasma p] {τE T : ℝ → ℝ}
    [h : PowerBalance p (fun _ => 0) (fun _ => 0) τE T] (hpos : ∀ t, 0 ≤ t → 0 < T t) :
    StrictAntiOn T (Set.Ici 0) := by
  have hc := heatCap_pos p
  have hW : ∀ s, p.thermalEnergy (T s) = (3 / 2 * p.n * (1 + p.ionRatio) * keV * p.V) * T s :=
    fun s => by unfold thermalEnergy; ring
  have hTd : ∀ t, 0 ≤ t → HasDerivWithinAt T
      (p.netHeating (fun _ => 0) 0 (τE t) (T t) / (3 / 2 * p.n * (1 + p.ionRatio) * keV * p.V))
      (Set.Ici 0) t := fun t ht => by
    have hd := (h.balance t ht).div_const (3 / 2 * p.n * (1 + p.ionRatio) * keV * p.V)
    simp only [hW, mul_div_cancel_left₀ _ hc.ne'] at hd
    simpa using hd
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun t ht => (hTd t ht).continuousWithinAt)
  intro t ht
  rw [interior_Ici] at ht
  rw [((hTd t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht)).deriv]
  exact div_neg_of_neg_of_pos (noAlpha_energy_deriv_neg p (le_of_lt ht) (hpos t ht.le)) hc

end PlasmaLean.Sanity.Fusion
