/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Zero-dimensional D-T burning-plasma kernel

**This is a domain kernel file** (not an extension of Lean's logical kernel). It
introduces no axioms: every physical fact enters as a definition or as a typeclass
of supplied empirical data/laws.

## Model

A spatially uniform ("0-D") deuterium-tritium plasma with electron density `n_e = n`
(m⁻³), volume `V` (m³), common electron and ion temperature `T` measured in **keV**,
effective charge `Z_eff`, **fuel fraction** `f_fuel = (n_D + n_T)/n_e ∈ (0, 1]` with a
50:50 mix (`n_D = n_T = f_fuel n/2`), and **ion ratio** `r_i = n_ions/n_e` (all ion
species, fuel plus impurities). Impurities therefore dilute the fuel: quasineutrality
`n_e = n_fuel + Σ Z_k n_k` forces `f_fuel < 1` whenever `Z_eff > 1`. For a single
impurity species of charge `Z` the consistent values are
`f_fuel = 1 − (Z_eff − 1)/(Z − 1)` and `r_i = f_fuel + (1 − f_fuel)/Z`
(`impurityFuelFraction`, `impurityIonRatio`; derivation checked in `Sanity/Fusion`).
The admissibility class `PhysicalPlasma` requires such a quasineutral composition
(`QuasineutralComposition`: finitely many non-fuel species with charges `Z_k ≥ 1`), so
`Z_eff`, `f_fuel` and `r_i` cannot be chosen independently.
All powers are in W and energies in J. The keV→J conversion `keV = 1.602176634e-16 J`
(exact SI value of the elementary charge times 10³) is explicit.

* thermal energy `W = (3/2)(n_e + n_ions) T V = (3/2) n (1 + r_i) T V`
  (`DTPlasma.thermalEnergy`);
* alpha heating `P_α = (E_α/4) (f_fuel n)² ⟨σv⟩(T) V` with `E_α = 3.5 MeV`, because the
  reaction rate density is `n_D n_T ⟨σv⟩ = (f_fuel n)²⟨σv⟩/4` (`DTPlasma.alphaPower`);
* total fusion power `P_fus = (E_fus/4) (f_fuel n)² ⟨σv⟩ V` with `E_fus = 17.589 MeV`;
* bremsstrahlung `P_br = C_br n² Z_eff √T V` (`n_e Σ Z_k² n_k = Z_eff n_e²`) with
  `C_br = 5.35e-37 W m³ keV^(-1/2)` (J. Wesson, *Tokamaks*, 4th ed., OUP 2011;
  equivalently the NRL Plasma Formulary value `1.69e-32 N_e T_e^{1/2} Σ Z² N_i W cm⁻³`
  with `T_e` in eV, converted to SI and keV);
* transport loss `W/τ_E` with a supplied confinement time `τ_E`;
* auxiliary heating power `P_aux`.

The reactivity `⟨σv⟩(T)` (m³/s) is an arbitrary function `sv : ℝ → ℝ`; it enters
**only** through the typeclass `BoschHaleDT sv`, which records supplied rational
enclosures on keV windows (see `boschHaleWindows`), continuity, and monotonicity on
`[1, 60]` keV. These are **supplied data, not proved**: they come from the
Bosch–Hale parametrization (H.-S. Bosch and G. M. Hale, *Improved formulas for
fusion cross-sections and thermal reactivities*, Nucl. Fusion **32** (1992) 611,
Table VII/eq. (12)–(14), D-T fit valid on 0.2–100 keV) evaluated in 50-digit decimal
arithmetic, widened by a relative ±1 % margin for fit accuracy, and rounded outward
to four significant digits.

The energy balance `dW/dt = P_α + P_aux − P_br − W/τ_E` is the typeclass
`PowerBalance` on a supplied trajectory `T(t)`; no existence of solutions is claimed.
Neglected: line radiation, synchrotron radiation, helium ash dilution, fuel burn-up,
alpha slowing-down delay and profile effects.
-/

public section
noncomputable section

namespace PlasmaLean.Fusion

/-- Joules per keV (exact SI: `1.602176634e-19 C × 10³ V`). -/
@[expose] def keV : ℝ := 1.602176634e-16

/-- Alpha-particle birth energy in J: `3.5 MeV = 3500 keV`. -/
@[expose] def alphaEnergy : ℝ := 3500 * keV

/-- Energy released per D-T reaction in J: `17.589 MeV` (alpha plus neutron). -/
@[expose] def fusionEnergy : ℝ := 17589 * keV

/-- Bremsstrahlung coefficient `C_br = 5.35e-37 W m³ keV^(-1/2)` (Wesson, *Tokamaks*;
NRL Plasma Formulary, converted to SI with `T` in keV). -/
@[expose] def bremsCoeff : ℝ := 5.35e-37

/-- Parameters of a 0-D D-T plasma: electron density `n` (m⁻³), volume `V` (m³),
effective charge `Zeff`, fuel fraction `fuelFraction = (n_D + n_T)/n_e` and ion ratio
`ionRatio = n_ions/n_e`. Physical admissibility is the separate class `PhysicalPlasma`,
so that degenerate data (e.g. `n = 0`) remain expressible. -/
structure DTPlasma where
  /-- Electron density (= total ion density), m⁻³. -/
  n : ℝ
  /-- Plasma volume, m³. -/
  V : ℝ
  /-- Effective ion charge (dimensionless). -/
  Zeff : ℝ
  /-- Fuel fraction `(n_D + n_T)/n_e` (dimensionless, 50:50 D-T mix). -/
  fuelFraction : ℝ
  /-- Ion ratio `n_ions/n_e`, all ion species (dimensionless). -/
  ionRatio : ℝ

/-- Fuel fraction for a single impurity species of charge `Z`:
`f_fuel = 1 − (Z_eff − 1)/(Z − 1)` (from quasineutrality and the definition of `Z_eff`). -/
@[expose] def impurityFuelFraction (Zeff Z : ℝ) : ℝ := 1 - (Zeff - 1) / (Z - 1)

/-- Ion ratio for a single impurity species of charge `Z`: `r_i = f + (1 − f)/Z`. -/
@[expose] def impurityIonRatio (Zeff Z : ℝ) : ℝ :=
  impurityFuelFraction Zeff Z + (1 - impurityFuelFraction Zeff Z) / Z

/-- **Quasineutral composition.** The electrons are supplied by the fuel ions (charge 1,
density `f_fuel n_e`) and by finitely many non-fuel ion species `i : Fin k` of charge
`Z i ≥ 1` and density `c i · n_e` with `c i ≥ 0`, such that (all densities divided by `n_e`)
* quasineutrality holds: `f_fuel + Σ Z_i c_i = 1`;
* `Z_eff` is the effective charge of this mixture: `f_fuel + Σ Z_i² c_i = Z_eff`;
* `r_i` counts all ions: `r_i = f_fuel + Σ c_i`.

Consequences: `f_fuel ≤ r_i ≤ 1`, `Z_eff ≥ 1`, and `f_fuel = 1` forces `Z_eff = 1`
(`QuasineutralComposition.Zeff_eq_one_of_fuel_one`). A single impurity of charge `Z > 1`
with the values `impurityFuelFraction`, `impurityIonRatio` is an instance
(`quasineutralComposition_of_impurity`). -/
@[expose] def QuasineutralComposition (p : DTPlasma) : Prop :=
  ∃ (k : ℕ) (Z c : Fin k → ℝ), (∀ i, 1 ≤ Z i) ∧ (∀ i, 0 ≤ c i) ∧
    p.fuelFraction + ∑ i, Z i * c i = 1 ∧
    p.fuelFraction + ∑ i, Z i ^ 2 * c i = p.Zeff ∧
    p.ionRatio = p.fuelFraction + ∑ i, c i

namespace QuasineutralComposition

variable {p : DTPlasma}

/-- The fuel fraction is at most `1`. -/
theorem fuel_le_one (h : QuasineutralComposition p) : p.fuelFraction ≤ 1 := by
  obtain ⟨k, Z, c, hZ, hc, hq, -, -⟩ := h
  have : 0 ≤ ∑ i, Z i * c i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (zero_le_one.trans (hZ i)) (hc i)
  linarith

/-- Fuel ions are among all ions: `f_fuel ≤ r_i`. -/
theorem fuel_le_ions (h : QuasineutralComposition p) : p.fuelFraction ≤ p.ionRatio := by
  obtain ⟨k, Z, c, -, hc, -, -, hr⟩ := h
  have : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  linarith

/-- Every ion carries at least one charge: `r_i ≤ 1`. -/
theorem ions_le_one (h : QuasineutralComposition p) : p.ionRatio ≤ 1 := by
  obtain ⟨k, Z, c, hZ, hc, hq, -, hr⟩ := h
  have : ∑ i, c i ≤ ∑ i, Z i * c i :=
    Finset.sum_le_sum fun i _ => le_mul_of_one_le_left (hc i) (hZ i)
  linarith

/-- The effective charge is at least `1`. -/
theorem Zeff_ge_one (h : QuasineutralComposition p) : 1 ≤ p.Zeff := by
  obtain ⟨k, Z, c, hZ, hc, hq, hz, -⟩ := h
  have : ∑ i, Z i * c i ≤ ∑ i, Z i ^ 2 * c i :=
    Finset.sum_le_sum fun i _ => by
      have h1 : Z i ≤ Z i ^ 2 := by nlinarith [hZ i]
      exact mul_le_mul_of_nonneg_right h1 (hc i)
  linarith

/-- **No impurity electrons, no impurities.** If the fuel supplies every electron
(`f_fuel = 1`), then `Z_eff = 1`. -/
theorem Zeff_eq_one_of_fuel_one (h : QuasineutralComposition p) (hf : p.fuelFraction = 1) :
    p.Zeff = 1 := by
  obtain ⟨k, Z, c, hZ, hc, hq, hz, -⟩ := h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ Z i * c i := fun i _ =>
    mul_nonneg (zero_le_one.trans (hZ i)) (hc i)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by linarith)
  have h2 : ∑ i, Z i ^ 2 * c i = 0 := Finset.sum_eq_zero fun i hi => by
    have := hzero i hi
    calc Z i ^ 2 * c i = Z i * (Z i * c i) := by ring
      _ = 0 := by rw [this, mul_zero]
  linarith

/-- An effective charge above `1` forces fuel dilution: `Z_eff > 1 → f_fuel < 1`. -/
theorem fuel_lt_one_of_Zeff_gt_one (h : QuasineutralComposition p) (hZ : 1 < p.Zeff) :
    p.fuelFraction < 1 :=
  lt_of_le_of_ne h.fuel_le_one fun hf => by
    have := h.Zeff_eq_one_of_fuel_one hf
    linarith

end QuasineutralComposition

/-- A single impurity species of charge `Z > 1` with `1 ≤ Z_eff` and the fuel fraction and ion
ratio `impurityFuelFraction Z_eff Z`, `impurityIonRatio Z_eff Z` is a quasineutral
composition (impurity density `(1 − f_fuel)/Z` per electron). -/
theorem quasineutralComposition_of_impurity {p : DTPlasma} {Z : ℝ} (hZ : 1 < Z)
    (hZeff : 1 ≤ p.Zeff) (hf : p.fuelFraction = impurityFuelFraction p.Zeff Z)
    (hr : p.ionRatio = impurityIonRatio p.Zeff Z) : QuasineutralComposition p := by
  have hZ1 : Z - 1 ≠ 0 := sub_ne_zero.mpr hZ.ne'
  have hZ0 : Z ≠ 0 := (zero_lt_one.trans hZ).ne'
  have h1f : 1 - p.fuelFraction = (p.Zeff - 1) / (Z - 1) := by
    rw [hf, impurityFuelFraction]; ring
  have hc : 0 ≤ (1 - p.fuelFraction) / Z := by
    rw [h1f]; exact div_nonneg (div_nonneg (by linarith) (by linarith)) (by linarith)
  refine ⟨1, fun _ => Z, fun _ => (1 - p.fuelFraction) / Z, fun _ => hZ.le, fun _ => hc,
    ?_, ?_, ?_⟩ <;> simp only [Fin.sum_univ_one]
  · field_simp; ring
  · have : p.fuelFraction + Z ^ 2 * ((1 - p.fuelFraction) / Z) =
        1 + (Z - 1) * (1 - p.fuelFraction) := by field_simp; ring
    rw [this, h1f]; field_simp; ring
  · rw [hr, impurityIonRatio, ← hf]

/-- Physical admissibility: positive density, volume and fuel fraction, and a quasineutral
composition (`QuasineutralComposition`) linking `Z_eff`, `f_fuel` and `r_i` through an
explicit list of non-fuel ion species. The bounds `Z_eff ≥ 1` and `0 < f_fuel ≤ r_i ≤ 1` are
consequences (`PhysicalPlasma.Zeff_ge_one`, `.fuel_le_ions`, `.ions_le_one`), and so is
`f_fuel = 1 → Z_eff = 1`. -/
class PhysicalPlasma (p : DTPlasma) : Prop where
  n_pos : 0 < p.n
  V_pos : 0 < p.V
  fuel_pos : 0 < p.fuelFraction
  composition : QuasineutralComposition p

namespace PhysicalPlasma

variable {p : DTPlasma} [h : PhysicalPlasma p]
include h

/-- `Z_eff ≥ 1` for a physical plasma. -/
theorem Zeff_ge_one : 1 ≤ p.Zeff := h.composition.Zeff_ge_one

/-- `f_fuel ≤ r_i` for a physical plasma. -/
theorem fuel_le_ions : p.fuelFraction ≤ p.ionRatio := h.composition.fuel_le_ions

/-- `r_i ≤ 1` for a physical plasma. -/
theorem ions_le_one : p.ionRatio ≤ 1 := h.composition.ions_le_one

/-- `f_fuel ≤ 1` for a physical plasma. -/
theorem fuel_le_one : p.fuelFraction ≤ 1 := h.composition.fuel_le_one

/-- A physical plasma with `f_fuel = 1` has `Z_eff = 1`. -/
theorem Zeff_eq_one_of_fuel_one (hf : p.fuelFraction = 1) : p.Zeff = 1 :=
  h.composition.Zeff_eq_one_of_fuel_one hf

end PhysicalPlasma

/-- A single-impurity plasma (charge `Z`, `1 ≤ Z_eff < Z`) with positive density and volume and
the consistent `f_fuel`, `r_i` is physical. -/
theorem physicalPlasma_of_impurity {p : DTPlasma} {Z : ℝ} (hn : 0 < p.n) (hV : 0 < p.V)
    (h1 : 1 ≤ p.Zeff) (hZ : p.Zeff < Z) (hf : p.fuelFraction = impurityFuelFraction p.Zeff Z)
    (hr : p.ionRatio = impurityIonRatio p.Zeff Z) : PhysicalPlasma p where
  n_pos := hn
  V_pos := hV
  fuel_pos := by
    have hZ1 : 0 < Z - 1 := by linarith
    have : (p.Zeff - 1) / (Z - 1) < 1 := (div_lt_one hZ1).mpr (by linarith)
    rw [hf, impurityFuelFraction]; linarith
  composition := quasineutralComposition_of_impurity (by linarith) h1 hf hr

namespace DTPlasma

/-- Thermal energy in J at temperature `T` keV: `W = (3/2)(n_e + n_ions) T V`. -/
@[expose] def thermalEnergy (p : DTPlasma) (T : ℝ) : ℝ :=
  3 / 2 * p.n * (1 + p.ionRatio) * (T * keV) * p.V

/-- Alpha heating power in W: `(E_α/4) (f_fuel n)² ⟨σv⟩(T) V`. -/
@[expose] def alphaPower (p : DTPlasma) (sv : ℝ → ℝ) (T : ℝ) : ℝ :=
  alphaEnergy / 4 * (p.fuelFraction * p.n) ^ 2 * sv T * p.V

/-- Total D-T fusion power in W: `(E_fus/4) (f_fuel n)² ⟨σv⟩(T) V`. -/
@[expose] def fusionPower (p : DTPlasma) (sv : ℝ → ℝ) (T : ℝ) : ℝ :=
  fusionEnergy / 4 * (p.fuelFraction * p.n) ^ 2 * sv T * p.V

/-- Bremsstrahlung power in W: `C_br n_e² Z_eff √T V`. -/
@[expose] def bremsPower (p : DTPlasma) (T : ℝ) : ℝ :=
  bremsCoeff * p.n ^ 2 * p.Zeff * Real.sqrt T * p.V

/-- Transport loss power in W: `W/τ_E`. -/
@[expose] def lossPower (p : DTPlasma) (τE T : ℝ) : ℝ := p.thermalEnergy T / τE

/-- Net heating power `P_α + P_aux − P_br − W/τ_E` in W. -/
@[expose] def netHeating (p : DTPlasma) (sv : ℝ → ℝ) (Paux τE T : ℝ) : ℝ :=
  p.alphaPower sv T + Paux - p.bremsPower T - p.lossPower τE T

end DTPlasma

/-- A supplied reactivity enclosure on a keV window: for `T ∈ [lo, hi]` keV,
`svLo ≤ ⟨σv⟩(T) ≤ svHi` in m³/s. -/
structure ReactivityWindow where
  /-- Lower end of the window, keV. -/
  lo : ℚ
  /-- Upper end of the window, keV. -/
  hi : ℚ
  /-- Lower reactivity bound, m³/s. -/
  svLo : ℚ
  /-- Upper reactivity bound, m³/s. -/
  svHi : ℚ

/-- A reactivity function satisfies the enclosure of a window. -/
@[expose] def ReactivityWindow.Holds (w : ReactivityWindow) (sv : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, (w.lo : ℝ) ≤ T → T ≤ w.hi → (w.svLo : ℝ) ≤ sv T ∧ sv T ≤ w.svHi

/-- Supplied Bosch–Hale D-T enclosures (Nucl. Fusion 32 (1992) 611). Windows
`[k, k+1]` keV for `k = 1, …, 59`, then `[60, 80]` and `[80, 100]`. On `[a, b] ⊆ [1, 60]`
the fit is increasing, so `svLo = ⌊0.99·BH(a)⌋₄` and `svHi = ⌈1.01·BH(b)⌉₄`
(four significant digits, rounded outward); on the last two windows min/max over
2001 samples were used with an extra 10⁻⁴ relative margin. Computed with 50-digit
Python `decimal` arithmetic; **supplied data, not proved in Lean**. -/
@[expose] def boschHaleWindows : List ReactivityWindow := [
  ⟨1, 2, 6.788e-27, 3.008e-25⟩,
  ⟨2, 3, 2.947e-25, 1.886e-24⟩,
  ⟨3, 4, 1.848e-24, 6.035e-24⟩,
  ⟨4, 5, 5.914e-24, 1.380e-23⟩,
  ⟨5, 6, 1.352e-23, 2.580e-23⟩,
  ⟨6, 7, 2.528e-23, 4.222e-23⟩,
  ⟨7, 8, 4.137e-23, 6.285e-23⟩,
  ⟨8, 9, 6.160e-23, 8.724e-23⟩,
  ⟨9, 10, 8.550e-23, 1.148e-22⟩,
  ⟨10, 11, 1.124e-22, 1.448e-22⟩,
  ⟨11, 12, 1.418e-22, 1.765e-22⟩,
  ⟨12, 13, 1.729e-22, 2.095e-22⟩,
  ⟨13, 14, 2.052e-22, 2.430e-22⟩,
  ⟨14, 15, 2.381e-22, 2.768e-22⟩,
  ⟨15, 16, 2.712e-22, 3.103e-22⟩,
  ⟨16, 17, 3.041e-22, 3.434e-22⟩,
  ⟨17, 18, 3.365e-22, 3.757e-22⟩,
  ⟨18, 19, 3.681e-22, 4.071e-22⟩,
  ⟨19, 20, 3.989e-22, 4.374e-22⟩,
  ⟨20, 21, 4.286e-22, 4.666e-22⟩,
  ⟨21, 22, 4.573e-22, 4.946e-22⟩,
  ⟨22, 23, 4.847e-22, 5.214e-22⟩,
  ⟨23, 24, 5.110e-22, 5.469e-22⟩,
  ⟨24, 25, 5.360e-22, 5.712e-22⟩,
  ⟨25, 26, 5.598e-22, 5.943e-22⟩,
  ⟨26, 27, 5.824e-22, 6.161e-22⟩,
  ⟨27, 28, 6.038e-22, 6.368e-22⟩,
  ⟨28, 29, 6.241e-22, 6.564e-22⟩,
  ⟨29, 30, 6.433e-22, 6.748e-22⟩,
  ⟨30, 31, 6.613e-22, 6.922e-22⟩,
  ⟨31, 32, 6.784e-22, 7.086e-22⟩,
  ⟨32, 33, 6.944e-22, 7.239e-22⟩,
  ⟨33, 34, 7.095e-22, 7.384e-22⟩,
  ⟨34, 35, 7.237e-22, 7.520e-22⟩,
  ⟨35, 36, 7.370e-22, 7.647e-22⟩,
  ⟨36, 37, 7.494e-22, 7.766e-22⟩,
  ⟨37, 38, 7.611e-22, 7.877e-22⟩,
  ⟨38, 39, 7.720e-22, 7.981e-22⟩,
  ⟨39, 40, 7.822e-22, 8.078e-22⟩,
  ⟨40, 41, 7.917e-22, 8.169e-22⟩,
  ⟨41, 42, 8.006e-22, 8.253e-22⟩,
  ⟨42, 43, 8.088e-22, 8.331e-22⟩,
  ⟨43, 44, 8.165e-22, 8.404e-22⟩,
  ⟨44, 45, 8.236e-22, 8.471e-22⟩,
  ⟨45, 46, 8.302e-22, 8.533e-22⟩,
  ⟨46, 47, 8.363e-22, 8.590e-22⟩,
  ⟨47, 48, 8.419e-22, 8.643e-22⟩,
  ⟨48, 49, 8.471e-22, 8.692e-22⟩,
  ⟨49, 50, 8.519e-22, 8.736e-22⟩,
  ⟨50, 51, 8.562e-22, 8.777e-22⟩,
  ⟨51, 52, 8.602e-22, 8.813e-22⟩,
  ⟨52, 53, 8.638e-22, 8.847e-22⟩,
  ⟨53, 54, 8.671e-22, 8.877e-22⟩,
  ⟨54, 55, 8.700e-22, 8.904e-22⟩,
  ⟨55, 56, 8.727e-22, 8.928e-22⟩,
  ⟨56, 57, 8.750e-22, 8.949e-22⟩,
  ⟨57, 58, 8.771e-22, 8.968e-22⟩,
  ⟨58, 59, 8.789e-22, 8.984e-22⟩,
  ⟨59, 60, 8.805e-22, 8.997e-22⟩,
  ⟨60, 80, 8.749e-22, 9.037e-22⟩,
  ⟨80, 100, 8.363e-22, 8.927e-22⟩
]

/-- Supplied empirical facts about the D-T thermal reactivity `sv` (m³/s, `T` in keV),
from the Bosch–Hale fit (Nucl. Fusion 32 (1992) 611): nonnegativity, continuity for
`T > 0`, monotonicity on `[1, 60]` keV (the fit peaks near 66.6 keV) and the rational
enclosures `boschHaleWindows`. **Supplied data, not proved.** -/
class BoschHaleDT (sv : ℝ → ℝ) : Prop where
  nonneg : ∀ T : ℝ, 0 ≤ T → 0 ≤ sv T
  continuousOn : ContinuousOn sv (Set.Ioi 0)
  monotoneOn : MonotoneOn sv (Set.Icc 1 60)
  windows : ∀ w ∈ boschHaleWindows, w.Holds sv

/-- Supplied 0-D energy balance law for a trajectory `T(t)` (keV) with auxiliary power
`Paux(t)` (W) and confinement time `τE(t)` (s), for `t ≥ 0`:
`dW/dt = P_α + P_aux − P_br − W/τ_E` (derivative within `[0, ∞)`, one-sided at
`t = 0`). `τE` may depend on time (hence, implicitly, on
the state), which allows supplied confinement-degradation hypotheses downstream. -/
class PowerBalance (p : DTPlasma) (sv Paux τE T : ℝ → ℝ) : Prop where
  tauE_pos : ∀ t : ℝ, 0 ≤ t → 0 < τE t
  balance : ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s => p.thermalEnergy (T s))
      (p.netHeating sv (Paux t) (τE t) (T t)) (Set.Ici 0) t

end PlasmaLean.Fusion
