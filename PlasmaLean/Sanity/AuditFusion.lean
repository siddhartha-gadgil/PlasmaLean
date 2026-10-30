/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.Fusion
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Strict-audit checks for `Kernel/Fusion` (audit of 30 October 2026)

Added by the first strict kernel audit (`notes/audit/2026-10-30-kernel-audit.md`, commit
`cda8bd0`). `Sanity/Fusion`, `Sanity/BoschHaleInstance` and `Sanity/BoschHaleFineInstance`
already give the degenerate case (zero density), concrete instances (`bhSv_boschHaleDT`,
`carbon_fixture`, `steady_state_iff`) and counterexamples for `BoschHaleDT`. This module adds:

* unit and constant checks: `keV` is `10³ e`, the neutron carries `14.089 MeV`
  (`keV_eq`, `neutron_energy`), and `C_br` agrees with the NRL Formulary value converted to SI
  and keV to within 1 % (`bremsCoeff_matches_NRL`);
* table coverage: the 61 supplied windows are contiguous from 1 keV to 100 keV
  (`boschHaleWindows_contiguous`), hence every temperature in `[1, 100]` keV lies in a window
  (`boschHaleWindows_cover`), and a `BoschHaleDT` reactivity is positive there
  (`BoschHaleDT.pos_of_mem`);
* counterexamples: zero density is not a physical plasma (`not_physical_zero_density`); a zero
  confinement time is rejected by `PowerBalance` (`powerBalance_rejects_zero_tau`);
* contradictory fields (regression for finding F-1, fixed by the quasineutral composition law
  `QuasineutralComposition`): `f_fuel = 1` with `Z_eff = 2` is **not** physical
  (`inconsistentPlasma_not_physical`), since quasineutrality forces `Z_eff = 1` when all
  electrons come from fuel (`fuel_one_forces_Zeff_one`); the sanity triad for the new law is a
  pure plasma (`purePlasma_physical`, degenerate), a carbon plus helium mixture
  (`carbonHeliumPlasma_physical`, instance), the counterexamples `inconsistentPlasma_not_physical`
  and `ionRatio_gt_one_not_physical`, and the risk-specific check that the carbon values
  `f_fuel = 0.86`, `r_i = 53/60` force `Z_eff ≥ 1.7` for **every** admissible mixture
  (`carbon_values_Zeff_ge`), so the M1/M2/Stellaris value `Z_eff = 1.7` is the least radiating
  composition consistent with them;
* zero-parameter witness (regression for finding F-2): with zero density and no auxiliary
  power, every temperature trajectory satisfies `PowerBalance` (`powerBalance_zero_density`);
* totalized operations (regression for finding F-3): `W/τ_E` with `τ_E = 0` is `0`, i.e.
  perfect confinement (`lossPower_zero_tau`, `netHeating_zero_tau`); `√T = 0` for `T ≤ 0`
  (`bremsPower_of_nonpos`); `impurityFuelFraction Z_eff 1 = 1` for every `Z_eff`
  (`impurityFuelFraction_Z_one`).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.Audit
open PlasmaLean.Fusion DTPlasma

/-! ### Units and constants -/

/-- `keV` is `10³` times the exact elementary charge `1.602176634e-19 C`. -/
theorem keV_eq : keV = 1000 * 1.602176634e-19 := by norm_num [keV]

/-- The neutron energy `E_fus − E_α` is `14.089 MeV`. -/
theorem neutron_energy : fusionEnergy - alphaEnergy = 14089 * keV := by
  unfold fusionEnergy alphaEnergy; ring

/-- **Dimensional cross-check.** The NRL Formulary coefficient
`1.69e-32 W cm⁻³` (densities in cm⁻³, `T` in eV), converted to `W m³ keV^(-1/2)`, is
`1.69e-32 · 10⁻¹² · 10⁶ · √1000 = 1.69e-38 √1000`; it agrees with `C_br = 5.35e-37` to
within 1 %. -/
theorem bremsCoeff_matches_NRL : |1.69e-38 * Real.sqrt 1000 - bremsCoeff| ≤ bremsCoeff / 100 := by
  have h1 : (31.62 : ℝ) < Real.sqrt 1000 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : Real.sqrt 1000 < 31.63 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [abs_le]
  unfold bremsCoeff
  constructor <;> nlinarith

/-! ### Coverage of the supplied table -/

/-- Consecutive windows share their endpoints. -/
@[expose] def Contiguous : List ReactivityWindow → Prop
  | a :: b :: rest => a.hi = b.lo ∧ Contiguous (b :: rest)
  | _ => True

/-- The supplied Bosch–Hale windows are contiguous. -/
theorem boschHaleWindows_contiguous : Contiguous boschHaleWindows := by
  norm_num [Contiguous, boschHaleWindows]

/-- A contiguous list of windows starting with `w` covers `[w.lo, last.hi]`. -/
theorem Contiguous.cover : ∀ (w : ReactivityWindow) (l : List ReactivityWindow),
    Contiguous (w :: l) → ∀ T : ℝ, (w.lo : ℝ) ≤ T → T ≤ ((w :: l).getLast (by simp)).hi →
      ∃ v ∈ w :: l, (v.lo : ℝ) ≤ T ∧ T ≤ v.hi
  | w, [], _, T, h1, h2 => ⟨w, by simp, h1, by simpa using h2⟩
  | w, x :: xs, hc, T, h1, h2 => by
    obtain ⟨hwx, hc'⟩ := hc
    by_cases hT : T ≤ (w.hi : ℝ)
    · exact ⟨w, by simp, h1, hT⟩
    · have hx : (x.lo : ℝ) ≤ T := by rw [← hwx]; exact (not_le.mp hT).le
      rw [List.getLast_cons_cons] at h2
      obtain ⟨v, hv, hv'⟩ := Contiguous.cover x xs hc' T hx h2
      exact ⟨v, List.mem_cons_of_mem _ hv, hv'⟩

/-- The first supplied window starts at `1` keV. -/
theorem boschHaleWindows_head_lo (h : boschHaleWindows ≠ []) : (boschHaleWindows.head h).lo = 1 :=
  rfl

/-- The last supplied window ends at `100` keV. -/
theorem boschHaleWindows_getLast_hi (h : boschHaleWindows ≠ []) :
    (boschHaleWindows.getLast h).hi = 100 :=
  rfl

/-- **Coverage.** Every temperature in `[1, 100]` keV lies in one of the supplied windows. -/
theorem boschHaleWindows_cover (T : ℝ) (h1 : 1 ≤ T) (h2 : T ≤ 100) :
    ∃ w ∈ boschHaleWindows, (w.lo : ℝ) ≤ T ∧ T ≤ w.hi := by
  have hne : boschHaleWindows ≠ [] := by simp [boschHaleWindows]
  have hlo := boschHaleWindows_head_lo hne
  have hhi := boschHaleWindows_getLast_hi hne
  have hc := boschHaleWindows_contiguous
  revert hne hlo hhi hc
  generalize boschHaleWindows = l
  intro hne hlo hhi hc
  obtain ⟨w, l', rfl⟩ := List.exists_cons_of_ne_nil hne
  refine Contiguous.cover w l' hc T ?_ ?_
  · simp only [List.head_cons] at hlo
    rw [hlo]; exact_mod_cast h1
  · rw [hhi]; exact_mod_cast h2

/-- Every supplied window has a positive lower reactivity bound. -/
theorem boschHaleWindows_svLo_pos : ∀ w ∈ boschHaleWindows, 0 < w.svLo := by
  simp only [boschHaleWindows, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

/-- **Positivity on the table range.** A `BoschHaleDT` reactivity is positive on
`[1, 100]` keV. -/
theorem BoschHaleDT.pos_of_mem (sv : ℝ → ℝ) [h : BoschHaleDT sv] {T : ℝ} (h1 : 1 ≤ T)
    (h2 : T ≤ 100) : 0 < sv T := by
  obtain ⟨w, hw, hlo, hhi⟩ := boschHaleWindows_cover T h1 h2
  have := (h.windows w hw T hlo hhi).1
  have hpos : (0 : ℝ) < w.svLo := by exact_mod_cast boschHaleWindows_svLo_pos w hw
  linarith

/-! ### Counterexamples -/

/-- **Counterexample.** A plasma with zero density is not physical. -/
theorem not_physical_zero_density (p : DTPlasma) (h : p.n = 0) : ¬ PhysicalPlasma p :=
  fun hp => (lt_irrefl (0 : ℝ)) (h ▸ hp.n_pos)

/-- **Counterexample.** A zero confinement time is rejected by the power balance law. -/
theorem powerBalance_rejects_zero_tau (p : DTPlasma) (sv : ℝ → ℝ) (P T₀ : ℝ) :
    ¬ PowerBalance p sv (fun _ => P) (fun _ => 0) (fun _ => T₀) := fun h =>
  lt_irrefl (0 : ℝ) (h.tauE_pos 0 le_rfl)

/-! ### Regression: contradictory composition fields -/

/-- A plasma with fuel fraction `1` and ion ratio `1` but `Z_eff = 2`. -/
@[expose] def inconsistentPlasma : DTPlasma := ⟨1e20, 1, 2, 1, 1⟩

/-- **Regression (finding F-1), now a counterexample.** With the quasineutral composition
law, `f_fuel = r_i = 1` with `Z_eff = 2` is not physical: `f_fuel = 1` forces `Z_eff = 1`. -/
theorem inconsistentPlasma_not_physical : ¬ PhysicalPlasma inconsistentPlasma := fun h => by
  have := h.composition.Zeff_eq_one_of_fuel_one (by norm_num [inconsistentPlasma])
  norm_num [inconsistentPlasma] at this

/-- **Degenerate case.** A pure D-T plasma (`Z_eff = f_fuel = r_i = 1`, no impurity species)
is physical. -/
theorem purePlasma_physical : PhysicalPlasma ⟨1e20, 1, 1, 1, 1⟩ where
  n_pos := by norm_num
  V_pos := by norm_num
  fuel_pos := by norm_num
  composition := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
    by simp, by simp, by simp⟩

/-- Carbon (`Z = 6`, `c = 1/50`) and helium (`Z = 2`, `c = 1/20`) impurities per electron:
`f_fuel = 1 − 6/50 − 2/20 = 39/50`, `Z_eff = 39/50 + 36/50 + 4/20 = 17/10`,
`r_i = 39/50 + 1/50 + 1/20 = 17/20`. -/
@[expose] def carbonHeliumPlasma : DTPlasma := ⟨1e20, 1, 17 / 10, 39 / 50, 17 / 20⟩

/-- **Concrete instance (two species).** The carbon plus helium mixture is physical. -/
theorem carbonHeliumPlasma_physical : PhysicalPlasma carbonHeliumPlasma where
  n_pos := by norm_num [carbonHeliumPlasma]
  V_pos := by norm_num [carbonHeliumPlasma]
  fuel_pos := by norm_num [carbonHeliumPlasma]
  composition := ⟨2, ![6, 2], ![1 / 50, 1 / 20],
    fun i => by fin_cases i <;> norm_num, fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two, carbonHeliumPlasma]; norm_num,
    by simp [Fin.sum_univ_two, carbonHeliumPlasma]; norm_num,
    by simp [Fin.sum_univ_two, carbonHeliumPlasma]; norm_num⟩

/-- **Counterexample.** An ion ratio above `1` (more ions than electrons) is not physical. -/
theorem ionRatio_gt_one_not_physical (p : DTPlasma) (h : 1 < p.ionRatio) :
    ¬ PhysicalPlasma p := fun hp => absurd hp.composition.ions_le_one (not_le.2 h)

/-- **Risk-specific check (composition).** For any quasineutral composition and any real `a`,
`Z_eff ≥ f_fuel + 2a(1 − f_fuel) − a²(r_i − f_fuel)` (from `Σ (Z_i − a)² c_i ≥ 0`). -/
theorem Zeff_ge_of_composition {p : DTPlasma} (h : QuasineutralComposition p) (a : ℝ) :
    p.fuelFraction + 2 * a * (1 - p.fuelFraction) - a ^ 2 * (p.ionRatio - p.fuelFraction) ≤
      p.Zeff := by
  obtain ⟨k, Z, c, -, hc, hq, hz, hr⟩ := h
  have hsq : 0 ≤ ∑ i, (Z i - a) ^ 2 * c i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hc i)
  have hexp : ∑ i, (Z i - a) ^ 2 * c i =
      ∑ i, Z i ^ 2 * c i - 2 * a * ∑ i, Z i * c i + a ^ 2 * ∑ i, c i := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : ∑ i, Z i * c i = 1 - p.fuelFraction := by linarith
  have h2 : ∑ i, c i = p.ionRatio - p.fuelFraction := by linarith
  rw [hexp, h1, h2] at hsq
  linarith

/-- **Risk-specific check (the design values).** Every physical plasma with the carbon values
`f_fuel = 0.86`, `r_i = 53/60` used by `m1Plasma`, `m2Plasma` and `stellarisPlasma` has
`Z_eff ≥ 1.7`; so `Z_eff = 1.7` (pure carbon) is the least radiating consistent choice and the
bremsstrahlung in those designs is not underestimated. -/
theorem carbon_values_Zeff_ge (p : DTPlasma) [h : PhysicalPlasma p] (hf : p.fuelFraction = 0.86)
    (hr : p.ionRatio = 53 / 60) : 1.7 ≤ p.Zeff := by
  have := Zeff_ge_of_composition h.composition 6
  rw [hf, hr] at this
  linarith

/-- **Quasineutrality forbids it.** If every electron comes from fuel (`n_fuel = n_e`), then
for an impurity of charge `Z ≠ 0` quasineutrality `n_e = n_fuel + Z n_imp` and the definition
`Z_eff n_e = n_fuel + Z² n_imp` force `Z_eff = 1`. -/
theorem fuel_one_forces_Zeff_one {ne ni Z Zeff : ℝ} (hne : ne ≠ 0) (hZ : Z ≠ 0)
    (hq : ne = ne + Z * ni) (hz : Zeff * ne = ne + Z ^ 2 * ni) : Zeff = 1 := by
  have hni : ni = 0 := by
    have : Z * ni = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hZ
    · exact h
  rw [hni, mul_zero, add_zero] at hz
  exact mul_right_cancel₀ hne (by rw [hz, one_mul])

/-- With `Z_eff = 2` and a carbon impurity, the consistent fuel fraction is `4/5`, not `1`. -/
theorem carbon_fuel_fraction_two : impurityFuelFraction 2 6 = 4 / 5 := by
  norm_num [impurityFuelFraction]

/-! ### Regression: zero-parameter witness -/

/-- **Regression (finding F-2).** With zero density and no auxiliary power, every temperature
trajectory satisfies the power balance (for any positive confinement time): `PowerBalance`
has content only together with `PhysicalPlasma`. -/
theorem powerBalance_zero_density (p : DTPlasma) (hn : p.n = 0) (sv τE T : ℝ → ℝ)
    (hτ : ∀ t, 0 ≤ t → 0 < τE t) : PowerBalance p sv (fun _ => 0) τE T := by
  refine ⟨hτ, fun t _ => ?_⟩
  have hW : (fun s => p.thermalEnergy (T s)) = fun _ => 0 :=
    funext fun s => Fusion.thermalEnergy_zero_density p hn (T s)
  rw [hW, Fusion.netHeating_zero_density p hn]
  exact hasDerivWithinAt_const _ _ _

/-- The zero-density witness applies to an arbitrary, e.g. linearly rising, temperature. -/
theorem powerBalance_zero_density_rising :
    PowerBalance ⟨0, 1, 1, 1, 1⟩ (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun t => t) :=
  powerBalance_zero_density _ rfl _ _ _ (fun _ _ => one_pos)

/-! ### Regression: totalized operations -/

/-- **Regression (finding F-3).** With `τ_E = 0` the transport loss is `0` (`x / 0 = 0`), i.e.
perfect confinement rather than infinite loss. -/
theorem lossPower_zero_tau (p : DTPlasma) (T : ℝ) : p.lossPower 0 T = 0 := by
  simp [lossPower]

/-- With `τ_E = 0` the net heating has no transport loss term. -/
theorem netHeating_zero_tau (p : DTPlasma) (sv : ℝ → ℝ) (P T : ℝ) :
    p.netHeating sv P 0 T = p.alphaPower sv T + P - p.bremsPower T := by
  simp [netHeating, lossPower]

/-- For a nonpositive temperature the bremsstrahlung power is `0` (`√T = 0`). -/
theorem bremsPower_of_nonpos (p : DTPlasma) {T : ℝ} (hT : T ≤ 0) : p.bremsPower T = 0 := by
  simp [bremsPower, Real.sqrt_eq_zero_of_nonpos hT]

/-- With impurity charge `Z = 1` the single-impurity fuel fraction is `1` for every `Z_eff`
(division by zero); the formula is meaningful only for `Z > 1`. -/
theorem impurityFuelFraction_Z_one (Zeff : ℝ) : impurityFuelFraction Zeff 1 = 1 := by
  simp [impurityFuelFraction]

end PlasmaLean.Sanity.Audit
