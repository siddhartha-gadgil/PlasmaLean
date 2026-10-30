/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Engineering.SlabHeat

/-!
# Strict-audit checks for `Kernel/ThermalSlab` (audit of 30 October 2026)

Added by the first strict kernel audit (`notes/audit/2026-10-30-kernel-audit.md`, commit
`cda8bd0`). `Theory/Engineering/SlabHeat` already gives the concrete instance
(`slab_solution`), uniqueness (`slab_unique`) and the zero-load profile (`slab_zero_load`);
there was no sanity module for `SteadySlab`. This module adds:

* degenerate case: with no loads the slab sits at the coolant temperature
  (`steadySlab_unloaded`);
* counterexample: an isothermal profile cannot carry a nonzero surface load
  (`steadySlab_rejects_isothermal`);
* conservation (global energy balance): the heat leaving the cooled face equals the surface
  load plus the volumetric heating, `hc (T(0) − Tc) = q + Q h` (`steadySlab_energy_balance`);
* sign check: nonnegative loads keep the cooled face at or above the coolant temperature
  (`steadySlab_cold_face_ge`);
* parameter endpoint (regression for finding T-1): the zero-thickness slab `h = 0` is admitted
  and reduces to the convective boundary relation `hc (T(0) − Tc) = q`
  (`steadySlab_zero_thickness`, `steadySlab_zero_thickness_exists`).
-/

public section

noncomputable section

namespace PlasmaLean.Sanity.Audit
open PlasmaLean.Engineering

/-- **Degenerate case.** With no surface load and no volumetric heating, the constant
coolant-temperature profile satisfies the slab laws. -/
theorem steadySlab_unloaded (Tc h k hc : ℝ) (hh : 0 ≤ h) (hk : 0 < k) (hhc : 0 < hc) :
    SteadySlab (fun _ => Tc) (fun _ => 0) Tc 0 0 h k hc :=
  ⟨hh, hk, hhc, fun x _ => hasDerivAt_const x Tc, fun x _ => by simpa using hasDerivAt_const x 0,
    by simp, by simp⟩

/-- **Counterexample.** An isothermal profile (zero gradient) cannot carry a nonzero surface
load: the hot-face flux law fails. -/
theorem steadySlab_rejects_isothermal (Tc q : ℝ) (hq : q ≠ 0) :
    ¬ SteadySlab (fun _ => Tc) (fun _ => 0) Tc q 0 1 1 1 := by
  intro h
  exact hq (by simpa using h.hot_flux.symm)

/-- **Conservation (global energy balance).** Every solution of the slab laws removes at the
cooled face exactly the surface load plus the volumetric heat: `hc (T(0) − Tc) = q + Q h`. -/
theorem steadySlab_energy_balance {T dT : ℝ → ℝ} {Tc q Q h k hc : ℝ}
    [laws : SteadySlab T dT Tc q Q h k hc] : hc * (T 0 - Tc) = q + Q * h := by
  have hhc := laws.cooling_pos
  rw [slab_unique T dT Tc q Q h k hc 0 ⟨le_rfl, laws.thickness_nonneg⟩]
  unfold slabTemperature
  field_simp
  ring

/-- **Sign check.** Nonnegative surface and volumetric loads keep the cooled face at or above
the coolant temperature. -/
theorem steadySlab_cold_face_ge {T dT : ℝ → ℝ} {Tc q Q h k hc : ℝ}
    [laws : SteadySlab T dT Tc q Q h k hc] (hq : 0 ≤ q) (hQ : 0 ≤ Q) : Tc ≤ T 0 := by
  have hhc := laws.cooling_pos
  have hb := steadySlab_energy_balance (laws := laws)
  have hh := laws.thickness_nonneg
  have h1 : 0 ≤ hc * (T 0 - Tc) := by rw [hb]; nlinarith [mul_nonneg hQ hh]
  have h2 : 0 ≤ T 0 - Tc := nonneg_of_mul_nonneg_right (by linarith) hhc
  linarith

/-- **Regression (finding T-1, parameter endpoint).** A zero-thickness slab is admitted by the
laws; they then reduce to the convective boundary relation `hc (T(0) − Tc) = q`. -/
theorem steadySlab_zero_thickness {T dT : ℝ → ℝ} {Tc q Q k hc : ℝ}
    [laws : SteadySlab T dT Tc q Q 0 k hc] : hc * (T 0 - Tc) = q := by
  simpa using steadySlab_energy_balance (laws := laws)

/-- The zero-thickness case is inhabited: `slab_solution` with `h = 0`. -/
theorem steadySlab_zero_thickness_exists (Tc q Q k hc : ℝ) (hk : 0 < k) (hhc : 0 < hc) :
    ∃ T dT : ℝ → ℝ, SteadySlab T dT Tc q Q 0 k hc :=
  ⟨_, _, slab_solution Tc q Q 0 k hc le_rfl hk hhc⟩

end PlasmaLean.Sanity.Audit
