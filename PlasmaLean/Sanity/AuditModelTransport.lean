/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.FluxGeometry
public import PlasmaLean.Theory.Transport.BoschHaleFine
public import PlasmaLean.Theory.Transport.ConfinementScaling

/-!
# Strict model audit: `FluxGeometry.Laws`, `BoschHaleFine`, `ConfinementLaw`

Added by the first strict audit of the model layer outside `Kernel/` (finding H-1 of
`notes/audit/2026-10-30-repository-audit.md`; record in `notes/audit/2026-10-30-model-audit.md`,
commit `cda8bd0`).

**Flux geometry** (`Transport.FluxGeometry.Laws`)
* regression (finding MA-L8): the laws admit the degenerate geometry `g = ⟨|∇ψ|²⟩ ≡ 0` (no
  radial transport at all, `zeroGeom_laws`) and a geometry with `g < 0` (`negGeom_laws`,
  `negGeom_g_neg`); `g ≥ 0` is a separate hypothesis of `coeffs_transportLaws`;
* counterexample: a geometry violating the Gauss identity (`noGauss_not_laws`);
* independent characterization: the Gauss identity and `g(0) = 0` give `g ≥ 0` on `[0, 1]`
  whenever `⟨Δψ⟩ ≥ 0` (`g_nonneg_of_h_nonneg`).

**Bosch–Hale fine windows** (`Transport.BoschHaleFine`)
* the 100 windows tile `[5, 30]` keV without gaps, each enclosure is ordered and the enclosures
  increase from window to window, as the supplied monotonicity requires (`fine_chain_check`,
  `fine_span_check`);
* counterexample: the zero reactivity is not `BoschHaleFine` (`zero_not_boschHaleFine`).
  (The window values were also recomputed independently from the Bosch–Hale formula, outside
  Lean; see the audit note.)

**Confinement scaling** (`Fusion.ConfinementLaw.tau`)
* regression (finding MA-L9): at zero heating power Lean's `0 ^ (−α) = 0` gives `τ_E = 0`
  (`tau_zero_power`), which with `W/τ_E = W/0 = 0` would mean *no* losses; this is why
  `SteadyScaling` carries the field `P_pos`;
* units: `τ_E` with `P` in watts equals the fit with `P` in megawatts (`tau_megawatt`).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.AuditModel
open Set PlasmaLean.Transport PlasmaLean.Fusion

/-! ### Flux geometry -/

/-- Degenerate geometry: `V' = 1`, `g = ⟨|∇ψ|²⟩ ≡ 0`, `h = ⟨Δψ⟩ ≡ 0`. -/
@[expose] def zeroGeom : FluxGeometry :=
  ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- Regression (MA-L8): the degenerate geometry `g ≡ 0` satisfies the laws; the resulting
diffusion coefficient `D = χ g` vanishes identically. -/
theorem zeroGeom_laws : zeroGeom.Laws where
  Vp_pos _ _ := one_pos
  Vp_deriv _ _ := hasDerivWithinAt_const _ _ _
  g_deriv _ _ := hasDerivWithinAt_const _ _ _
  g_zero := rfl
  gauss _ _ := by simp [zeroGeom]

/-- A geometry with negative `⟨|∇ψ|²⟩ = −s` (impossible for an average of squares). -/
@[expose] def negGeom : FluxGeometry :=
  ⟨fun _ => 1, fun _ => 0, fun s => -s, fun _ => -1, fun _ => -1⟩

/-- Regression (MA-L8): `negGeom` satisfies the laws. -/
theorem negGeom_laws : negGeom.Laws where
  Vp_pos _ _ := one_pos
  Vp_deriv _ _ := hasDerivWithinAt_const _ _ _
  g_deriv s _ := (hasDerivAt_neg s).hasDerivWithinAt
  g_zero := by simp [negGeom]
  gauss _ _ := by simp [negGeom]

/-- `negGeom` has `⟨|∇ψ|²⟩ < 0` on `(0, 1]`. -/
theorem negGeom_g_neg {s : ℝ} (hs : 0 < s) : negGeom.g s < 0 := by
  simp only [negGeom]; linarith

/-- A geometry violating the Gauss identity: `g = s` with `V' = 1` but `h = 0`. -/
@[expose] def noGauss : FluxGeometry :=
  ⟨fun _ => 1, fun _ => 0, fun s => s, fun _ => 1, fun _ => 0⟩

/-- Counterexample: `noGauss` does not satisfy the laws, so the Gauss identity has content. -/
theorem noGauss_not_laws : ¬ noGauss.Laws := by
  intro h
  have := h.gauss 0 ⟨le_rfl, zero_le_one⟩
  simp [noGauss] at this

/-- **Sign of `g` from the Gauss identity**: if `⟨Δψ⟩ ≥ 0` on `[0, 1]`, then
`⟨|∇ψ|²⟩ ≥ 0` on `[0, 1]` (`(V' g)' = V' h ≥ 0` and `V' g = 0` on the axis). -/
theorem g_nonneg_of_h_nonneg (G : FluxGeometry) [hG : G.Laws]
    (hh : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ G.h s) : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ G.g s := by
  have hF : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ G.Vp s * G.g s := by
    refine nonneg_of_deriv_nonneg_Icc (F' := fun s => G.Vp s * G.h s)
      (fun s hs => ?_) (by simp [hG.g_zero]) (fun s hs => ?_)
    · have := (hG.Vp_deriv s hs).mul (hG.g_deriv s hs)
      rw [← hG.gauss s hs]
      exact this
    · have hs' := Ioo_subset_Icc_self hs
      exact mul_nonneg (hG.Vp_pos s hs').le (hh s hs')
  intro s hs
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hF s hs) (hG.Vp_pos s hs)

/-! ### Bosch–Hale fine windows -/

/-- Chain check of a window list: each enclosure is ordered, consecutive windows are contiguous
(`hi = lo` of the next) and both enclosure ends are nondecreasing. -/
@[expose] def fineChain : List ReactivityWindow → Bool
  | [] => true
  | [w] => decide (w.svLo ≤ w.svHi)
  | w :: w' :: ws => decide (w.svLo ≤ w.svHi) && decide (w.hi = w'.lo) &&
      decide (w.svLo ≤ w'.svLo) && decide (w.svHi ≤ w'.svHi) && fineChain (w' :: ws)

/-- The fine Bosch–Hale windows form a gap-free chain with increasing enclosures (consistent
with the supplied monotonicity of the reactivity on `[1, 60]` keV). -/
theorem fine_chain_check : fineChain boschHaleFineWindows = true := by
  bool_cert

/-- The fine windows start at `5` keV and end at `30` keV. -/
theorem fine_span_check :
    (decide (boschHaleFineWindows.head?.map (·.lo) = some 5) &&
      decide (boschHaleFineWindows.getLast?.map (·.hi) = some 30)) = true := by
  bool_cert

/-- Counterexample: the zero reactivity violates the fine data (already the first window at
`T = 5` keV), so `BoschHaleFine` has content. -/
theorem zero_not_boschHaleFine : ¬ BoschHaleFine (fun _ => 0) := by
  intro h
  have hw := h.fine ⟨20 / 4, 21 / 4, 1.352e-23, 1.639e-23⟩ (by simp [boschHaleFineWindows])
  have := (hw 5 (by norm_num) (by norm_num)).1
  norm_num at this

/-! ### Confinement scaling -/

/-- Regression (MA-L9): at zero heating power the scaling law returns `τ_E = 0` (Lean's
`0 ^ (−α) = 0` for `α ≠ 0`), the opposite of the physical limit `τ_E → ∞`. `SteadyScaling`
therefore requires `P_α + P_aux > 0` (`SteadyScaling.P_pos`). -/
theorem tau_zero_power (L : ConfinementLaw) (hα : L.α ≠ 0) (H : ℝ) : L.tau H 0 = 0 := by
  simp [ConfinementLaw.tau, Real.zero_rpow (neg_ne_zero.2 hα)]

/-- Units: with `P = 10⁶ P_MW` watts the law is the published fit `H C P_MW^(−α)`. -/
theorem tau_megawatt (L : ConfinementLaw) (H Pmw : ℝ) :
    L.tau H (1e6 * Pmw) = H * L.C * Pmw ^ (-L.α) := by
  unfold ConfinementLaw.tau
  rw [mul_div_cancel_left₀ Pmw (by norm_num : (1e6 : ℝ) ≠ 0)]

end PlasmaLean.Sanity.AuditModel
