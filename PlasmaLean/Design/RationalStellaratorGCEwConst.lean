/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCEwAdm
public import PlasmaLean.Design.RationalStellaratorGCEwMaj

/-!
# The KAM constants over the energy window

The numerical conditions of the KAM theorem (`Design/KamFlowIterationS`, `GlobalH`, `KamH`) for the
constants `cE` of the energy window `|ρ − 1/256| ≤ 2⁻³²`, `λ ∈ [0, 1/16]`: `c_K ≤ 6400`,
`c_L ≤ 21900`, the smallness `32 κ e₀/δ₀⁴ ≈ 0.26 ≤ 1` with `e₀ = 7 × 10⁻²¹`, the displacement
budgets below `μ = 10⁻¹¹`, and the global conditions uniform over the window (`ew_global`: the
Taylor constant of `Design/RationalStellaratorGCEwMaj`, node validity of the pitch-angle family).

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `cE_cK`: the step constant stays below its budget `6400`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 Complex

/-- Unfolding set for the step constants of `cE`. -/
macro "cE_norm" : tactic =>
  `(tactic| (simp only [SC.cK, SC.k1, SC.k2, SC.kc, SC.k20, SC.g, SC.kη1, SC.kη2, SC.kh, SC.kE,
    SC.tTot, SC.τ', SC.kTc, SC.eM, SC.mA, SC.mV, SC.cL, SC.kA, SC.XRb, SC.XZb, SC.kRem, SC.kS,
    SC.kap, cE, e0E, δ0G, KamTorusA.rA, auM, azM, aRtM, aztM, aLRM, aLzM, acG, μM, sDM, sRM, sWM,
    tTE, τE, max_def]; norm_num))

/-- `τ' > 0`. -/
theorem cE_τ' : 0 < cE.τ' := by cE_norm

/-- **Sanity**: `c_K ≤ 6400`. -/
theorem cE_cK : cE.cK ≤ 6400 := by cE_norm

/-- `c_L ≤ 21900`. -/
theorem cE_cL : cE.cL ≤ 21900 := by cE_norm

/-- `c_K ≥ 0`. -/
theorem cE_cK_nonneg : 0 ≤ cE.cK := by cE_norm

/-- `c_L ≥ 0`. -/
theorem cE_cL_nonneg : 0 ≤ cE.cL := by cE_norm

/-- **The smallness condition** `32 κ e₀/δ₀⁴ ≤ 1` (actual value `≈ 0.26`). -/
theorem cE_small : 32 * cE.kap * e0E / cE.δ0 ^ 4 ≤ 1 := by cE_norm

/-- `κ > 0`. -/
theorem cE_kap_pos : 0 < cE.kap := by cE_norm

/-- Displacement budget (torus). -/
theorem cE_μK : 2 * cE.cK * e0E / cE.δ0 ^ 2 ≤ μM := by cE_norm

/-- Displacement budget (`θ`-derivatives). -/
theorem cE_μt : 2 * (cE.cK / cE.E1) * e0E / cE.δ0 ^ 3 ≤ μM := by cE_norm

/-- Displacement budget (transport). -/
theorem cE_μL : 2 * cE.cL * e0E / cE.δ0 ^ 2 ≤ μM := by cE_norm

/-- The perturbation profile is the rational profile `mvQE`. -/
theorem cE_mvec : cE.mvec = fun i => (RationalStellaratorGCMu.mvQE i : ℝ) := by
  funext i; fin_cases i <;> simp [SC.mvec, cE, RationalStellaratorGCMu.mvQE]

/-- The Taylor segment bounds lie below the validity bounds `aTQ`. -/
theorem cE_avecT : (∀ i, 0 ≤ (cE.avec + cE.Tq • cE.mvec) i) ∧
    ∀ i, (cE.avec + cE.Tq • cE.mvec) i ≤ (RationalStellaratorGCMu.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, SC.mvec, SC.Tq, cE, RationalStellaratorGCMu.aTQ, auM, azM, aLRM, aLzM,
      acG, μM, e0E, δ0G, KamTorusA.rA] <;> norm_num

/-- The limit segment bounds lie below the validity bounds `aTQ`. -/
theorem cE_avecμ : (∀ i, 0 ≤ (cE.avec + (2 * μM) • mOne) i) ∧
    ∀ i, (cE.avec + (2 * μM) • mOne) i ≤ (RationalStellaratorGCMu.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, mOne, cE, RationalStellaratorGCMu.aTQ, auM, azM, aLRM, aLzM, acG, μM] <;>
    norm_num

/-- Validity at bounds below `aTQ`, for every gyro-length. -/
theorem ew_valid {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i)
    (haa : ∀ i, a i ≤ RationalStellaratorGCMu.aTQ i) (ρ : ℝ) {lm : ℝ}
    (hlm : |lm| ≤ RationalStellaratorGCMu.lam1) :
    (gcFlowMu ρ lm).Valid6 a ∧ PolyExprS.Valid a (gcFlowMu ρ lm).resRp ∧
      PolyExprS.Valid a (gcFlowMu ρ lm).resZp := by
  obtain ⟨hE, hE4, hN⟩ := RationalStellaratorGCMu.mu_node_bounds ha haa hlm
  exact gcFlowMu_valid ρ lm a hE hE4 hN

/-- **The global conditions over the energy window** (`|ρ| ≤ 1/256 + 2⁻³²`, `|λ| ≤ 1/16`). -/
theorem ew_global {ρ lm : ℝ} (hρ : |ρ| ≤ ((RationalStellaratorGCMu.rhoMaxQ : ℚ) : ℝ))
    (hlm : |lm| ≤ RationalStellaratorGCMu.lam1) :
    (gcFlowMu ρ lm).GlobalH cE KamTorusA.iota where
  dio := iota_dio
  γ_pos := by norm_num [cE]
  hτ' := cE_τ'
  hC2R := by
    have h := (RationalStellaratorGCMu.ew_C2_cell cE_avecT.1 cE_avecT.2 hρ hlm).1
    rw [← cE_mvec] at h
    simpa [cE, RationalStellaratorGCMu.C2QE] using h
  hC2Z := by
    have h := (RationalStellaratorGCMu.ew_C2_cell cE_avecT.1 cE_avecT.2 hρ hlm).2
    rw [← cE_mvec] at h
    simpa [cE, RationalStellaratorGCMu.C2QE] using h
  hvR := (ew_valid cE_avecT.1 cE_avecT.2 ρ hlm).2.1
  hvZ := (ew_valid cE_avecT.1 cE_avecT.2 ρ hlm).2.2
  hδ2 := by
    have := Real.exp_one_lt_d9
    rw [le_div_iff₀ (Real.exp_pos 1)]
    simp only [cE, δ0G, KamTorusA.rA]
    norm_num at this ⊢
    nlinarith
  hac := by
    have := exp_rA_le'; push_cast at this; simp only [cE, acG]; linarith
  hE1 := ⟨by norm_num [cE], by
    have := Real.exp_one_gt_d9; simp only [cE]; norm_num at this ⊢; linarith⟩
  hcb := ⟨cE_cK, cE_cL⟩

/-- The limiting strip `ρ_∞ = r_A/7`. -/
theorem rInf_cE : rInf cE = KamTorusA.rA / 7 := by unfold rInf; simp only [cE, δ0G]; ring

end PlasmaLean.Design.RationalStellaratorGC
