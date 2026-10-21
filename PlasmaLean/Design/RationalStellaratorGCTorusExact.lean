/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTorusAdm

/-!
# An exact invariant torus of the guiding-centre field (`gc_exact_torus`)

The hypotheses `KamH` of the KAM theorem for fields with an inverse-square-root node
(`Design/KamFlowIterationS`) for the guiding-centre field `gcFlow (1/256)` of the rational
stellarator (`ρ_s = 1/256` in model units), the approximate torus `K₀ = (1 + u₀G, z₀G)` and the
rotational transform `ι = (75 + √5)/562`:

* the Diophantine constant `γ = 0.0687` of `ι/2` (`KamNewton.iota_dio`, as for torus A);
* the initial error `e₀ = 3.7 × 10⁻²³` on the strip `r_A = 0.1257` (`gc_resR_bound`);
* the losses `δ_j = δ₀ 2^{−j}`, `δ₀ = r_A/7`;
* admissibility of every `μ = 10⁻¹²`-close torus (`gc_adm`);
* node validity and the Taylor constant `C₂ ≤ 5.99 × 10¹⁰` (`Design/RationalStellaratorGCTorusMaj`);
* the step constants `c_K ≤ 5310`, `c_L ≤ 18200`, hence `κ ≈ 6.0 × 10¹⁰` and **the smallness
  condition** `32 κ e₀/δ₀⁴ ≈ 6.8 × 10⁻⁴ ≤ 1` (margin about `1470`);
* the displacement budget `μ = 10⁻¹²` (actual: `1.2 × 10⁻¹⁵`, `2.5 × 10⁻¹⁴`, `4.2 × 10⁻¹⁵`).

**Main result** (`gc_exact_torus`): there is a real analytic torus `(u, z)` on the strip `r_A/7`
with `D̃ 𝓛K = ñ` exactly for the guiding-centre flow form (`resR = resZ = 0`), `10⁻¹²`-close to
`K₀` in `u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2

/-- Unfolding set for the step constants of `cGC`. -/
macro "cGC_norm" : tactic =>
  `(tactic| (simp only [SC.cK, SC.k1, SC.k2, SC.kc, SC.k20, SC.g, SC.kη1, SC.kη2, SC.kh, SC.kE,
    SC.tTot, SC.τ', SC.kTc, SC.eM, SC.mA, SC.mV, SC.cL, SC.kA, SC.XRb, SC.XZb, SC.kRem, SC.kS,
    SC.kap, cGC, e0G, δ0G, KamTorusA.rA, auG, azG, aRtG, aztG, aLRG, aLzG, acG, μG, sDG, sRG, sWG,
    tTG, τG, C2Q, max_def]; norm_num))

/-- `τ' > 0`. -/
theorem cGC_τ' : 0 < cGC.τ' := by cGC_norm

/-- `c_K ≤ 5310`. -/
theorem cGC_cK : cGC.cK ≤ 5310 := by cGC_norm

/-- `c_L ≤ 18200`. -/
theorem cGC_cL : cGC.cL ≤ 18200 := by cGC_norm

/-- `c_K ≥ 0`. -/
theorem cGC_cK_nonneg : 0 ≤ cGC.cK := by cGC_norm

/-- `c_L ≥ 0`. -/
theorem cGC_cL_nonneg : 0 ≤ cGC.cL := by cGC_norm

/-- **The smallness condition** `32 κ e₀/δ₀⁴ ≤ 1` (actual value `≈ 6.8 × 10⁻⁴`). -/
theorem cGC_small : 32 * cGC.kap * e0G / cGC.δ0 ^ 4 ≤ 1 := by cGC_norm

/-- `κ > 0`. -/
theorem cGC_kap_pos : 0 < cGC.kap := by cGC_norm

/-- Displacement budget (torus). -/
theorem cGC_μK : 2 * cGC.cK * e0G / cGC.δ0 ^ 2 ≤ μG := by cGC_norm

/-- Displacement budget (`θ`-derivatives). -/
theorem cGC_μt : 2 * (cGC.cK / cGC.E1) * e0G / cGC.δ0 ^ 3 ≤ μG := by cGC_norm

/-- Displacement budget (transport). -/
theorem cGC_μL : 2 * cGC.cL * e0G / cGC.δ0 ^ 2 ≤ μG := by cGC_norm

/-- The perturbation profile is the rational profile `mvQ`. -/
theorem cGC_mvec : cGC.mvec = fun i => (mvQ i : ℝ) := by
  funext i; fin_cases i <;> simp [SC.mvec, cGC, mvQ]

/-- The Taylor segment bounds lie below the validity bounds `aTQ`. -/
theorem cGC_avecT : (∀ i, 0 ≤ (cGC.avec + cGC.Tq • cGC.mvec) i) ∧
    ∀ i, (cGC.avec + cGC.Tq • cGC.mvec) i ≤ (aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, SC.mvec, SC.Tq, cGC, aTQ, auG, azG, aLRG, aLzG, acG, μG, e0G, δ0G,
      KamTorusA.rA] <;> norm_num

/-- The limit segment bounds lie below the validity bounds `aTQ`. -/
theorem cGC_avecμ : (∀ i, 0 ≤ (cGC.avec + (2 * μG) • mOne) i) ∧
    ∀ i, (cGC.avec + (2 * μG) • mOne) i ≤ (aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, mOne, cGC, aTQ, auG, azG, aLRG, aLzG, acG, μG] <;> norm_num

/-- The global conditions for the guiding-centre torus. -/
theorem cGC_global : (gcFlow (1 / 256)).GlobalH cGC KamTorusA.iota where
  dio := iota_dio
  γ_pos := by norm_num [cGC]
  hτ' := cGC_τ'
  hC2R := by have h := gc_C2R cGC_avecT.1 cGC_avecT.2; rwa [← cGC_mvec] at h
  hC2Z := by have h := gc_C2Z cGC_avecT.1 cGC_avecT.2; rwa [← cGC_mvec] at h
  hvR := (gc_valid_res cGC_avecT.1 cGC_avecT.2).1
  hvZ := (gc_valid_res cGC_avecT.1 cGC_avecT.2).2
  hδ2 := by
    have := Real.exp_one_lt_d9
    rw [le_div_iff₀ (Real.exp_pos 1)]
    simp only [cGC, δ0G, KamTorusA.rA]
    norm_num at this ⊢
    nlinarith
  hac := by
    have := exp_rA_le'; push_cast at this; simp only [cGC, acG]; linarith
  hE1 := ⟨by norm_num [cGC], by
    have := Real.exp_one_gt_d9; simp only [cGC]; norm_num at this ⊢; linarith⟩
  hcb := ⟨cGC_cK, cGC_cL⟩

/-- **All hypotheses of the KAM theorem hold for the guiding-centre torus.** -/
theorem cGC_kamH : (gcFlow (1 / 256)).KamH cGC KamTorusA.iota u₀G z₀G e0G μG where
  G := cGC_global
  hδ0 := by norm_num [cGC, δ0G, KamTorusA.rA]
  hρ6 := by norm_num [cGC, δ0G, KamTorusA.rA]
  hθ := rfl
  he₀ := by norm_num [e0G]
  hκ := cGC_kap_pos
  hsmall := cGC_small
  hcK := cGC_cK_nonneg
  hcL := cGC_cL_nonneg
  hμK := cGC_μK
  hμt := cGC_μt
  hμL := cGC_μL
  hadm := fun ρ u z hlo hhi hu hz hC => gc_adm
    (lt_of_lt_of_le (by norm_num [cGC, δ0G, KamTorusA.rA]) hlo) hhi hu hz hC
  ana_u₀ := ana_u₀G
  ana_z₀ := ana_z₀G
  real_u₀ := isReal_u₀G
  real_z₀ := isReal_z₀G
  e0R := gc_resR_bound
  e0Z := gc_resZ_bound
  hvR' := (gc_valid_res cGC_avecμ.1 cGC_avecμ.2).1
  hvZ' := (gc_valid_res cGC_avecμ.1 cGC_avecμ.2).2

/-- The limiting strip `ρ_∞ = r_A/7`. -/
theorem rInf_cGC : rInf cGC = KamTorusA.rA / 7 := by unfold rInf; simp only [cGC, δ0G]; ring

/-- **An exact invariant torus of the guiding-centre field** (`ρ_s = 1/256`). There is a real
analytic torus `(u, z)` (strip `r_A/7 ≈ 0.018`) solving the flow-form invariance equation of the
guiding-centre field `B̃ = B + ρ_s ∇×b` of the rational stellarator exactly, with rotational
transform `ι = (75 + √5)/562`, and `10⁻¹²`-close to the certified torus `K₀ = (1 + u₀G, z₀G)` in
`u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z` on that strip. -/
theorem gc_exact_torus :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
      (gcFlow (1 / 256)).resR KamTorusA.iota u z = 0 ∧
      (gcFlow (1 / 256)).resZ KamTorusA.iota u z = 0 ∧
      Close (KamTorusA.rA / 7) KamTorusA.iota u z u₀G z₀G μG := by
  have := gc_kam_torus cGC_kamH
  rwa [rInf_cGC] at this

end PlasmaLean.Design.RationalStellaratorGC
