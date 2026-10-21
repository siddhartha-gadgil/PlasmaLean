/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCBoxAdm

/-!
# Exact invariant tori of the `μ > 0` passing fields over a box of energies and pitch angles

For every gyro-length `ρ ∈ rhoBox = [1/256 − 2⁻⁸⁶, 1/256]` and every pitch parameter
`λ = μB₀/E ∈ [0, 1/16]` the hypotheses `KamH` of the KAM theorem with inverse-square-root nodes
hold for the field `gcFlowMu ρ λ` at the certified pitch-angle family torus `K(λ)`, with the
constants `cM` of `Design/RationalStellaratorGCMuExact`:

* the residual and admissibility come from `Design/RationalStellaratorGCBoxAdm`;
* node validity is independent of `ρ` (`gcFlowMu_valid`);
* the Taylor constant `C₂` is uniform: `ρ` and `λ` enter the residual trees only through
  constants of modulus `≤ 1/256` and `≤ 1/16` (`constLe_res_box`, `PolyExprS.ConstLe`), so the
  kernel bound `C₂ ≤ 9.35 × 10¹⁰` at `(1/256, 1/16)` covers the box.

**Main result** (`box_family_torus`): for every `(ρ, λ) ∈ rhoBox × [0, 1/16]` there is a real
analytic torus solving the flow-form invariance equation of `gcFlowMu ρ λ` exactly,
`μ = 10⁻¹¹`-close to `K(λ)` on the strip `r_A/7`.

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `box_family_torus_center`: at `ρ = 1/256` this is an instance of the pitch-angle
family statement.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 Complex
open PlasmaLean.Certificates.KronBallCheb

/-- The residual trees at `(ρ, λ)` in the box are `ConstLe` those at `(1/256, 1/16)`. -/
theorem constLe_res_box {ρ lm : ℝ} (hρ : |ρ| ≤ 1 / 256) (h : |lm| ≤ RationalStellaratorGCMu.lam1) :
    PolyExprS.ConstLe (gcFlowMu ρ lm).resRp
        (gcFlowMu (1 / 256) RationalStellaratorGCMu.lam1).resRp ∧
    PolyExprS.ConstLe (gcFlowMu ρ lm).resZp
        (gcFlowMu (1 / 256) RationalStellaratorGCMu.lam1).resZp := by
  have hF := RationalStellaratorGCMu.constLe_eF h
  have hc : ‖(ρ : ℂ)‖ ≤ ‖(((1 / 256 : ℝ)) : ℂ)‖ := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 256)]; exact hρ
  have r := PolyExprS.constLe_refl (𝕜 := ℂ) (σ := Fin 6)
  exact ⟨.sub (.mul (.add (r _) (.mul (.const hc) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (.const hc) (.mul hF (r _)))),
    .sub (.mul (.add (r _) (.mul (.const hc) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (.const hc) (.mul hF (r _))))⟩

/-- **The Taylor constants, uniform over the box** (`|ρ| ≤ 1/256`, `|λ| ≤ 1/16`). -/
theorem box_C2 {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i)
    (haa : ∀ i, a i ≤ RationalStellaratorGCMu.aTQ i) {ρ lm : ℝ} (hρ : |ρ| ≤ 1 / 256)
    (hlm : |lm| ≤ RationalStellaratorGCMu.lam1) :
    PolyExprS.majD2 a (fun i => (RationalStellaratorGCMu.mvQ i : ℝ)) (gcFlowMu ρ lm).resRp / 2 ≤
      (RationalStellaratorGCMu.C2Q : ℝ) ∧
    PolyExprS.majD2 a (fun i => (RationalStellaratorGCMu.mvQ i : ℝ)) (gcFlowMu ρ lm).resZp / 2 ≤
      (RationalStellaratorGCMu.C2Q : ℝ) := by
  have hb : ∀ i, (0 : ℝ) ≤ (RationalStellaratorGCMu.mvQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ RationalStellaratorGCMu.mvQ i by decide +kernel) i
    exact_mod_cast this
  obtain ⟨cR, cZ⟩ := constLe_res_box hρ hlm
  have vR := PQS.valid_of_nodesOK RationalStellaratorGCMu.nodesOK_res.1
  have vZ := PQS.valid_of_nodesOK RationalStellaratorGCMu.nodesOK_res.2
  have mR := PolyExprS.majD2_mono (b := fun i => (RationalStellaratorGCMu.mvQ i : ℝ))
    (b' := fun i => (RationalStellaratorGCMu.mvQ i : ℝ)) ha hb haa (fun _ => le_rfl)
    (cR.valid RationalStellaratorGCMu.aTQ_nonneg vR)
  have mZ := PolyExprS.majD2_mono (b := fun i => (RationalStellaratorGCMu.mvQ i : ℝ))
    (b' := fun i => (RationalStellaratorGCMu.mvQ i : ℝ)) ha hb haa (fun _ => le_rfl)
    (cZ.valid RationalStellaratorGCMu.aTQ_nonneg vZ)
  have kR := cR.majD2_le RationalStellaratorGCMu.aTQ_nonneg hb vR
  have kZ := cZ.majD2_le RationalStellaratorGCMu.aTQ_nonneg hb vZ
  exact ⟨by linarith [RationalStellaratorGCMu.mu_C2R],
    by linarith [RationalStellaratorGCMu.mu_C2Z]⟩

/-- **Validity over the box** (independent of `ρ`). -/
theorem box_valid {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i)
    (haa : ∀ i, a i ≤ RationalStellaratorGCMu.aTQ i) (ρ : ℝ) {lm : ℝ}
    (hlm : |lm| ≤ RationalStellaratorGCMu.lam1) :
    (gcFlowMu ρ lm).Valid6 a ∧ PolyExprS.Valid a (gcFlowMu ρ lm).resRp ∧
      PolyExprS.Valid a (gcFlowMu ρ lm).resZp := by
  obtain ⟨hE, hE4, hN⟩ := RationalStellaratorGCMu.mu_node_bounds ha haa hlm
  exact gcFlowMu_valid ρ lm a hE hE4 hN

/-- The global conditions over the box. -/
theorem box_global {ρ lm : ℝ} (hρ : |ρ| ≤ 1 / 256) (hlm : |lm| ≤ RationalStellaratorGCMu.lam1) :
    (gcFlowMu ρ lm).GlobalH cM KamTorusA.iota where
  dio := iota_dio
  γ_pos := by norm_num [cM]
  hτ' := cM_τ'
  hC2R := by
    have h := (box_C2 cM_avecT.1 cM_avecT.2 hρ hlm).1
    rwa [← cM_mvec] at h
  hC2Z := by
    have h := (box_C2 cM_avecT.1 cM_avecT.2 hρ hlm).2
    rwa [← cM_mvec] at h
  hvR := (box_valid cM_avecT.1 cM_avecT.2 ρ hlm).2.1
  hvZ := (box_valid cM_avecT.1 cM_avecT.2 ρ hlm).2.2
  hδ2 := (cM_global hlm).hδ2
  hac := (cM_global hlm).hac
  hE1 := (cM_global hlm).hE1
  hcb := ⟨cM_cK, cM_cL⟩

/-- **All hypotheses of the KAM theorem over the box**: for `ρ ∈ rhoBox` and every parameter
`|c| = 1` (`λ = lamF c`). -/
theorem box_kamH {ρ : ℝ} (hρ : ρ ∈ rhoBox) {c : ℂ} (hc : ‖c‖ = 1) :
    (gcFlowMu ρ (lamF c)).KamH cM KamTorusA.iota (xHM c 4) (xHM c 5) e0M μM where
  G := box_global (abs_le_of_rhoBox hρ) (abs_lamF_le hc)
  hδ0 := (cM_kamH hc).hδ0
  hρ6 := (cM_kamH hc).hρ6
  hθ := rfl
  he₀ := (cM_kamH hc).he₀
  hκ := cM_kap_pos
  hsmall := cM_small
  hcK := cM_cK_nonneg
  hcL := cM_cL_nonneg
  hμK := cM_μK
  hμt := cM_μt
  hμL := cM_μL
  hadm := fun r u z hlo hhi hu hz hC => boxAdm (abs_sub_le_of_rhoBox hρ)
    (lt_of_lt_of_le (by norm_num [cM, δ0G, KamTorusA.rA]) hlo) hhi hc hu hz hC
  ana_u₀ := ana_uM hc
  ana_z₀ := ana_zM hc
  real_u₀ := isReal_uM hc
  real_z₀ := isReal_zM hc
  e0R := boxResR (abs_sub_le_of_rhoBox hρ) hc
  e0Z := boxResZ (abs_sub_le_of_rhoBox hρ) hc
  hvR' := (box_valid cM_avecμ.1 cM_avecμ.2 ρ (abs_lamF_le hc)).2.1
  hvZ' := (box_valid cM_avecμ.1 cM_avecμ.2 ρ (abs_lamF_le hc)).2.2

/-- **Exact invariant tori over the box of gyro-lengths and pitch parameters.** For every
`ρ ∈ [1/256 − 2⁻⁸⁶, 1/256]` and every `λ ∈ [0, 1/16]` there is a real analytic torus `(u, z)`
(strip `r_A/7`) solving the flow-form invariance equation of the `μ > 0` passing field
`gcFlowMu ρ λ` exactly, with rotational transform `ι = (75 + √5)/562`, and `10⁻¹¹`-close to the
certified family torus `K(λ) = (1 + uFamM λ, zFamM λ)`. -/
theorem box_family_torus {ρ lm : ℝ} (hρ : ρ ∈ rhoBox) (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
      (gcFlowMu ρ lm).resR KamTorusA.iota u z = 0 ∧
      (gcFlowMu ρ lm).resZ KamTorusA.iota u z = 0 ∧
      Close (KamTorusA.rA / 7) KamTorusA.iota u z (uFamM lm) (zFamM lm) μM := by
  have h := gcMu_kam_torus (box_kamH hρ (cOfM_norm lm))
  rw [rInf_cM, lamF_cOfM hlm] at h
  exact h

/-- **Sanity**: at the centre `ρ = 1/256` of the box the statement specialises to the pitch-angle
family. -/
theorem box_family_torus_center {lm : ℝ} (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
      (gcFlowMu (1 / 256) lm).resR KamTorusA.iota u z = 0 ∧
      (gcFlowMu (1 / 256) lm).resZ KamTorusA.iota u z = 0 ∧
      Close (KamTorusA.rA / 7) KamTorusA.iota u z (uFamM lm) (zFamM lm) μM :=
  box_family_torus rho0_mem_rhoBox hlm

end PlasmaLean.Design.RationalStellaratorGC
