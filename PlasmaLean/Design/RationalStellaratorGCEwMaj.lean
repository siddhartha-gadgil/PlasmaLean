/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuMaj

/-!
# Majorants over the energy window: the Taylor constant

The Taylor constant `C₂` of the KAM theorem over the energy window `|ρ − 1/256| ≤ 2⁻³²`,
`|λ| ≤ 1/16`: the gyro-length enters the residual trees only through a constant of modulus
`≤ ρ_max = 1/256 + 2⁻³²` (`constLe_res_ew`, `PolyExprS.ConstLe`), so the kernel-evaluated
rational majorant at `(ρ_max, 1/16)` (`ew_C2R`, `ew_C2Z`) with the perturbation profile
`mvQE = (6400, 6400, 0, 0, 21900, 21900)` of the window constants bounds `½ majD2 ≤ 1.2 × 10¹¹`
for every `(ρ, λ)` of the window and every bound `a ≤ aTQ` (`ew_C2_cell`). Node validity does not
depend on `ρ` (`mu_valid_cell`).

**Sanity.** `gcDMQE_toS`: the mirror embeds to the field expression `gcDM ρ_max λ₁`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCMu

open PlasmaLean.Design.RationalStellaratorGC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Theory.KAM.PQS

/-- The largest gyro-length of the window, `1/256 + 2⁻³²`. -/
def rhoMaxQ : ℚ := 1 / 256 + 1 / 2 ^ 32

/-- The mirror of `D̃` at `(ρ_max, λ₁)`. -/
def gcDMQE : PQS (Fin 6) := .add DpQ (.mul (.const rhoMaxQ) (.mul eFQ eYDQ))
/-- The mirror of `ñ_R` at `(ρ_max, λ₁)`. -/
def gcNRMQE : PQS (Fin 6) := .add nRpQ (.mul (.const rhoMaxQ) (.mul eFQ eYRQ))
/-- The mirror of `ñ_z` at `(ρ_max, λ₁)`. -/
def gcNZMQE : PQS (Fin 6) := .add nZpQ (.mul (.const rhoMaxQ) (.mul eFQ eYZQ))

/-- **Sanity**: the mirror of `D̃` embeds to it. -/
theorem gcDMQE_toS : gcDMQE.toS = gcDM (rhoMaxQ : ℝ) lam1 := by
  simp only [gcDMQE, toS, DpQ_toS, eFQ_toS, eYDQ_toS, gcDM]; push_cast; rfl
/-- The mirror of `ñ_R` embeds to it. -/
theorem gcNRMQE_toS : gcNRMQE.toS = gcNRM (rhoMaxQ : ℝ) lam1 := by
  simp only [gcNRMQE, toS, nRpQ_toS, eFQ_toS, eYRQ_toS, gcNRM]; push_cast; rfl
/-- The mirror of `ñ_z` embeds to it. -/
theorem gcNZMQE_toS : gcNZMQE.toS = gcNZM (rhoMaxQ : ℝ) lam1 := by
  simp only [gcNZMQE, toS, nZpQ_toS, eFQ_toS, eYZQ_toS, gcNZM]; push_cast; rfl

/-- The mirror of the `R`-residual expression at `(ρ_max, λ₁)`. -/
def resRQE : PQS (Fin 6) := .sub (.mul gcDMQE (.var 4)) gcNRMQE
/-- The mirror of the `z`-residual expression at `(ρ_max, λ₁)`. -/
def resZQE : PQS (Fin 6) := .sub (.mul gcDMQE (.var 5)) gcNZMQE

/-- The mirror of the `R`-residual embeds to it. -/
theorem resRQE_toS : resRQE.toS = (gcFlowMu (rhoMaxQ : ℝ) lam1).resRp := by
  simp only [resRQE, toS, gcDMQE_toS, gcNRMQE_toS]; rfl
/-- The mirror of the `z`-residual embeds to it. -/
theorem resZQE_toS : resZQE.toS = (gcFlowMu (rhoMaxQ : ℝ) lam1).resZp := by
  simp only [resZQE, toS, gcDMQE_toS, gcNZMQE_toS]; rfl

/-- The perturbation profile of the window constants `(c_K, c_K, 0, 0, c_L, c_L)`. -/
def mvQE : Fin 6 → ℚ := ![6400, 6400, 0, 0, 21900, 21900]

/-- The Taylor constant over the window. -/
def C2QE : ℚ := 120000000000

/-- **The node condition on the residual trees** at `aTQ`, `(ρ_max, λ₁)`. -/
theorem nodesOK_resE :
    NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) (gcFlowMu (rhoMaxQ : ℝ) lam1).resRp ∧
    NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) (gcFlowMu (rhoMaxQ : ℝ) lam1).resZp := by
  obtain ⟨hD, hR, hZ⟩ := nodesOK_eY
  have hF := nodesOK_eF
  have p := nodesOK_ofPoly (fun i => (aTQ i : ℝ)) (gQ : ℝ)
  exact ⟨⟨⟨⟨p _, trivial, hF, hD⟩, trivial⟩, p _, trivial, hF, hR⟩,
    ⟨⟨⟨p _, trivial, hF, hD⟩, trivial⟩, p _, trivial, hF, hZ⟩⟩

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `R`-residual** at `aTQ`, `(ρ_max, λ₁)`. -/
theorem ew_C2R : PolyExprS.majD2 (fun i => (aTQ i : ℝ)) (fun i => (mvQE i : ℝ))
    (gcFlowMu (rhoMaxQ : ℝ) lam1).resRp / 2 ≤ (C2QE : ℝ) := by
  rw [← resRQE_toS]
  have h2 := majD2_le (a := aTQ) (b := mvQE) (g := gQ) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) resRQE (by rw [resRQE_toS]; exact nodesOK_resE.1)
  have h3 : (mD2Q aTQ mvQE gQ resRQE : ℝ) / 2 ≤ C2QE := by
    exact_mod_cast (show mD2Q aTQ mvQE gQ resRQE / 2 ≤ C2QE by decide +kernel)
  linarith

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `z`-residual** at `aTQ`, `(ρ_max, λ₁)`. -/
theorem ew_C2Z : PolyExprS.majD2 (fun i => (aTQ i : ℝ)) (fun i => (mvQE i : ℝ))
    (gcFlowMu (rhoMaxQ : ℝ) lam1).resZp / 2 ≤ (C2QE : ℝ) := by
  rw [← resZQE_toS]
  have h2 := majD2_le (a := aTQ) (b := mvQE) (g := gQ) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) resZQE (by rw [resZQE_toS]; exact nodesOK_resE.2)
  have h3 : (mD2Q aTQ mvQE gQ resZQE : ℝ) / 2 ≤ C2QE := by
    exact_mod_cast (show mD2Q aTQ mvQE gQ resZQE / 2 ≤ C2QE by decide +kernel)
  linarith

/-- The residual trees at `(ρ, λ)` in the window are `ConstLe` those at `(ρ_max, λ₁)`. -/
theorem constLe_res_ew {ρ lm : ℝ} (hρ : |ρ| ≤ (rhoMaxQ : ℝ)) (h : |lm| ≤ lam1) :
    PolyExprS.ConstLe (gcFlowMu ρ lm).resRp (gcFlowMu (rhoMaxQ : ℝ) lam1).resRp ∧
    PolyExprS.ConstLe (gcFlowMu ρ lm).resZp (gcFlowMu (rhoMaxQ : ℝ) lam1).resZp := by
  have hF := constLe_eF h
  have hc : ‖(ρ : ℂ)‖ ≤ ‖((rhoMaxQ : ℝ) : ℂ)‖ := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num [rhoMaxQ] : (0 : ℝ) < (rhoMaxQ : ℝ))]; exact hρ
  have r := PolyExprS.constLe_refl (𝕜 := ℂ) (σ := Fin 6)
  exact ⟨.sub (.mul (.add (r _) (.mul (.const hc) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (.const hc) (.mul hF (r _)))),
    .sub (.mul (.add (r _) (.mul (.const hc) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (.const hc) (.mul hF (r _))))⟩

/-- **The Taylor constants, uniform over the window** (`|ρ| ≤ ρ_max`, `|λ| ≤ 1/16`, `a ≤ aTQ`). -/
theorem ew_C2_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {ρ lm : ℝ}
    (hρ : |ρ| ≤ (rhoMaxQ : ℝ)) (hlm : |lm| ≤ lam1) :
    PolyExprS.majD2 a (fun i => (mvQE i : ℝ)) (gcFlowMu ρ lm).resRp / 2 ≤ (C2QE : ℝ) ∧
    PolyExprS.majD2 a (fun i => (mvQE i : ℝ)) (gcFlowMu ρ lm).resZp / 2 ≤ (C2QE : ℝ) := by
  have hb : ∀ i, (0 : ℝ) ≤ (mvQE i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ mvQE i by decide +kernel) i
    exact_mod_cast this
  obtain ⟨cR, cZ⟩ := constLe_res_ew hρ hlm
  have vR := valid_of_nodesOK nodesOK_resE.1
  have vZ := valid_of_nodesOK nodesOK_resE.2
  have mR := PolyExprS.majD2_mono (b := fun i => (mvQE i : ℝ)) (b' := fun i => (mvQE i : ℝ)) ha hb
    haa (fun _ => le_rfl) (cR.valid aTQ_nonneg vR)
  have mZ := PolyExprS.majD2_mono (b := fun i => (mvQE i : ℝ)) (b' := fun i => (mvQE i : ℝ)) ha hb
    haa (fun _ => le_rfl) (cZ.valid aTQ_nonneg vZ)
  have kR := cR.majD2_le aTQ_nonneg hb vR
  have kZ := cZ.majD2_le aTQ_nonneg hb vZ
  exact ⟨by linarith [ew_C2R], by linarith [ew_C2Z]⟩

end PlasmaLean.Design.RationalStellaratorGCMu
