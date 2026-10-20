/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusAAdm
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An exact invariant torus of the rational stellarator near torus A (KAM route, K3d)

The explicit constants of the Newton step for torus A (`cA`) and the verification of all the
hypotheses of the abstract KAM theorem `KamH.kam_flow_torus` (`Design/KamIteration`):

* the Diophantine constant `γ = 0.0687` of `ι/2` (`torusA_period_diophantine`);
* the initial error `e₀ = 5.83 × 10⁻²²` on the strip `r_A = 0.1257` (`Bd_resR₀`, `Bd_resZ₀`);
* the losses `δ_j = δ₀ 2^{−j}` with `δ₀ = r_A/7`, so the limiting strip is `ρ_∞ = r_A/7 > 0`;
* the admissibility bounds of `Design/KamTorusAAdm` (frame, inverses, torsion `‖T₀‖ ≤ 19.84`,
  twist `|⟨T₀⟩| ≥ 0.22`);
* the step constants `cK ≤ 10800`, `cL ≤ 130500`, Taylor constant `C₂ ≤ 6 × 10⁹`, hence
  `κ ≈ 5.7 × 10⁹`, and **the smallness condition** `32 κ e₀/δ₀⁴ ≈ 1.1 × 10⁻³ ≤ 1` (margin about
  `900`);
* the displacement budget `μ = 10⁻¹⁰` (actual: `4 × 10⁻¹⁴` for the torus,
  `8 × 10⁻¹³` for `∂_θ`, `5 × 10⁻¹³` for `𝓛`).

**Main result** (`torusA_exact`): there is a real analytic torus `(u, z)` on the strip
`r_A/7` with `D 𝓛K = n` exactly (`resR = resZ = 0`, rotational transform exactly
`ι = (75 + √5)/562`) and `‖u − u₀‖, ‖z − z₀‖, ‖∂_θ(u − u₀)‖, ‖∂_θ(z − z₀)‖ ≤ 10⁻¹⁰` on that strip.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamTorusA WEll1Z2 PolyExpr

/-- The initial error `e₀ = 5.83 × 10⁻²²`. -/
def e0A : ℝ := 583 / 10 ^ 24
/-- The initial loss `δ₀ = r_A / 7`. -/
def δ0A : ℝ := rA / 7

/-- **The step constants for torus A.** -/
def cA : SC where
  ρ := rA
  δ0 := δ0A
  γ := 687 / 10000
  θ := e0A / δ0A ^ 4
  au := auA
  az := azA
  aRt := aRtA
  azt := aztA
  aLR := aLRA
  aLz := aLzA
  ac := acA
  bD := 164 / 100
  bDu := 309 / 100
  bDz := 61 / 100
  bnR := 42 / 100
  bnRu := 171 / 100
  bnRz := 108 / 100
  bnZ := 45 / 100
  bnZu := 159 / 100
  bnZz := 143 / 100
  sD := sDA
  sR := sRA
  sW := sWA
  tT := tTA
  τ := τA
  C2 := 6 * 10 ^ 9
  E1 := 2718 / 1000
  cKb := 10800
  cLb := 130500

/-- **Admissibility** of every torus `μ`-close to torus A on a strip `0 < ρ ≤ r_A`. -/
theorem torusA_adm {ρ : ℝ} (hρ : 0 < ρ) (hρA : ρ ≤ rA) {u z : FA} (hu : Ana u) (hz : Ana z)
    (hC : Close ρ iota u z u₀ z₀ μA) : AdmBounds cA iota ρ u z := by
  obtain ⟨hDu, hDb⟩ := adm_Di hρ hρA hC
  obtain ⟨hRu, hRb⟩ := adm_Ri hρ hρA hC
  obtain ⟨hWu, hWb⟩ := adm_Wi hρ hρA hC
  obtain ⟨hT, hτ⟩ := adm_T hρ hρA hC
  exact
  { frame := ⟨hu, hz, hDu, hRu, hWu, ⟨ρ, _, hρ, hDb⟩, ⟨ρ, _, hρ, hRb⟩, ⟨ρ, _, hρ, hWb⟩⟩
    hu := adm_u hρA hC
    hz := adm_z hρA hC
    hRt := adm_Rt hρA hC
    hzt := adm_zt hρA hC
    hLR := adm_LR hρA hC
    hLz := adm_Lz hρA hC
    hbD := adm_eval hρ hρA hC Dp maj_D
    hbDu := adm_pd hρ hρA hC 0 Dp maj_Du
    hbDz := adm_pd hρ hρA hC 1 Dp maj_Dz
    hbnR := adm_eval hρ hρA hC nRp maj_nR
    hbnRu := adm_pd hρ hρA hC 0 nRp maj_nRu
    hbnRz := adm_pd hρ hρA hC 1 nRp maj_nRz
    hbnZ := adm_eval hρ hρA hC nZp maj_nZ
    hbnZu := adm_pd hρ hρA hC 0 nZp maj_nZu
    hbnZz := adm_pd hρ hρA hC 1 nZp maj_nZz
    hsD := hDb
    hsR := hRb
    hsW := hWb
    hT := hT
    hτ := hτ }

/-! ## The numerical conditions -/

/-- Unfolding set for the step constants of `cA`. -/
macro "cA_norm" : tactic =>
  `(tactic| (simp only [SC.cK, SC.k1, SC.k2, SC.kc, SC.k20, SC.g, SC.kη1, SC.kη2, SC.kh, SC.kE,
    SC.tTot, SC.τ', SC.kTc, SC.eM, SC.mA, SC.mV, SC.cL, SC.kA, SC.XRb, SC.XZb, SC.kRem, SC.kS,
    SC.kap, cA, e0A, δ0A, rA, auA, azA, aRtA, aztA, aLRA, aLzA, acA, μA, sDA, sRA, sWA, tTA, τA,
    max_def]; norm_num))

/-- `τ' > 0`. -/
theorem cA_τ' : 0 < cA.τ' := by cA_norm

/-- `cK ≤ 10800`. -/
theorem cA_cK : cA.cK ≤ 10800 := by cA_norm

/-- `cL ≤ 130500`. -/
theorem cA_cL : cA.cL ≤ 130500 := by cA_norm

/-- `cK ≥ 0`. -/
theorem cA_cK_nonneg : 0 ≤ cA.cK := by cA_norm

/-- `cL ≥ 0`. -/
theorem cA_cL_nonneg : 0 ≤ cA.cL := by cA_norm

/-- The Taylor constant of the `R`-residual. -/
theorem cA_C2R : PolyExpr.majD2 (cA.avec + cA.Tq • cA.mvec) cA.mvec resRp / 2 ≤ cA.C2 := by
  simp only [PolyExpr.maj, PolyExpr.majD, PolyExpr.majD2, resRp, Dp, nRp, sumE, monoE,
    PolyExpr.npow, SC.avec, SC.mvec, SC.Tq, cA, e0A, δ0A, rA, auA, azA, aRtA, aztA, aLRA, aLzA,
    acA, μA, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, Fin.isValue, norm_div,
    norm_neg, norm_one, Complex.norm_ofNat]
  norm_num

/-- The Taylor constant of the `z`-residual. -/
theorem cA_C2Z : PolyExpr.majD2 (cA.avec + cA.Tq • cA.mvec) cA.mvec resZp / 2 ≤ cA.C2 := by
  simp only [PolyExpr.maj, PolyExpr.majD, PolyExpr.majD2, resZp, Dp, nZp, sumE, monoE,
    PolyExpr.npow, SC.avec, SC.mvec, SC.Tq, cA, e0A, δ0A, rA, auA, azA, aRtA, aztA, aLRA, aLzA,
    acA, μA, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, Fin.isValue, norm_div,
    norm_neg, norm_one, Complex.norm_ofNat]
  norm_num

/-- **The smallness condition** `32 κ e₀ / δ₀⁴ ≤ 1` (the actual value is `≈ 1.1 × 10⁻³`). -/
theorem cA_small : 32 * cA.kap * e0A / cA.δ0 ^ 4 ≤ 1 := by cA_norm

/-- `κ > 0`. -/
theorem cA_kap_pos : 0 < cA.kap := by cA_norm

/-- Displacement budget (torus). -/
theorem cA_μK : 2 * cA.cK * e0A / cA.δ0 ^ 2 ≤ μA := by cA_norm

/-- Displacement budget (`θ`-derivatives). -/
theorem cA_μt : 2 * (cA.cK / cA.E1) * e0A / cA.δ0 ^ 3 ≤ μA := by cA_norm

/-- Displacement budget (transport). -/
theorem cA_μL : 2 * cA.cL * e0A / cA.δ0 ^ 2 ≤ μA := by cA_norm

/-- `ι/2` is `(0.0687, 1)`-Diophantine. -/
theorem iota_dio : Diophantine (iota / 2) (687 / 10000) 1 := torusA_period_diophantine

/-- The global conditions for torus A. -/
theorem cA_global : GlobalH cA iota where
  dio := iota_dio
  γ_pos := by norm_num [cA]
  hτ' := cA_τ'
  hC2R := cA_C2R
  hC2Z := cA_C2Z
  hδ2 := by
    have := Real.exp_one_lt_d9
    rw [le_div_iff₀ (Real.exp_pos 1)]
    simp only [cA, δ0A, rA]
    norm_num at this ⊢
    nlinarith
  hac := exp_rA_le_acA
  hE1 := ⟨by norm_num [cA], by
    have := Real.exp_one_gt_d9; simp only [cA]; norm_num at this ⊢; linarith⟩
  hcb := ⟨cA_cK, cA_cL⟩

/-- **All hypotheses of the KAM theorem hold for torus A.** -/
theorem cA_kamH : KamH cA iota u₀ z₀ e0A μA where
  G := cA_global
  hδ0 := by norm_num [cA, δ0A, rA]
  hρ6 := by norm_num [cA, δ0A, rA]
  hθ := rfl
  he₀ := by norm_num [e0A]
  hκ := cA_kap_pos
  hsmall := cA_small
  hcK := cA_cK_nonneg
  hcL := cA_cL_nonneg
  hμK := cA_μK
  hμt := cA_μt
  hμL := cA_μL
  hadm := fun ρ u z hlo hhi hu hz hC => torusA_adm
    (lt_of_lt_of_le (by norm_num [cA, δ0A, rA]) hlo) hhi hu hz hC
  ana_u₀ := ana_u₀
  ana_z₀ := ana_z₀
  real_u₀ := isReal_u₀
  real_z₀ := isReal_z₀
  e0R := Bd_resR₀
  e0Z := Bd_resZ₀.le (by norm_num [e0A])

/-- The limiting strip `ρ_∞ = r_A/7`. -/
theorem rInf_cA : rInf cA = rA / 7 := by unfold rInf; simp only [cA, δ0A]; ring

/-- **An exact invariant torus near torus A (K3d main theorem).** There is a real analytic torus
`(u, z)` (strip `r_A/7 ≈ 0.018`) solving the flow-form invariance equation of `field (1/4)`
exactly, with rotational transform `ι = (75 + √5)/562`, and `10⁻¹⁰`-close to torus A in
`u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z` on that strip. -/
theorem torusA_exact :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ resR iota u z = 0 ∧
      resZ iota u z = 0 ∧ Close (rA / 7) iota u z u₀ z₀ μA := by
  have := cA_kamH.kam_flow_torus
  rwa [rInf_cA] at this

end PlasmaLean.Design.KamNewton
