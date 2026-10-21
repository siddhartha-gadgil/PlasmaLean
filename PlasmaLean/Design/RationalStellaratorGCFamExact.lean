/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCFamAdm

/-!
# Exact invariant tori of the guiding-centre fields of a whole interval of `ρ` (`gc_family_torus`)

The hypotheses `KamH` of the KAM theorem for fields with an inverse-square-root node
(`Design/KamFlowIterationS`) for the guiding-centre fields `gcFlow ρ` of the rational stellarator,
**for every `ρ ∈ [63/16384, 65/16384]`** (`B₀R₀ ≈ [67.9, 70.06] T·m` for 3.5 MeV
alphas; the SI theorem proves `[67.95, 69.99]`), at the
approximate torus `K(ρ)` given by the family centre `(xHF c 4, xHF c 5)` at the parameter
`c = e^{iϑ}` with `cos ϑ = 2^14 ρ − 64` (a Chebyshev series of degree `10` in `ρ`, certified for
all `ϑ` at once by the family ball chains `Design/RationalStellaratorGCFamChain{H,L}`), and the
rotational transform `ι = (75 + √5)/562`; the constants `cF` are uniform over the cell:

* the Diophantine constant `γ = 0.0687` of `ι/2`;
* the initial error `e₀ = 2.7 × 10⁻²¹` on the strip `r_A = 0.1257` (`famResR`);
* admissibility of every `μ = 10⁻¹¹`-close torus (`famAdm`);
* node validity and the Taylor constant `C₂ ≤ 8.83 × 10¹⁰`, uniform in `|ρ| ≤ 65/16384`
  (`Design/RationalStellaratorGCFamMaj`);
* the step constants `c_K ≤ 6170`, `c_L ≤ 21400`, and **the smallness condition**
  `32 κ e₀/δ₀⁴ ≈ 0.073 ≤ 1`.

**Main result** (`gc_family_torus`): for every `ρ ∈ [63/16384, 65/16384]` there is a real analytic
torus `(u, z)` with `D̃ 𝓛K = ñ` exactly for the guiding-centre flow form of `gcFlow ρ`, `μ`-close
to the family torus `K(ρ)` (`uFam ρ`, `zFam ρ`) on the strip `r_A/7`.

**Sanity.** `cOf_norm`: the parameter `cOf ρ` lies on the unit circle.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 Complex
open PlasmaLean.Certificates.KronBallCheb

/-- Unfolding set for the step constants of `cF`. -/
macro "cF_norm" : tactic =>
  `(tactic| (simp only [SC.cK, SC.k1, SC.k2, SC.kc, SC.k20, SC.g, SC.kη1, SC.kη2, SC.kh, SC.kE,
    SC.tTot, SC.τ', SC.kTc, SC.eM, SC.mA, SC.mV, SC.cL, SC.kA, SC.XRb, SC.XZb, SC.kRem, SC.kS,
    SC.kap, cF, e0F, δ0G, KamTorusA.rA, auF, azF, aRtF, aztF, aLRF, aLzF, acG, μF, sDF, sRF, sWF,
    tTF, τF, RationalStellaratorGCFamily.C2Q, max_def]; norm_num))

/-- `τ' > 0`. -/
theorem cF_τ' : 0 < cF.τ' := by cF_norm

/-- `c_K ≤ 6170`. -/
theorem cF_cK : cF.cK ≤ 6170 := by cF_norm

/-- `c_L ≤ 21400`. -/
theorem cF_cL : cF.cL ≤ 21400 := by cF_norm

/-- `c_K ≥ 0`. -/
theorem cF_cK_nonneg : 0 ≤ cF.cK := by cF_norm

/-- `c_L ≥ 0`. -/
theorem cF_cL_nonneg : 0 ≤ cF.cL := by cF_norm

/-- **The smallness condition** `32 κ e₀/δ₀⁴ ≤ 1` (actual value `≈ 0.073`). -/
theorem cF_small : 32 * cF.kap * e0F / cF.δ0 ^ 4 ≤ 1 := by cF_norm

/-- `κ > 0`. -/
theorem cF_kap_pos : 0 < cF.kap := by cF_norm

/-- Displacement budget (torus). -/
theorem cF_μK : 2 * cF.cK * e0F / cF.δ0 ^ 2 ≤ μF := by cF_norm

/-- Displacement budget (`θ`-derivatives). -/
theorem cF_μt : 2 * (cF.cK / cF.E1) * e0F / cF.δ0 ^ 3 ≤ μF := by cF_norm

/-- Displacement budget (transport). -/
theorem cF_μL : 2 * cF.cL * e0F / cF.δ0 ^ 2 ≤ μF := by cF_norm

/-- The perturbation profile is the rational profile `mvQ`. -/
theorem cF_mvec : cF.mvec = fun i => (RationalStellaratorGCFamily.mvQ i : ℝ) := by
  funext i; fin_cases i <;> simp [SC.mvec, cF, RationalStellaratorGCFamily.mvQ]

/-- The Taylor segment bounds lie below the validity bounds `aTQ`. -/
theorem cF_avecT : (∀ i, 0 ≤ (cF.avec + cF.Tq • cF.mvec) i) ∧
    ∀ i, (cF.avec + cF.Tq • cF.mvec) i ≤ (RationalStellaratorGCFamily.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, SC.mvec, SC.Tq, cF, RationalStellaratorGCFamily.aTQ, auF, azF, aLRF, aLzF,
      acG, μF, e0F, δ0G, KamTorusA.rA] <;> norm_num

/-- The limit segment bounds lie below the validity bounds `aTQ`. -/
theorem cF_avecμ : (∀ i, 0 ≤ (cF.avec + (2 * μF) • mOne) i) ∧
    ∀ i, (cF.avec + (2 * μF) • mOne) i ≤ (RationalStellaratorGCFamily.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, mOne, cF, RationalStellaratorGCFamily.aTQ, auF, azF, aLRF, aLzF, acG, μF] <;>
    norm_num

/-- The global conditions for the family torus at `ρ` (`|ρ| ≤ 65/16384`). -/
theorem cF_global {ρ : ℝ} (hρ : |ρ| ≤ 65 / 16384) : (gcFlow ρ).GlobalH cF KamTorusA.iota where
  dio := iota_dio
  γ_pos := by norm_num [cF]
  hτ' := cF_τ'
  hC2R := by
    have h := RationalStellaratorGCFamily.gc_C2R_cell cF_avecT.1 cF_avecT.2 hρ
    rwa [← cF_mvec] at h
  hC2Z := by
    have h := RationalStellaratorGCFamily.gc_C2Z_cell cF_avecT.1 cF_avecT.2 hρ
    rwa [← cF_mvec] at h
  hvR := (RationalStellaratorGCFamily.gc_valid_res_cell cF_avecT.1 cF_avecT.2 ρ).1
  hvZ := (RationalStellaratorGCFamily.gc_valid_res_cell cF_avecT.1 cF_avecT.2 ρ).2
  hδ2 := by
    have := Real.exp_one_lt_d9
    rw [le_div_iff₀ (Real.exp_pos 1)]
    simp only [cF, δ0G, KamTorusA.rA]
    norm_num at this ⊢
    nlinarith
  hac := by
    have := exp_rA_le'; push_cast at this; simp only [cF, acG]; linarith
  hE1 := ⟨by norm_num [cF], by
    have := Real.exp_one_gt_d9; simp only [cF]; norm_num at this ⊢; linarith⟩
  hcb := ⟨cF_cK, cF_cL⟩

/-- **All hypotheses of the KAM theorem hold for the family torus** at every parameter `|c| = 1`
(`ρ = ρF c`). -/
theorem cF_kamH {c : ℂ} (hc : ‖c‖ = 1) :
    (gcFlow (ρF c)).KamH cF KamTorusA.iota (xHF c 4) (xHF c 5) e0F μF where
  G := cF_global (abs_ρF_le hc)
  hδ0 := by norm_num [cF, δ0G, KamTorusA.rA]
  hρ6 := by norm_num [cF, δ0G, KamTorusA.rA]
  hθ := rfl
  he₀ := by norm_num [e0F]
  hκ := cF_kap_pos
  hsmall := cF_small
  hcK := cF_cK_nonneg
  hcL := cF_cL_nonneg
  hμK := cF_μK
  hμt := cF_μt
  hμL := cF_μL
  hadm := fun ρ u z hlo hhi hu hz hC => famAdm
    (lt_of_lt_of_le (by norm_num [cF, δ0G, KamTorusA.rA]) hlo) hhi hc hu hz hC
  ana_u₀ := ana_uF hc
  ana_z₀ := ana_zF hc
  real_u₀ := isReal_uF hc
  real_z₀ := isReal_zF hc
  e0R := famResR hc
  e0Z := famResZ hc
  hvR' := (RationalStellaratorGCFamily.gc_valid_res_cell cF_avecμ.1 cF_avecμ.2 _).1
  hvZ' := (RationalStellaratorGCFamily.gc_valid_res_cell cF_avecμ.1 cF_avecμ.2 _).2

/-- The limiting strip `ρ_∞ = r_A/7`. -/
theorem rInf_cF : rInf cF = KamTorusA.rA / 7 := by unfold rInf; simp only [cF, δ0G]; ring

/-! ## The parameter of `ρ` -/

/-- The parameter value `c = e^{iϑ}` with `cos ϑ = 2^14 ρ − 64` (clamped to `[−1, 1]`). -/
def cOf (ρ : ℝ) : ℂ :=
  ⟨max (-1) (min 1 (16384 * ρ - 64)), Real.sqrt (1 - max (-1) (min 1 (16384 * ρ - 64)) ^ 2)⟩

/-- **Sanity**: the parameter lies on the unit circle. -/
theorem cOf_norm (ρ : ℝ) : ‖cOf ρ‖ = 1 := by
  set x := max (-1) (min 1 (16384 * ρ - 64)) with hx
  have h1 : -1 ≤ x := le_max_left _ _
  have h2 : x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have h3 : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [Complex.norm_def, Complex.normSq_mk, cOf, ← hx]
  rw [Real.mul_self_sqrt h3, show x * x + (1 - x ^ 2) = 1 by ring, Real.sqrt_one]

/-- On the cell, `ρF (cOf ρ) = ρ`. -/
theorem ρF_cOf {ρ : ℝ} (h : ρ ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384)) : ρF (cOf ρ) = ρ := by
  obtain ⟨h1, h2⟩ := h
  have e : max (-1) (min 1 (16384 * ρ - 64)) = 16384 * ρ - 64 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  simp only [ρF, cOf, e]
  ring

/-- **The family torus** at `ρ` (the `R − 1` component). -/
def uFam (ρ : ℝ) : FA := xHF (cOf ρ) 4

/-- **The family torus** at `ρ` (the `z` component). -/
def zFam (ρ : ℝ) : FA := xHF (cOf ρ) 5

/-- **Exact invariant tori of the guiding-centre fields of the whole cell** `ρ ∈ [63/16384,
65/16384]` (`B₀R₀ ≈ [67.9, 70.06] T·m` for 3.5 MeV alphas; the SI theorem proves
`[67.95, 69.99]`, `v∥ > 0`). For every such `ρ` there is a
real analytic torus `(u, z)` (strip `r_A/7 ≈ 0.018`) solving the flow-form invariance equation of
the guiding-centre field `B̃ = B + ρ ∇×b` of the rational stellarator exactly, with rotational
transform `ι = (75 + √5)/562`, and `10⁻¹¹`-close to the certified family torus
`K(ρ) = (1 + uFam ρ, zFam ρ)` in `u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z` on that strip. -/
theorem gc_family_torus {ρ : ℝ} (hρ : ρ ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384)) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
      (gcFlow ρ).resR KamTorusA.iota u z = 0 ∧ (gcFlow ρ).resZ KamTorusA.iota u z = 0 ∧
      Close (KamTorusA.rA / 7) KamTorusA.iota u z (uFam ρ) (zFam ρ) μF := by
  have h := gc_kam_torus (cF_kamH (cOf_norm ρ))
  rw [rInf_cF, ρF_cOf hρ] at h
  exact h

end PlasmaLean.Design.RationalStellaratorGC
