/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowFrameS
public import PlasmaLean.Design.KamFlowStep

/-!
# One Newton step for a flow field with an inverse-square-root node (`kam_step`)

The quasi-Newton step of `Design/KamFlowStep`, verbatim, for a field `F : FlowFieldS`
(`Design/KamFlowFieldS`), with the same constants `SC` (`cK`, `cL`, `κ`) and the same estimates:
`‖ΔK‖_{ρ−2δ} ≤ cK e/δ²`, `‖𝓛ΔK‖_{ρ−2δ} ≤ cL e/δ²`, `‖E'‖_{ρ−2δ} ≤ κ e²/δ⁴`
(`FlowFieldS.StepH.kam_step`). The only changes:

* the Taylor estimate of the residual uses the majorants of `PolyExprS` (`PolyExprS.Bd.taylorS`),
  which require the **validity** of the residual expressions at the enlarged bounds
  `avec + Tq·mvec` (`StepH.hvR`, `StepH.hvZ`): along the whole segment from `K` to `K + ΔK` every
  node `(c + d)^{−1/2}` stays inside its disc of convergence;
* reality of the field quantities is proved with `PolyExprS.IsReal.evalS`/`derivS` (the node is
  positive at real points), and the torsion numerator is the formula `FlowFieldS.Pof`.

**Sanity.** `majD2_smulS`: the second-derivative majorant is quadratic in the direction, also
through the node.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM Complex WEll1Z2

/-! ## Homogeneity of the majorants with the node -/

section Homog

variable {σ : Type*}

/-- `P̂'(a)·(t b) = t P̂'(a)·b`. -/
theorem majD_smulS (a b : σ → ℝ) (t : ℝ) (e : PolyExprS ℂ σ) :
    PolyExprS.majD a (t • b) e = t * PolyExprS.majD a b e := by
  induction e with
  | const c => simp [PolyExprS.majD]
  | var i => simp [PolyExprS.majD]
  | add p q hp hq => simp only [PolyExprS.majD, hp, hq]; ring
  | sub p q hp hq => simp only [PolyExprS.majD, hp, hq]; ring
  | mul p q hp hq => simp only [PolyExprS.majD, hp, hq]; ring
  | isqrt c d hd => simp only [PolyExprS.majD, hd]; ring

/-- **Sanity**: `P̂''(a)[t b, t b] = t² P̂''(a)[b, b]`, also through the node. -/
theorem majD2_smulS (a b : σ → ℝ) (t : ℝ) (e : PolyExprS ℂ σ) :
    PolyExprS.majD2 a (t • b) e = t ^ 2 * PolyExprS.majD2 a b e := by
  induction e with
  | const c => simp [PolyExprS.majD2]
  | var i => simp [PolyExprS.majD2]
  | add p q hp hq => simp only [PolyExprS.majD2, hp, hq]; ring
  | sub p q hp hq => simp only [PolyExprS.majD2, hp, hq]; ring
  | mul p q hp hq => simp only [PolyExprS.majD2, majD_smulS, hp, hq]; ring
  | isqrt c d hd => simp only [PolyExprS.majD2, majD_smulS, hd]; ring

end Homog

namespace FlowFieldS

variable (F : FlowFieldS)

/-- `D w_R − n_R` has real coefficients. -/
theorem real_resRp : PolyExprS.RealConstsS F.resRp := ⟨⟨F.real_Dp, True.intro⟩, F.real_nRp⟩

/-- `D w_z − n_z` has real coefficients. -/
theorem real_resZp : PolyExprS.RealConstsS F.resZp := ⟨⟨F.real_Dp, True.intro⟩, F.real_nZp⟩

/-! ## The Newton correction -/

section StepDefs

variable (ι : ℝ) (u z : FA)

/-- `ξ₂⁰ = −½ coh_{ι/2}(η₂)`: the zero-mean solution of `𝓛ξ₂⁰ = −η₂`. -/
def xi20 : FA := (-(1 / 2 : ℂ)) • coh (ι / 2) (F.eta2 ι u z)

/-- The average `c̄ = −⟨η₁ + Tξ₂⁰⟩/⟨T⟩` of `ξ₂`, fixed by the twist condition. -/
def cbar : ℂ := -avg (F.eta1 ι u z + F.Tor ι u z * F.xi20 ι u z) / avg (F.Tor ι u z)

/-- `ξ₂ = ξ₂⁰ + c̄`. -/
def xi2 : FA := F.xi20 ι u z + algebraMap ℂ FA (F.cbar ι u z)

/-- `ξ₁ = −½ coh_{ι/2}(η₁ + Tξ₂)`. -/
def xi1 : FA := (-(1 / 2 : ℂ)) • coh (ι / 2) (F.eta1 ι u z + F.Tor ι u z * F.xi2 ι u z)

/-- The correction `ΔR = ξ₁ ∂_θR + ξ₂ N_R`. -/
def dRs : FA := F.xi1 ι u z * Rt u + F.xi2 ι u z * F.NR u z

/-- The correction `Δz = ξ₁ ∂_θz + ξ₂ N_z`. -/
def dZs : FA := F.xi1 ι u z * zt z + F.xi2 ι u z * F.NZ u z

end StepDefs

namespace FrameHyp

variable {F : FlowFieldS} {ι γ : ℝ} {u z : FA} (H : F.FrameHyp u z)
include H

/-- Analyticity: `η₁`. -/
theorem ana_eta1 : Ana (F.eta1 ι u z) :=
  H.anaWi.mul ((H.ana_z.mul H.ana_EhR).sub (H.ana_u.mul H.ana_EhZ))
/-- Analyticity: `η₂`. -/
theorem ana_eta2 : Ana (F.eta2 ι u z) :=
  H.ana_wD.mul ((H.ana_Rt.mul H.ana_EhZ).sub (H.ana_zt.mul H.ana_EhR))
/-- Analyticity: `T₀`. -/
theorem ana_Talg : Ana (F.Talg u z) :=
  (((H.ana_R.pow 3).mul (H.anaDi.pow 3)).mul (H.anaWi.pow 2)).mul H.ana_Pof
/-- Analyticity: `T`. -/
theorem ana_Tor : Ana (F.Tor ι u z) :=
  H.ana_Talg.add ((((H.ana_R.pow 3).mul H.anaDi).mul (H.anaWi.pow 2)).mul
    ((H.ana_EhR.mul H.ana_z).sub (H.ana_EhZ.mul H.ana_u)))

variable (hD : Diophantine (ι / 2) γ 1) (hγ : 0 < γ)
include hD hγ

/-- Analyticity: `ξ₂⁰`. -/
theorem ana_xi20 : Ana (F.xi20 ι u z) := ((H.ana_eta2.coh hD hγ).1).smul _
/-- Analyticity: `ξ₂`. -/
theorem ana_xi2 : Ana (F.xi2 ι u z) := (H.ana_xi20 hD hγ).add (Ana.algebraMap _)
/-- Analyticity: `ξ₁`. -/
theorem ana_xi1 : Ana (F.xi1 ι u z) :=
  (((H.ana_eta1.add (H.ana_Tor.mul (H.ana_xi2 hD hγ))).coh hD hγ).1).smul _
/-- Analyticity: `ΔR`. -/
theorem ana_dRs : Ana (F.dRs ι u z) :=
  ((H.ana_xi1 hD hγ).mul H.ana_Rt).add ((H.ana_xi2 hD hγ).mul (H.ana_hN.mul H.ana_u))
/-- Analyticity: `Δz`. -/
theorem ana_dZs : Ana (F.dZs ι u z) :=
  ((H.ana_xi1 hD hγ).mul H.ana_zt).add ((H.ana_xi2 hD hγ).mul (H.ana_hN.mul H.ana_z))

/-- **`𝓛ξ₂ = −η₂`** (uses the exact flux identity `⟨η₂⟩ = 0`). -/
theorem Lt_xi2 : Lt ι (F.xi2 ι u z) = -F.eta2 ι u z := by
  rw [Lt, xi2, dS_add _ _ (H.ana_xi20 hD hγ) (Ana.algebraMap _), dS_algebraMap, add_zero,
    ← Lt, Lt_eq_two ι (H.ana_xi20 hD hγ), xi20,
    dS_smul _ _ _ ((H.ana_eta2.coh hD hγ).1), dS_coh hD hγ H.ana_eta2 H.avg_eta2, smul_smul]
  norm_num

/-- **`𝓛ξ₁ = −(η₁ + Tξ₂)`** (uses the twist `⟨T⟩ ≠ 0` through the choice of `c̄`). -/
theorem Lt_xi1 (htw : avg (F.Tor ι u z) ≠ 0) :
    Lt ι (F.xi1 ι u z) = -(F.eta1 ι u z + F.Tor ι u z * F.xi2 ι u z) := by
  have hana : Ana (F.eta1 ι u z + F.Tor ι u z * F.xi2 ι u z) :=
    H.ana_eta1.add (H.ana_Tor.mul (H.ana_xi2 hD hγ))
  have havg : avg (F.eta1 ι u z + F.Tor ι u z * F.xi2 ι u z) = 0 := by
    have e1 : F.Tor ι u z * algebraMap ℂ FA (F.cbar ι u z) = F.cbar ι u z • F.Tor ι u z := by
      rw [Algebra.smul_def, mul_comm]
    rw [xi2, mul_add, e1, ← add_assoc, avg_add, avg_smul, cbar]
    field_simp
    ring
  rw [Lt_eq_two ι (H.ana_xi1 hD hγ), xi1, dS_smul _ _ _ (hana.coh hD hγ).1,
    dS_coh hD hγ hana havg, smul_smul]
  norm_num
  abel

end FrameHyp



/-- **Hypotheses of one Newton step** at a torus `K = (1 + u, z)` with error `e` and loss `δ`. -/
structure StepH (c : SC) (ι : ℝ) (u z : FA) (e δ : ℝ) : Prop where
  /-- The frame hypotheses. -/
  frame : F.FrameHyp u z
  /-- `ι/2` is `(γ, 1)`-Diophantine. -/
  dio : Diophantine (ι / 2) c.γ 1
  /-- `γ > 0`. -/
  γ_pos : 0 < c.γ
  /-- Torus bound. -/
  hu : Bd c.ρ u c.au
  /-- Torus bound. -/
  hz : Bd c.ρ z c.az
  /-- Torus bound. -/
  hRt : Bd c.ρ (Rt u) c.aRt
  /-- Torus bound. -/
  hzt : Bd c.ρ (zt z) c.azt
  /-- Torus bound. -/
  hLR : Bd c.ρ (LR ι u) c.aLR
  /-- Torus bound. -/
  hLz : Bd c.ρ (Lz ι z) c.aLz
  /-- Bound of `cos 2φ`, `sin 2φ`. -/
  hac : Real.exp c.ρ ≤ c.ac
  /-- Field bound. -/
  hbD : Bd c.ρ (F.Dof u z) c.bD
  /-- Field bound. -/
  hbDu : Bd c.ρ (F.Du u z) c.bDu
  /-- Field bound. -/
  hbDz : Bd c.ρ (F.Dz u z) c.bDz
  /-- Field bound. -/
  hbnR : Bd c.ρ (F.nR u z) c.bnR
  /-- Field bound. -/
  hbnRu : Bd c.ρ (F.nRu u z) c.bnRu
  /-- Field bound. -/
  hbnRz : Bd c.ρ (F.nRz u z) c.bnRz
  /-- Field bound. -/
  hbnZ : Bd c.ρ (F.nZ u z) c.bnZ
  /-- Field bound. -/
  hbnZu : Bd c.ρ (F.nZu u z) c.bnZu
  /-- Field bound. -/
  hbnZz : Bd c.ρ (F.nZz u z) c.bnZz
  /-- Inverse bound. -/
  hsD : Bd c.ρ (F.Di u z) c.sD
  /-- Inverse bound. -/
  hsR : Bd c.ρ (Ri u) c.sR
  /-- Inverse bound. -/
  hsW : Bd c.ρ (Wi u z) c.sW
  /-- Torsion bound. -/
  hT : Bd c.ρ (F.Talg u z) c.tT
  /-- Twist. -/
  hτ : c.τ ≤ ‖avg (F.Talg u z)‖
  /-- Twist margin. -/
  hτ' : 0 < c.τ'
  /-- Taylor constant (`R`). -/
  hC2R : PolyExprS.majD2 (c.avec + c.Tq • c.mvec) c.mvec F.resRp / 2 ≤ c.C2
  /-- Taylor constant (`z`). -/
  hC2Z : PolyExprS.majD2 (c.avec + c.Tq • c.mvec) c.mvec F.resZp / 2 ≤ c.C2
  /-- Validity of the `R`-residual on the Taylor segment. -/
  hvR : PolyExprS.Valid (c.avec + c.Tq • c.mvec) F.resRp
  /-- Validity of the `z`-residual on the Taylor segment. -/
  hvZ : PolyExprS.Valid (c.avec + c.Tq • c.mvec) F.resZp
  /-- Error. -/
  heR : Bd c.ρ (F.resR ι u z) e
  /-- Error. -/
  heZ : Bd c.ρ (F.resZ ι u z) e
  /-- Error scale. -/
  heθ : e ≤ c.θ * δ ^ 4
  /-- `δ > 0`. -/
  hδ : 0 < δ
  /-- `δ ≤ δ₀`. -/
  hδ0 : δ ≤ c.δ0
  /-- Room for the losses. -/
  h3δ : 3 * δ ≤ c.ρ
  /-- Rüssmann range. -/
  hδ2 : c.δ0 ≤ 2 / Real.exp 1
  /-- `0 < E1 ≤ e`. -/
  hE1 : 0 < c.E1 ∧ c.E1 ≤ Real.exp 1
  /-- `cK ≤ cKb`, `cL ≤ cLb`. -/
  hcb : c.cK ≤ c.cKb ∧ c.cL ≤ c.cLb

namespace StepH

variable {F : FlowFieldS} {c : SC} {ι : ℝ} {u z : FA} {e δ : ℝ} (h : F.StepH c ι u z e δ)
include h

/-- `e ≥ 0`. -/
theorem e_nonneg : 0 ≤ e := h.heR.nonneg
/-- `ρ > 0`. -/
theorem ρ_pos : 0 < c.ρ := by linarith [h.hδ, h.h3δ]
/-- `e ≤ eM`. -/
theorem e_le_eM : e ≤ c.eM := by
  have h1 : δ ^ 4 ≤ c.δ0 ^ 4 := pow_le_pow_left₀ h.hδ.le h.hδ0 4
  have hθ : 0 ≤ c.θ := by
    have := h.heθ; have := h.e_nonneg
    by_contra hneg; push Not at hneg
    have : c.θ * δ ^ 4 < 0 := mul_neg_of_neg_of_pos hneg (by have := h.hδ; positivity)
    linarith
  unfold SC.eM; nlinarith [h.heθ, mul_le_mul_of_nonneg_left h1 hθ]

/-- `‖Ê_R‖ ≤ sD e`. -/
theorem bEhR : Bd c.ρ (F.EhR ι u z) (e * c.sD) := h.heR.mul h.ρ_pos.le h.hsD
/-- `‖Ê_z‖ ≤ sD e`. -/
theorem bEhZ : Bd c.ρ (F.EhZ ι u z) (e * c.sD) := h.heZ.mul h.ρ_pos.le h.hsD

/-- `‖η₁‖ ≤ kη1 e`. -/
theorem bEta1 : Bd c.ρ (F.eta1 ι u z) (c.kη1 * e) := by
  have hρ := h.ρ_pos.le
  refine (h.hsW.mul hρ ((h.hz.mul hρ h.bEhR).sub (h.hu.mul hρ h.bEhZ))).le (le_of_eq ?_)
  simp only [SC.kη1, SC.kE]; ring

/-- `‖w‖ ≤ bD sR³`. -/
theorem bwD : Bd c.ρ (F.wD u z) (c.bD * c.sR ^ 3) :=
  h.hbD.mul h.ρ_pos.le (h.hsR.pow h.ρ_pos.le 3)

/-- `‖η₂‖ ≤ kη2 e`. -/
theorem bEta2 : Bd c.ρ (F.eta2 ι u z) (c.kη2 * e) := by
  have hρ := h.ρ_pos.le
  refine (h.bwD.mul hρ ((h.hRt.mul hρ h.bEhZ).sub (h.hzt.mul hρ h.bEhR))).le (le_of_eq ?_)
  simp only [SC.kη2, SC.kE]; ring

/-- `‖R‖ ≤ 1 + ‖u‖`. -/
theorem bR : Bd c.ρ (1 + u) (1 + c.au) := (Bd_one c.ρ).add h.hu

/-- `‖h‖ ≤ kh`. -/
theorem bhN : Bd c.ρ (F.hN u z) c.kh := by
  have hρ := h.ρ_pos.le
  exact ((h.bR.pow hρ 3).mul hρ h.hsD).mul hρ h.hsW

/-- `‖T − T₀‖ ≤ kTc e`. -/
theorem bTcorr :
    Bd c.ρ ((1 + u) ^ 3 * F.Di u z * Wi u z ^ 2 * (F.EhR ι u z * z - F.EhZ ι u z * u))
      (c.kTc * e) := by
  have hρ := h.ρ_pos.le
  refine ((((h.bR.pow hρ 3).mul hρ h.hsD).mul hρ (h.hsW.pow hρ 2)).mul hρ
    ((h.bEhR.mul hρ h.hz).sub (h.bEhZ.mul hρ h.hu))).le (le_of_eq ?_)
  simp only [SC.kTc, SC.kE]; ring

/-- `kTc ≥ 0`. -/
theorem kTc_nonneg : 0 ≤ c.kTc := by
  have := h.bTcorr.nonneg
  have he := h.e_nonneg
  by_cases he0 : e = 0
  · have : 0 ≤ (1 + c.au) ^ 3 * c.sD * c.sW ^ 2 * (c.az + c.au) * c.kE := by
      have h1 := h.bR.nonneg; have h2 := h.hsD.nonneg; have h3 := h.hsW.nonneg
      have h4 := h.hz.nonneg; have h5 := h.hu.nonneg
      unfold SC.kE; positivity
    exact this
  · have hpos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
    exact nonneg_of_mul_nonneg_left this hpos

/-- `‖T‖ ≤ tTot`. -/
theorem bTor : Bd c.ρ (F.Tor ι u z) c.tTot := by
  refine (h.hT.add h.bTcorr).le ?_
  unfold SC.tTot
  have := h.e_le_eM; have := h.kTc_nonneg
  nlinarith

/-- `|⟨T⟩| ≥ τ'`. -/
theorem avg_Tor_ge : c.τ' ≤ ‖avg (F.Tor ι u z)‖ := by
  have h1 : ‖avg (F.Tor ι u z) - avg (F.Talg u z)‖ ≤ c.kTc * e := by
    rw [← avg_sub]
    have e1 : F.Tor ι u z - F.Talg u z =
        (1 + u) ^ 3 * F.Di u z * Wi u z ^ 2 * (F.EhR ι u z * z - F.EhZ ι u z * u) := by
      rw [Tor]; ring
    rw [e1]; exact h.bTcorr.norm_avg_le h.ρ_pos.le
  have h2 := norm_sub_norm_le (avg (F.Talg u z)) (avg (F.Tor ι u z))
  rw [norm_sub_rev] at h2
  unfold SC.τ'
  have := h.e_le_eM; have := h.kTc_nonneg; have := h.hτ
  nlinarith

/-- `⟨T⟩ ≠ 0`. -/
theorem avg_Tor_ne : avg (F.Tor ι u z) ≠ 0 := by
  intro h0; have := h.avg_Tor_ge; rw [h0, norm_zero] at this; linarith [h.hτ']

/-! ### Nonnegativity of the constants -/

/-- The base constants are nonnegative. -/
theorem base_nonneg : 0 ≤ c.au ∧ 0 ≤ c.az ∧ 0 ≤ c.aRt ∧ 0 ≤ c.azt ∧ 0 ≤ c.bD ∧ 0 ≤ c.bDu ∧
    0 ≤ c.bDz ∧ 0 ≤ c.bnR ∧ 0 ≤ c.bnRu ∧ 0 ≤ c.bnRz ∧ 0 ≤ c.bnZ ∧ 0 ≤ c.bnZu ∧ 0 ≤ c.bnZz ∧
    0 ≤ c.sD ∧ 0 ≤ c.sR ∧ 0 ≤ c.sW ∧ 0 ≤ c.tT ∧ 0 ≤ c.δ0 ∧ 0 ≤ c.θ :=
  ⟨h.hu.nonneg, h.hz.nonneg, h.hRt.nonneg, h.hzt.nonneg, h.hbD.nonneg, h.hbDu.nonneg,
    h.hbDz.nonneg, h.hbnR.nonneg, h.hbnRu.nonneg, h.hbnRz.nonneg, h.hbnZ.nonneg, h.hbnZu.nonneg,
    h.hbnZz.nonneg, h.hsD.nonneg, h.hsR.nonneg, h.hsW.nonneg, h.hT.nonneg,
    h.hδ.le.trans h.hδ0, by
      have := h.heθ; have := h.e_nonneg; have := h.hδ
      by_contra hn; push Not at hn
      have : c.θ * δ ^ 4 < 0 := mul_neg_of_neg_of_pos hn (by positivity)
      linarith⟩

/-- `g = 2eγ > 0`. -/
theorem g_pos : 0 < c.g := by have := h.γ_pos; have := h.hE1.1; unfold SC.g; positivity

/-- `1/e ≤ 1/E1`. -/
theorem inv_e_le {X : ℝ} (hX : 0 ≤ X) : X / Real.exp 1 ≤ X / c.E1 :=
  div_le_div_of_nonneg_left hX h.hE1.1 h.hE1.2

/-- Derived constants are nonnegative. -/
theorem derived_nonneg : 0 ≤ c.kE ∧ 0 ≤ c.kη1 ∧ 0 ≤ c.kη2 ∧ 0 ≤ c.kh ∧ 0 ≤ c.tTot ∧
    0 ≤ c.k20 ∧ 0 ≤ c.kc ∧ 0 ≤ c.k2 ∧ 0 ≤ c.k1 ∧ 0 ≤ c.mA ∧ 0 ≤ c.mV ∧ 0 ≤ c.cK ∧ 0 ≤ c.kS ∧
    0 ≤ c.kRem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := h.base_nonneg
  have hg := h.g_pos
  have hE := h.hE1.1
  have hτ := h.hτ'
  have hkTc := h.kTc_nonneg
  have heM : 0 ≤ c.eM := by unfold SC.eM; positivity
  have kE : 0 ≤ c.kE := h14
  have kη1 : 0 ≤ c.kη1 := by unfold SC.kη1; positivity
  have kη2 : 0 ≤ c.kη2 := by unfold SC.kη2; positivity
  have kh : 0 ≤ c.kh := by unfold SC.kh; positivity
  have tTot : 0 ≤ c.tTot := by unfold SC.tTot; positivity
  have k20 : 0 ≤ c.k20 := by unfold SC.k20; positivity
  have kc : 0 ≤ c.kc := by unfold SC.kc; positivity
  have k2 : 0 ≤ c.k2 := by unfold SC.k2; positivity
  have k1 : 0 ≤ c.k1 := by unfold SC.k1; positivity
  have mA : 0 ≤ c.mA := le_max_of_le_left h3
  have mV : 0 ≤ c.mV := le_max_of_le_left h1
  have cK : 0 ≤ c.cK := by unfold SC.cK; positivity
  have kS : 0 ≤ c.kS := by unfold SC.kS; positivity
  have kRem : 0 ≤ c.kRem := by unfold SC.kRem; positivity
  exact ⟨kE, kη1, kη2, kh, tTot, k20, kc, k2, k1, mA, mV, cK, kS, kRem⟩

/-! ### The cohomological solves -/

/-- `X ≤ X δ₀/δ` for `X ≥ 0`. -/
theorem up_one {X : ℝ} (hX : 0 ≤ X) : X ≤ X * c.δ0 / δ := by
  rw [mul_div_assoc]
  exact le_mul_of_one_le_right hX ((one_le_div h.hδ).2 h.hδ0)

/-- `‖ξ₂⁰‖_{ρ−δ} ≤ k20 e/δ`. -/
theorem bXi20 : Bd (c.ρ - δ) (F.xi20 ι u z) (c.k20 * e / δ) := by
  have hb := h.bEta2.coh h.dio h.γ_pos h.hδ (by linarith [h.h3δ, h.hδ])
    (h.hδ0.trans h.hδ2)
  refine (hb.smul _).le ?_
  have hE := h.hE1
  have hk := h.derived_nonneg.2.2.1
  have he := h.e_nonneg; have hδ := h.hδ; have hγ := h.γ_pos
  simp only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  rw [show c.k20 * e / δ = 1 / 2 * (c.kη2 * e / (c.E1 * c.γ * δ)) by
    unfold SC.k20 SC.g; field_simp]
  have hE1p := hE.1
  gcongr
  exact hE.2

/-- `‖η₁ + T ξ₂⁰‖_{ρ−δ} ≤ kη1 e + tTot k20 e/δ`. -/
theorem bArg0 : Bd (c.ρ - δ) (F.eta1 ι u z + F.Tor ι u z * F.xi20 ι u z)
    (c.kη1 * e + c.tTot * (c.k20 * e / δ)) :=
  (h.bEta1.strip (by linarith [h.hδ])).add
    ((h.bTor.strip (by linarith [h.hδ])).mul (by linarith [h.h3δ, h.hδ]) h.bXi20)

/-- `|c̄| ≤ kc e/δ`. -/
theorem norm_cbar : ‖F.cbar ι u z‖ ≤ c.kc * e / δ := by
  obtain ⟨-, kη1, -, -, tTot, k20, -⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hδ := h.hδ
  have hτ := h.hτ'
  have h1 : ‖avg (F.eta1 ι u z + F.Tor ι u z * F.xi20 ι u z)‖ ≤
      c.kη1 * e + c.tTot * (c.k20 * e / δ) := h.bArg0.norm_avg_le (by linarith [h.h3δ])
  have h2 := h.avg_Tor_ge
  rw [cbar, norm_div, norm_neg, div_le_iff₀ (lt_of_lt_of_le hτ h2)]
  calc _ ≤ c.kη1 * e + c.tTot * (c.k20 * e / δ) := h1
    _ ≤ c.kη1 * c.δ0 * e / δ + c.tTot * (c.k20 * e / δ) := by
        have := h.up_one (mul_nonneg kη1 he)
        rw [show c.kη1 * e * c.δ0 / δ = c.kη1 * c.δ0 * e / δ by ring] at this
        linarith
    _ = c.kc * e / δ * c.τ' := by
        unfold SC.kc; field_simp
    _ ≤ c.kc * e / δ * ‖avg (F.Tor ι u z)‖ := by
        gcongr; have := h.derived_nonneg.2.2.2.2.2.2.1; positivity

/-- `‖ξ₂‖_{ρ−δ} ≤ k2 e/δ`. -/
theorem bXi2 : Bd (c.ρ - δ) (F.xi2 ι u z) (c.k2 * e / δ) := by
  refine (h.bXi20.add (Bd_algebraMap _ _)).le ?_
  have := h.norm_cbar
  unfold SC.k2
  rw [add_mul, add_div]; linarith

/-- `‖ξ₁‖_{ρ−2δ} ≤ k1 e/δ²`. -/
theorem bXi1 : Bd (c.ρ - 2 * δ) (F.xi1 ι u z) (c.k1 * e / δ ^ 2) := by
  obtain ⟨-, kη1, -, -, tTot, -, -, k2, -⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hδ := h.hδ
  have harg : Bd (c.ρ - δ) (F.eta1 ι u z + F.Tor ι u z * F.xi2 ι u z)
      (c.kη1 * e + c.tTot * (c.k2 * e / δ)) :=
    (h.bEta1.strip (by linarith)).add
      ((h.bTor.strip (by linarith)).mul (by linarith [h.h3δ]) h.bXi2)
  have hb := harg.coh h.dio h.γ_pos h.hδ (by linarith [h.h3δ]) (h.hδ0.trans h.hδ2)
  rw [show c.ρ - δ - δ = c.ρ - 2 * δ by ring] at hb
  refine (hb.smul (-(1 / 2 : ℂ))).le ?_
  have hg := h.g_pos
  have hup := h.up_one (mul_nonneg kη1 he)
  simp only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  have hE := h.hE1
  have hγ := h.γ_pos
  have hE1p := hE.1
  have e0 : 1 / 2 * ((c.kη1 * e + c.tTot * (c.k2 * e / δ)) / (Real.exp 1 * c.γ * δ)) ≤
      1 / 2 * ((c.kη1 * e + c.tTot * (c.k2 * e / δ)) / (c.E1 * c.γ * δ)) := by
    gcongr
    exact hE.2
  have e1 : 1 / 2 * ((c.kη1 * e + c.tTot * (c.k2 * e / δ)) / (c.E1 * c.γ * δ)) =
      (c.kη1 * e + c.tTot * (c.k2 * e / δ)) / (c.g * δ) := by
    unfold SC.g; field_simp
  refine e0.trans ?_
  rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
  have e2 : c.k1 * e * (c.g * δ) = (c.kη1 * c.δ0 * e / δ + c.tTot * (c.k2 * e / δ)) * δ ^ 2 := by
    unfold SC.k1; field_simp
  rw [e2]
  gcongr
  rw [show c.kη1 * c.δ0 * e / δ = c.kη1 * e * c.δ0 / δ by ring]
  exact hup

/-! ### The correction and the remainder -/

/-- `X/δ ≤ X δ₀/δ²` for `X ≥ 0`. -/
theorem up_two {X : ℝ} (hX : 0 ≤ X) : X / δ ≤ X * c.δ0 / δ ^ 2 := by
  have h1 := h.up_one hX
  have hδ := h.hδ
  rw [div_le_div_iff₀ hδ (by positivity)]
  rw [le_div_iff₀ hδ] at h1
  nlinarith

/-- `‖ΔR‖_{ρ−2δ} ≤ cK e/δ²`. -/
theorem bdR : Bd (c.ρ - 2 * δ) (F.dRs ι u z) (c.cK * e / δ ^ 2) := by
  obtain ⟨h1, -, h3, -⟩ := h.base_nonneg
  obtain ⟨-, -, -, kh, -, -, -, k2, k1, -⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have hb := (h.bXi1.mul hρ2 (h.hRt.strip (by linarith [h.hδ]))).add
    ((h.bXi2.strip (by linarith [h.hδ])).mul hρ2
      ((h.bhN.strip (by linarith [h.hδ])).mul hρ2 (h.hu.strip (by linarith [h.hδ]))))
  refine hb.le ?_
  have hA : c.aRt ≤ c.mA := le_max_left _ _
  have hV : c.au ≤ c.mV := le_max_left _ _
  have hup := h.up_two (mul_nonneg k2 he)
  have hδ := h.hδ
  have hδ0' : 0 ≤ c.δ0 := h.hδ.le.trans h.hδ0
  unfold SC.cK
  calc c.k1 * e / δ ^ 2 * c.aRt + c.k2 * e / δ * (c.kh * c.au)
      ≤ c.k1 * e / δ ^ 2 * c.mA + c.k2 * e * c.δ0 / δ ^ 2 * (c.kh * c.mV) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
          (mul_le_mul hup (mul_le_mul_of_nonneg_left hV kh) (by positivity) (by positivity))
    _ = _ := by field_simp

/-- `‖Δz‖_{ρ−2δ} ≤ cK e/δ²`. -/
theorem bdZ : Bd (c.ρ - 2 * δ) (F.dZs ι u z) (c.cK * e / δ ^ 2) := by
  obtain ⟨-, h2, -, h4, -⟩ := h.base_nonneg
  obtain ⟨-, -, -, kh, -, -, -, k2, k1, -⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have hb := (h.bXi1.mul hρ2 (h.hzt.strip (by linarith [h.hδ]))).add
    ((h.bXi2.strip (by linarith [h.hδ])).mul hρ2
      ((h.bhN.strip (by linarith [h.hδ])).mul hρ2 (h.hz.strip (by linarith [h.hδ]))))
  refine hb.le ?_
  have hA : c.azt ≤ c.mA := le_max_right _ _
  have hV : c.az ≤ c.mV := le_max_right _ _
  have hup := h.up_two (mul_nonneg k2 he)
  have hδ := h.hδ
  have hδ0' : 0 ≤ c.δ0 := h.hδ.le.trans h.hδ0
  unfold SC.cK
  calc c.k1 * e / δ ^ 2 * c.azt + c.k2 * e / δ * (c.kh * c.az)
      ≤ c.k1 * e / δ ^ 2 * c.mA + c.k2 * e * c.δ0 / δ ^ 2 * (c.kh * c.mV) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
          (mul_le_mul hup (mul_le_mul_of_nonneg_left hV kh) (by positivity) (by positivity))
    _ = _ := by field_simp

/-- `‖∂_θÊ_R‖_{ρ−δ} ≤ sD e/(eδ)`. -/
theorem bdEhR : Bd (c.ρ - δ) (dTh (F.EhR ι u z)) (e * c.sD / (Real.exp 1 * δ)) := by
  have := h.bEhR.dS h.hδ (by linarith [h.h3δ, h.hδ]) 1 0
  refine this.le (le_of_eq ?_)
  simp only [norm_one, norm_zero, max_eq_left zero_le_one]; ring

/-- `‖∂_θÊ_z‖_{ρ−δ} ≤ sD e/(eδ)`. -/
theorem bdEhZ : Bd (c.ρ - δ) (dTh (F.EhZ ι u z)) (e * c.sD / (Real.exp 1 * δ)) := by
  have := h.bEhZ.dS h.hδ (by linarith [h.h3δ, h.hδ]) 1 0
  refine this.le (le_of_eq ?_)
  simp only [norm_one, norm_zero, max_eq_left zero_le_one]; ring

/-- `‖S‖_{ρ−δ} ≤ kS e/δ`. -/
theorem bS : Bd (c.ρ - δ) (F.Scoef ι u z) (c.kS * e / δ) := by
  obtain ⟨h1, h2, -, -, -, h6, h7, -, -, -, -, -, -, h14, h15, h16, -⟩ := h.base_nonneg
  have he := h.e_nonneg
  have hδ := h.hδ
  have hρ1 : 0 ≤ c.ρ - δ := by linarith [h.h3δ]
  have hs : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - δ) x B := fun hx => hx.strip (by linarith)
  have hb := (((((hs h.hbDu).mul hρ1 (hs h.bEhR)).add ((hs h.hbDz).mul hρ1 (hs h.bEhZ))).mul hρ1
    (hs h.hsD)).neg.add (((Bd_three _).mul hρ1 (hs h.hsR)).mul hρ1 (hs h.bEhR))).sub
    ((hs h.hsW).mul hρ1 ((h.bdEhR.mul hρ1 (hs h.hz)).sub (h.bdEhZ.mul hρ1 (hs h.hu))))
  refine hb.le ?_
  have he1 := Real.exp_pos 1
  have hup := h.up_one (X := ((c.bDu + c.bDz) * c.sD * c.sD + 3 * c.sR * c.sD) * e)
    (by positivity)
  have hinv := h.inv_e_le (X := c.sW * (c.az + c.au) * c.sD) (by positivity)
  unfold SC.kS SC.kE
  have e1 : (c.bDu * (e * c.sD) + c.bDz * (e * c.sD)) * c.sD + 3 * c.sR * (e * c.sD) +
      c.sW * (e * c.sD / (Real.exp 1 * δ) * c.az + e * c.sD / (Real.exp 1 * δ) * c.au) =
      ((c.bDu + c.bDz) * c.sD * c.sD + 3 * c.sR * c.sD) * e +
        c.sW * (c.az + c.au) * c.sD / Real.exp 1 * (e / δ) := by
    field_simp
  rw [e1]
  have e2 : ((c.bDu + c.bDz) * c.sD * c.sD * c.δ0 + 3 * c.sR * c.sD * c.δ0 +
      c.sW * (c.az + c.au) * c.sD / c.E1) * e / δ =
      ((c.bDu + c.bDz) * c.sD * c.sD + 3 * c.sR * c.sD) * e * c.δ0 / δ +
        c.sW * (c.az + c.au) * c.sD / c.E1 * (e / δ) := by
    field_simp
  rw [e2]
  have hed : 0 ≤ e / δ := by positivity
  have := mul_le_mul_of_nonneg_right hinv hed
  linarith

/-- `‖ξ₂ S N_R + ξ₁ ∂_θÊ_R‖_{ρ−2δ} ≤ kRem e²/δ³`. -/
theorem bRemR : Bd (c.ρ - 2 * δ)
    (F.Scoef ι u z * F.xi2 ι u z * F.NR u z + F.xi1 ι u z * dTh (F.EhR ι u z))
    (c.kRem * e ^ 2 / δ ^ 3) := by
  obtain ⟨h1, -⟩ := h.base_nonneg
  obtain ⟨kE, -, -, kh, -, -, -, k2, k1, -, mV, -, kS, -⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hδ := h.hδ
  have hδ0' : 0 ≤ c.δ0 := h.hδ.le.trans h.hδ0
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ]
  have hs1 : ∀ {x : FA} {B : ℝ}, Bd (c.ρ - δ) x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith)
  have hs0 : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith)
  have hb := (((hs1 h.bS).mul hρ2 (hs1 h.bXi2)).mul hρ2 ((hs0 h.bhN).mul hρ2 (hs0 h.hu))).add
    (h.bXi1.mul hρ2 (hs1 h.bdEhR))
  refine hb.le ?_
  have hV : c.au ≤ c.mV := le_max_left _ _
  have he1 := Real.exp_pos 1
  unfold SC.kRem
  have e1 : c.kS * e / δ * (c.k2 * e / δ) * (c.kh * c.au) +
      c.k1 * e / δ ^ 2 * (e * c.sD / (Real.exp 1 * δ)) =
      c.kS * c.k2 * c.kh * c.au * δ * e ^ 2 / δ ^ 3 + c.k1 * c.kE / Real.exp 1 * e ^ 2 / δ ^ 3 := by
    unfold SC.kE; field_simp
  rw [e1, add_mul, add_div]
  have hE1p := h.hE1.1
  gcongr
  all_goals first | exact h.hδ0 | exact h.hE1.2

/-- `‖ξ₂ S N_z + ξ₁ ∂_θÊ_z‖_{ρ−2δ} ≤ kRem e²/δ³`. -/
theorem bRemZ : Bd (c.ρ - 2 * δ)
    (F.Scoef ι u z * F.xi2 ι u z * F.NZ u z + F.xi1 ι u z * dTh (F.EhZ ι u z))
    (c.kRem * e ^ 2 / δ ^ 3) := by
  obtain ⟨-, h2, -⟩ := h.base_nonneg
  obtain ⟨kE, -, -, kh, -, -, -, k2, k1, -, mV, -, kS, -⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hδ := h.hδ
  have hδ0' : 0 ≤ c.δ0 := h.hδ.le.trans h.hδ0
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ]
  have hs1 : ∀ {x : FA} {B : ℝ}, Bd (c.ρ - δ) x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith)
  have hs0 : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith)
  have hb := (((hs1 h.bS).mul hρ2 (hs1 h.bXi2)).mul hρ2 ((hs0 h.bhN).mul hρ2 (hs0 h.hz))).add
    (h.bXi1.mul hρ2 (hs1 h.bdEhZ))
  refine hb.le ?_
  have hV : c.az ≤ c.mV := le_max_right _ _
  have he1 := Real.exp_pos 1
  unfold SC.kRem
  have e1 : c.kS * e / δ * (c.k2 * e / δ) * (c.kh * c.az) +
      c.k1 * e / δ ^ 2 * (e * c.sD / (Real.exp 1 * δ)) =
      c.kS * c.k2 * c.kh * c.az * δ * e ^ 2 / δ ^ 3 + c.k1 * c.kE / Real.exp 1 * e ^ 2 / δ ^ 3 := by
    unfold SC.kE; field_simp
  rw [e1, add_mul, add_div]
  have hE1p := h.hE1.1
  gcongr
  all_goals first | exact h.hδ0 | exact h.hE1.2

/-- `‖(DX)_{RR}‖`. -/
theorem bA11 : Bd c.ρ (F.A11 u z) ((c.bnRu + c.XRb * c.bDu) * c.sD) :=
  (h.hbnRu.sub ((h.hbnR.mul h.ρ_pos.le h.hsD).mul h.ρ_pos.le h.hbDu)).mul h.ρ_pos.le h.hsD
/-- `‖(DX)_{Rz}‖`. -/
theorem bA12 : Bd c.ρ (F.A12 u z) ((c.bnRz + c.XRb * c.bDz) * c.sD) :=
  (h.hbnRz.sub ((h.hbnR.mul h.ρ_pos.le h.hsD).mul h.ρ_pos.le h.hbDz)).mul h.ρ_pos.le h.hsD
/-- `‖(DX)_{zR}‖`. -/
theorem bA21 : Bd c.ρ (F.A21 u z) ((c.bnZu + c.XZb * c.bDu) * c.sD) :=
  (h.hbnZu.sub ((h.hbnZ.mul h.ρ_pos.le h.hsD).mul h.ρ_pos.le h.hbDu)).mul h.ρ_pos.le h.hsD
/-- `‖(DX)_{zz}‖`. -/
theorem bA22 : Bd c.ρ (F.A22 u z) ((c.bnZz + c.XZb * c.bDz) * c.sD) :=
  (h.hbnZz.sub ((h.hbnZ.mul h.ρ_pos.le h.hsD).mul h.ρ_pos.le h.hbDz)).mul h.ρ_pos.le h.hsD

/-- The linearised equation for the actual correction (`R`). -/
theorem LdR_eq : Lt ι (F.dRs ι u z) =
    (F.Scoef ι u z * F.xi2 ι u z * F.NR u z + F.xi1 ι u z * dTh (F.EhR ι u z)) +
      (F.A11 u z * F.dRs ι u z + F.A12 u z * F.dZs ι u z) - F.EhR ι u z := by
  have := h.frame.linear_residual_R (h.frame.ana_xi1 h.dio h.γ_pos) (h.frame.ana_xi2 h.dio h.γ_pos)
    (h.frame.Lt_xi1 h.dio h.γ_pos h.avg_Tor_ne) (h.frame.Lt_xi2 h.dio h.γ_pos)
  rw [dRs, dZs]; linear_combination this

/-- The linearised equation for the actual correction (`z`). -/
theorem LdZ_eq : Lt ι (F.dZs ι u z) =
    (F.Scoef ι u z * F.xi2 ι u z * F.NZ u z + F.xi1 ι u z * dTh (F.EhZ ι u z)) +
      (F.A21 u z * F.dRs ι u z + F.A22 u z * F.dZs ι u z) - F.EhZ ι u z := by
  have := h.frame.linear_residual_Z (h.frame.ana_xi1 h.dio h.γ_pos) (h.frame.ana_xi2 h.dio h.γ_pos)
    (h.frame.Lt_xi1 h.dio h.γ_pos h.avg_Tor_ne) (h.frame.Lt_xi2 h.dio h.γ_pos)
  rw [dRs, dZs]; linear_combination this

/-- `e²/δ³ ≤ θ δ₀³ e/δ²` from `e ≤ θ δ⁴`. -/
theorem sq_le : e ^ 2 / δ ^ 3 ≤ c.θ * c.δ0 ^ 3 * e / δ ^ 2 := by
  have he := h.e_nonneg
  have hδ := h.hδ
  have hθ := h.base_nonneg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h3 : δ ^ 3 ≤ c.δ0 ^ 3 := pow_le_pow_left₀ hδ.le h.hδ0 3
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := h.heθ
  calc e ^ 2 * δ ^ 2 = e * e * δ ^ 2 := by ring
    _ ≤ e * (c.θ * δ ^ 4) * δ ^ 2 := by gcongr
    _ = c.θ * δ ^ 3 * e * δ ^ 3 := by ring
    _ ≤ c.θ * c.δ0 ^ 3 * e * δ ^ 3 := by gcongr

/-- `e ≤ δ₀² e/δ²`. -/
theorem e_le : e ≤ c.δ0 ^ 2 * e / δ ^ 2 := by
  have he := h.e_nonneg
  have hδ := h.hδ
  have h2 : δ ^ 2 ≤ c.δ0 ^ 2 := pow_le_pow_left₀ hδ.le h.hδ0 2
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **`‖𝓛ΔR‖_{ρ−2δ} ≤ cL e/δ²`**. -/
theorem bLdR : Bd (c.ρ - 2 * δ) (Lt ι (F.dRs ι u z)) (c.cL * e / δ ^ 2) := by
  obtain ⟨kE, -, -, -, -, -, -, -, -, -, -, cK, -, kRem⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have hs0 : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith [h.hδ])
  rw [h.LdR_eq]
  refine ((h.bRemR.add (((hs0 h.bA11).mul hρ2 h.bdR).add ((hs0 h.bA12).mul hρ2 h.bdZ))).sub
    (hs0 h.bEhR)).le ?_
  have hkA : (c.bnRu + c.XRb * c.bDu) * c.sD + (c.bnRz + c.XRb * c.bDz) * c.sD ≤ c.kA :=
    le_max_left _ _
  have h1 := h.sq_le
  have h2 := h.e_le
  have hδ := h.hδ
  unfold SC.cL
  have hK : 0 ≤ c.cK * e / δ ^ 2 := by positivity
  calc c.kRem * e ^ 2 / δ ^ 3 +
        ((c.bnRu + c.XRb * c.bDu) * c.sD * (c.cK * e / δ ^ 2) +
          (c.bnRz + c.XRb * c.bDz) * c.sD * (c.cK * e / δ ^ 2)) + e * c.sD
      = c.kRem * (e ^ 2 / δ ^ 3) +
          ((c.bnRu + c.XRb * c.bDu) * c.sD + (c.bnRz + c.XRb * c.bDz) * c.sD) *
            (c.cK * e / δ ^ 2) + c.kE * e := by unfold SC.kE; ring
    _ ≤ c.kRem * (c.θ * c.δ0 ^ 3 * e / δ ^ 2) + c.kA * (c.cK * e / δ ^ 2) +
          c.kE * (c.δ0 ^ 2 * e / δ ^ 2) := by gcongr
    _ = _ := by ring

/-- **`‖𝓛Δz‖_{ρ−2δ} ≤ cL e/δ²`**. -/
theorem bLdZ : Bd (c.ρ - 2 * δ) (Lt ι (F.dZs ι u z)) (c.cL * e / δ ^ 2) := by
  obtain ⟨kE, -, -, -, -, -, -, -, -, -, -, cK, -, kRem⟩ := h.derived_nonneg
  have he := h.e_nonneg
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have hs0 : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith [h.hδ])
  rw [h.LdZ_eq]
  refine ((h.bRemZ.add (((hs0 h.bA21).mul hρ2 h.bdR).add ((hs0 h.bA22).mul hρ2 h.bdZ))).sub
    (hs0 h.bEhZ)).le ?_
  have hkA : (c.bnZu + c.XZb * c.bDu) * c.sD + (c.bnZz + c.XZb * c.bDz) * c.sD ≤ c.kA :=
    le_max_right _ _
  have h1 := h.sq_le
  have h2 := h.e_le
  have hδ := h.hδ
  unfold SC.cL
  have hK : 0 ≤ c.cK * e / δ ^ 2 := by positivity
  calc c.kRem * e ^ 2 / δ ^ 3 +
        ((c.bnZu + c.XZb * c.bDu) * c.sD * (c.cK * e / δ ^ 2) +
          (c.bnZz + c.XZb * c.bDz) * c.sD * (c.cK * e / δ ^ 2)) + e * c.sD
      = c.kRem * (e ^ 2 / δ ^ 3) +
          ((c.bnZu + c.XZb * c.bDu) * c.sD + (c.bnZz + c.XZb * c.bDz) * c.sD) *
            (c.cK * e / δ ^ 2) + c.kE * e := by unfold SC.kE; ring
    _ ≤ c.kRem * (c.θ * c.δ0 ^ 3 * e / δ ^ 2) + c.kA * (c.cK * e / δ ^ 2) +
          c.kE * (c.δ0 ^ 2 * e / δ ^ 2) := by gcongr
    _ = _ := by ring

/-! ### The new error -/

/-- The residual variables are bounded by `avec` on the narrower strip. -/
theorem bxK : ∀ i, Bd (c.ρ - 2 * δ) (xK ι u z i) (c.avec i) := by
  have hs0 : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith [h.hδ])
  have hc : Real.exp (c.ρ - 2 * δ) ≤ c.ac :=
    (Real.exp_le_exp.2 (by linarith [h.hδ])).trans h.hac
  intro i
  fin_cases i
  · exact hs0 h.hu
  · exact hs0 h.hz
  · exact (Bd_cS _).le hc
  · exact (Bd_sS _).le hc
  · exact hs0 h.hLR
  · exact hs0 h.hLz

/-- The perturbation is bounded by `(e/δ²) mvec`. -/
theorem bhDel : ∀ i, Bd (c.ρ - 2 * δ) (hDel ι (F.dRs ι u z) (F.dZs ι u z) i)
    (((e / δ ^ 2) • c.mvec) i) := by
  have he := h.e_nonneg
  have hδ := h.hδ
  have hed : 0 ≤ e / δ ^ 2 := by positivity
  have hK : c.cK * e / δ ^ 2 ≤ (e / δ ^ 2) * c.cKb := by
    rw [mul_div_assoc, mul_comm]; exact mul_le_mul_of_nonneg_left h.hcb.1 hed
  have hL : c.cL * e / δ ^ 2 ≤ (e / δ ^ 2) * c.cLb := by
    rw [mul_div_assoc, mul_comm]; exact mul_le_mul_of_nonneg_left h.hcb.2 hed
  intro i
  fin_cases i
  · exact h.bdR.le (by simpa [SC.mvec] using hK)
  · exact h.bdZ.le (by simpa [SC.mvec] using hK)
  · exact (Bd_zero _).le (by simp [SC.mvec])
  · exact (Bd_zero _).le (by simp [SC.mvec])
  · exact h.bLdR.le (by simpa [SC.mvec] using hL)
  · exact h.bLdZ.le (by simpa [SC.mvec] using hL)

/-- `avec ≥ 0`. -/
theorem avec_nonneg : ∀ i, 0 ≤ c.avec i := fun i => (h.bxK i).nonneg

/-- `mvec ≥ 0`. -/
theorem mvec_nonneg : ∀ i, 0 ≤ c.mvec i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, cK, -⟩ := h.derived_nonneg
  have hL : 0 ≤ c.cL := by
    have := h.bLdR.nonneg; have he := h.e_nonneg; have hδ := h.hδ
    by_cases he0 : e = 0
    · unfold SC.cL
      obtain ⟨kE, -, -, -, -, -, -, -, -, -, -, -, -, kRem⟩ := h.derived_nonneg
      have hkA : 0 ≤ c.kA := le_trans (by
        have := h.bA11.nonneg; have := h.bA12.nonneg; positivity) (le_max_left _ _)
      have := h.base_nonneg
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, h19⟩ := this
      positivity
    · have hpos : 0 < e / δ ^ 2 := by
        have := lt_of_le_of_ne he (Ne.symm he0); positivity
      have : 0 ≤ c.cL * (e / δ ^ 2) := by rw [← mul_div_assoc]; exact this
      exact nonneg_of_mul_nonneg_left this hpos
  have hKb : 0 ≤ c.cKb := cK.trans h.hcb.1
  have hLb : 0 ≤ c.cLb := hL.trans h.hcb.2
  intro i
  fin_cases i <;> simp [SC.mvec, hKb, hLb]

/-- **Taylor remainder** `‖Q_R‖_{ρ−2δ} ≤ C₂ e²/δ⁴`. -/
theorem bQR : Bd (c.ρ - 2 * δ) (F.QR ι u z (F.dRs ι u z) (F.dZs ι u z)) (c.C2 * e ^ 2 / δ ^ 4) := by
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have he := h.e_nonneg
  have hδ := h.hδ
  have ht : 0 ≤ e / δ ^ 2 := by positivity
  have htT : e / δ ^ 2 ≤ c.Tq := by
    unfold SC.Tq
    have h2 : δ ^ 2 ≤ c.δ0 ^ 2 := pow_le_pow_left₀ hδ.le h.hδ0 2
    have hθ := h.base_nonneg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [div_le_iff₀ (by positivity)]
    calc e ≤ c.θ * δ ^ 4 := h.heθ
      _ = c.θ * δ ^ 2 * δ ^ 2 := by ring
      _ ≤ c.θ * c.δ0 ^ 2 * δ ^ 2 := by gcongr
  have hnn : ∀ i, 0 ≤ (c.avec + (e / δ ^ 2) • c.mvec) i := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h.avec_nonneg i; have := h.mvec_nonneg i; positivity
  have hle : ∀ i, (c.avec + (e / δ ^ 2) • c.mvec) i ≤ (c.avec + c.Tq • c.mvec) i := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h.mvec_nonneg i; nlinarith
  have hT := PolyExprS.Bd.taylorS hρ2 h.bxK h.bhDel (PolyExprS.Valid.mono hnn hle h.hvR)
  refine hT.le ?_
  rw [majD2_smulS]
  have hmono := PolyExprS.majD2_mono hnn h.mvec_nonneg hle (fun i => le_rfl) h.hvR
  have hC := h.hC2R
  calc (e / δ ^ 2) ^ 2 * PolyExprS.majD2 (c.avec + (e / δ ^ 2) • c.mvec) c.mvec F.resRp / 2
      ≤ (e / δ ^ 2) ^ 2 * (PolyExprS.majD2 (c.avec + c.Tq • c.mvec) c.mvec F.resRp / 2) := by
        rw [mul_div_assoc]; gcongr
    _ ≤ (e / δ ^ 2) ^ 2 * c.C2 := by gcongr
    _ = c.C2 * e ^ 2 / δ ^ 4 := by ring

/-- **Taylor remainder** `‖Q_z‖_{ρ−2δ} ≤ C₂ e²/δ⁴`. -/
theorem bQZ : Bd (c.ρ - 2 * δ) (F.QZ ι u z (F.dRs ι u z) (F.dZs ι u z)) (c.C2 * e ^ 2 / δ ^ 4) := by
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have he := h.e_nonneg
  have hδ := h.hδ
  have ht : 0 ≤ e / δ ^ 2 := by positivity
  have htT : e / δ ^ 2 ≤ c.Tq := by
    unfold SC.Tq
    have h2 : δ ^ 2 ≤ c.δ0 ^ 2 := pow_le_pow_left₀ hδ.le h.hδ0 2
    have hθ := h.base_nonneg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [div_le_iff₀ (by positivity)]
    calc e ≤ c.θ * δ ^ 4 := h.heθ
      _ = c.θ * δ ^ 2 * δ ^ 2 := by ring
      _ ≤ c.θ * c.δ0 ^ 2 * δ ^ 2 := by gcongr
  have hnn : ∀ i, 0 ≤ (c.avec + (e / δ ^ 2) • c.mvec) i := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h.avec_nonneg i; have := h.mvec_nonneg i; positivity
  have hle : ∀ i, (c.avec + (e / δ ^ 2) • c.mvec) i ≤ (c.avec + c.Tq • c.mvec) i := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h.mvec_nonneg i; nlinarith
  have hT := PolyExprS.Bd.taylorS hρ2 h.bxK h.bhDel (PolyExprS.Valid.mono hnn hle h.hvZ)
  refine hT.le ?_
  rw [majD2_smulS]
  have hmono := PolyExprS.majD2_mono hnn h.mvec_nonneg hle (fun i => le_rfl) h.hvZ
  have hC := h.hC2Z
  calc (e / δ ^ 2) ^ 2 * PolyExprS.majD2 (c.avec + (e / δ ^ 2) • c.mvec) c.mvec F.resZp / 2
      ≤ (e / δ ^ 2) ^ 2 * (PolyExprS.majD2 (c.avec + c.Tq • c.mvec) c.mvec F.resZp / 2) := by
        rw [mul_div_assoc]; gcongr
    _ ≤ (e / δ ^ 2) ^ 2 * c.C2 := by gcongr
    _ = c.C2 * e ^ 2 / δ ^ 4 := by ring

/-- **The new error** (`R`): `‖E_R(K + ΔK)‖_{ρ−2δ} ≤ κ e²/δ⁴`. -/
theorem bER' :
    Bd (c.ρ - 2 * δ) (F.resR ι (u + F.dRs ι u z) (z + F.dZs ι u z)) (c.kap * e ^ 2 / δ ^ 4) := by
  have hana1 := h.frame.ana_dRs h.dio h.γ_pos
  have hana2 := h.frame.ana_dZs h.dio h.γ_pos
  rw [h.frame.newton_error_R hana1 hana2]
  have hres := h.LdR_eq
  have e1 : Lt ι (F.dRs ι u z) - (F.A11 u z * F.dRs ι u z + F.A12 u z * F.dZs ι u z) + F.EhR ι u z =
      F.Scoef ι u z * F.xi2 ι u z * F.NR u z + F.xi1 ι u z * dTh (F.EhR ι u z) := by
    rw [hres]; ring
  rw [e1]
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have hs0 : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith [h.hδ])
  refine ((((hs0 h.hbD).mul hρ2 h.bRemR).add
    ((((hs0 h.hbDu).mul hρ2 h.bdR).add ((hs0 h.hbDz).mul hρ2 h.bdZ)).mul hρ2 (hs0 h.bEhR))).add
    h.bQR).le ?_
  have he := h.e_nonneg
  have hδ := h.hδ
  have hδ0 := h.hδ0
  obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := h.base_nonneg
  obtain ⟨kE, -, -, -, -, -, -, -, -, -, -, cK, -, kRem⟩ := h.derived_nonneg
  unfold SC.kap
  have t1 : c.bD * (c.kRem * e ^ 2 / δ ^ 3) ≤ c.bD * c.kRem * c.δ0 * e ^ 2 / δ ^ 4 := by
    rw [show c.bD * (c.kRem * e ^ 2 / δ ^ 3) = c.bD * c.kRem * e ^ 2 / δ ^ 3 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ c.bD * c.kRem * e ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hδ0 (show 0 ≤ c.bD * c.kRem * e ^ 2 * δ ^ 3 by positivity)]
  have t2 : (c.bDu * (c.cK * e / δ ^ 2) + c.bDz * (c.cK * e / δ ^ 2)) * (e * c.sD) ≤
      (c.bDu + c.bDz) * c.cK * c.kE * c.δ0 ^ 2 * e ^ 2 / δ ^ 4 := by
    have h2 : δ ^ 2 ≤ c.δ0 ^ 2 := pow_le_pow_left₀ hδ.le h.hδ0 2
    have e3 : (c.bDu * (c.cK * e / δ ^ 2) + c.bDz * (c.cK * e / δ ^ 2)) * (e * c.sD) =
        (c.bDu + c.bDz) * c.cK * c.kE * δ ^ 2 * e ^ 2 / δ ^ 4 := by
      unfold SC.kE; field_simp
    rw [e3]; gcongr
  calc c.bD * (c.kRem * e ^ 2 / δ ^ 3) +
        (c.bDu * (c.cK * e / δ ^ 2) + c.bDz * (c.cK * e / δ ^ 2)) * (e * c.sD) +
        c.C2 * e ^ 2 / δ ^ 4
      ≤ c.bD * c.kRem * c.δ0 * e ^ 2 / δ ^ 4 +
          (c.bDu + c.bDz) * c.cK * c.kE * c.δ0 ^ 2 * e ^ 2 / δ ^ 4 + c.C2 * e ^ 2 / δ ^ 4 := by
        gcongr
    _ = _ := by ring

/-- **The new error** (`z`): `‖E_z(K + ΔK)‖_{ρ−2δ} ≤ κ e²/δ⁴`. -/
theorem bEZ' :
    Bd (c.ρ - 2 * δ) (F.resZ ι (u + F.dRs ι u z) (z + F.dZs ι u z)) (c.kap * e ^ 2 / δ ^ 4) := by
  have hana1 := h.frame.ana_dRs h.dio h.γ_pos
  have hana2 := h.frame.ana_dZs h.dio h.γ_pos
  rw [h.frame.newton_error_Z hana1 hana2]
  have hres := h.LdZ_eq
  have e1 : Lt ι (F.dZs ι u z) - (F.A21 u z * F.dRs ι u z + F.A22 u z * F.dZs ι u z) + F.EhZ ι u z =
      F.Scoef ι u z * F.xi2 ι u z * F.NZ u z + F.xi1 ι u z * dTh (F.EhZ ι u z) := by
    rw [hres]; ring
  rw [e1]
  have hρ2 : 0 ≤ c.ρ - 2 * δ := by linarith [h.h3δ, h.hδ]
  have hs0 : ∀ {x : FA} {B : ℝ}, Bd c.ρ x B → Bd (c.ρ - 2 * δ) x B :=
    fun hx => hx.strip (by linarith [h.hδ])
  refine ((((hs0 h.hbD).mul hρ2 h.bRemZ).add
    ((((hs0 h.hbDu).mul hρ2 h.bdR).add ((hs0 h.hbDz).mul hρ2 h.bdZ)).mul hρ2 (hs0 h.bEhZ))).add
    h.bQZ).le ?_
  have he := h.e_nonneg
  have hδ := h.hδ
  have hδ0 := h.hδ0
  obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := h.base_nonneg
  obtain ⟨kE, -, -, -, -, -, -, -, -, -, -, cK, -, kRem⟩ := h.derived_nonneg
  unfold SC.kap
  have t1 : c.bD * (c.kRem * e ^ 2 / δ ^ 3) ≤ c.bD * c.kRem * c.δ0 * e ^ 2 / δ ^ 4 := by
    rw [show c.bD * (c.kRem * e ^ 2 / δ ^ 3) = c.bD * c.kRem * e ^ 2 / δ ^ 3 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ c.bD * c.kRem * e ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hδ0 (show 0 ≤ c.bD * c.kRem * e ^ 2 * δ ^ 3 by positivity)]
  have t2 : (c.bDu * (c.cK * e / δ ^ 2) + c.bDz * (c.cK * e / δ ^ 2)) * (e * c.sD) ≤
      (c.bDu + c.bDz) * c.cK * c.kE * c.δ0 ^ 2 * e ^ 2 / δ ^ 4 := by
    have h2 : δ ^ 2 ≤ c.δ0 ^ 2 := pow_le_pow_left₀ hδ.le h.hδ0 2
    have e3 : (c.bDu * (c.cK * e / δ ^ 2) + c.bDz * (c.cK * e / δ ^ 2)) * (e * c.sD) =
        (c.bDu + c.bDz) * c.cK * c.kE * δ ^ 2 * e ^ 2 / δ ^ 4 := by
      unfold SC.kE; field_simp
    rw [e3]; gcongr
  calc c.bD * (c.kRem * e ^ 2 / δ ^ 3) +
        (c.bDu * (c.cK * e / δ ^ 2) + c.bDz * (c.cK * e / δ ^ 2)) * (e * c.sD) +
        c.C2 * e ^ 2 / δ ^ 4
      ≤ c.bD * c.kRem * c.δ0 * e ^ 2 / δ ^ 4 +
          (c.bDu + c.bDz) * c.cK * c.kE * c.δ0 ^ 2 * e ^ 2 / δ ^ 4 + c.C2 * e ^ 2 / δ ^ 4 := by
        gcongr
    _ = _ := by ring

/-- **One Newton step with explicit estimates (`kam_step`).** Under the step hypotheses `StepH`
(error `e ≤ θ δ⁴`, loss `0 < δ ≤ δ₀`, `3δ ≤ ρ`), the correction `ΔK = (ΔR, Δz)` is analytic and
`‖ΔK‖_{ρ−2δ} ≤ cK e/δ²`, `‖𝓛ΔK‖_{ρ−2δ} ≤ cL e/δ²`, and the new residual satisfies
`‖E(K + ΔK)‖_{ρ−2δ} ≤ κ e²/δ⁴`. -/
theorem kam_step :
    Ana (F.dRs ι u z) ∧ Ana (F.dZs ι u z) ∧
      Bd (c.ρ - 2 * δ) (F.dRs ι u z) (c.cK * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (F.dZs ι u z) (c.cK * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (Lt ι (F.dRs ι u z)) (c.cL * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (Lt ι (F.dZs ι u z)) (c.cL * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (F.resR ι (u + F.dRs ι u z) (z + F.dZs ι u z)) (c.kap * e ^ 2 / δ ^ 4) ∧
      Bd (c.ρ - 2 * δ) (F.resZ ι (u + F.dRs ι u z) (z + F.dZs ι u z)) (c.kap * e ^ 2 / δ ^ 4) :=
  ⟨h.frame.ana_dRs h.dio h.γ_pos, h.frame.ana_dZs h.dio h.γ_pos, h.bdR, h.bdZ, h.bLdR, h.bLdZ,
    h.bER', h.bEZ'⟩

end StepH

/-! ## Reality is preserved -/



namespace FrameHyp

variable {F : FlowFieldS} {ι γ : ℝ} {u z : FA} (H : F.FrameHyp u z) (hur : IsReal u)
  (hzr : IsReal z)
include H hur hzr

/-- Valid real expressions have real values at a real torus. -/
theorem isReal_evalB {e : PolyExprS ℂ (Fin 6)} (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e)
    (hre : PolyExprS.RealConstsS e) : IsReal (PolyExprS.eval (xB u z) e) := by
  obtain ⟨ρ, hρ, a, hx, hv⟩ := H.good
  exact PolyExprS.IsReal.evalS hρ.le hx (isReal_xB hur hzr) (he a hv) hre

/-- Partial derivatives of valid real expressions are real at a real torus. -/
theorem isReal_pdB (i : Fin 6) {e : PolyExprS ℂ (Fin 6)}
    (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e) (hre : PolyExprS.RealConstsS e) :
    IsReal (pdS (xB u z) i e) := by
  obtain ⟨ρ, hρ, a, hx, hv⟩ := H.good
  refine PolyExprS.IsReal.derivS hρ.le hx (isReal_xB hur hzr) (fun j => ?_) (he a hv) hre
  by_cases hj : j = i
  · subst hj; simpa using IsReal.one
  · simp only [Pi.single_apply, hj, ite_false]; exact map_zero cjHom

/-- `D` is real. -/
theorem isReal_D : IsReal (F.Dof u z) := H.isReal_evalB hur hzr (fun _ h => h.1) F.real_Dp
/-- `n_R` is real. -/
theorem isReal_nR : IsReal (F.nR u z) := H.isReal_evalB hur hzr (fun _ h => h.2.1) F.real_nRp
/-- `n_z` is real. -/
theorem isReal_nZ : IsReal (F.nZ u z) := H.isReal_evalB hur hzr (fun _ h => h.2.2.1) F.real_nZp
/-- `D⁻¹` is real. -/
theorem isReal_Di : IsReal (F.Di u z) := (H.isReal_D hur hzr).inverse H.unit_D
omit hzr in
/-- `R⁻¹` is real. -/
theorem isReal_Ri : IsReal (Ri u) := (IsReal.one.add hur).inverse H.unit_R
omit H in
/-- `W₀` is real. -/
theorem isReal_W : IsReal (W0of u z) :=
  ((isReal_dTh hur).mul hzr).sub ((isReal_dTh hzr).mul hur)
/-- `W₀⁻¹` is real. -/
theorem isReal_Wi : IsReal (Wi u z) := (isReal_W hur hzr).inverse H.unit_W
/-- `Ê_R` is real. -/
theorem isReal_EhR : IsReal (F.EhR ι u z) := by
  rw [EhR, F.resR_eq]
  exact (((H.isReal_D hur hzr).mul (isReal_Lt hur ι)).sub (H.isReal_nR hur hzr)).mul
    (H.isReal_Di hur hzr)
/-- `Ê_z` is real. -/
theorem isReal_EhZ : IsReal (F.EhZ ι u z) := by
  rw [EhZ, F.resZ_eq]
  exact (((H.isReal_D hur hzr).mul (isReal_Lt hzr ι)).sub (H.isReal_nZ hur hzr)).mul
    (H.isReal_Di hur hzr)
/-- The torsion numerator is real. -/
theorem isReal_Pof : IsReal (F.Pof u z) := by
  have hD := H.isReal_D hur hzr
  have hnR := H.isReal_nR hur hzr
  have hnZ := H.isReal_nZ hur hzr
  have p := fun (i : Fin 6) => H.isReal_pdB hur hzr i (e := F.Dp) (fun _ h => h.1) F.real_Dp
  have q := fun (i : Fin 6) => H.isReal_pdB hur hzr i (e := F.nRp) (fun _ h => h.2.1) F.real_nRp
  have r := fun (i : Fin 6) => H.isReal_pdB hur hzr i (e := F.nZp) (fun _ h => h.2.2.1)
    F.real_nZp
  unfold FlowFieldS.Pof
  exact (((hnR.mul hD).sub (hD.mul (((q 0).mul hur).add ((q 1).mul hzr)))).add
      (hnR.mul (((p 0).mul hur).add ((p 1).mul hzr)))).mul hzr |>.sub
    ((((hnZ.mul hD).sub (hD.mul (((r 0).mul hur).add ((r 1).mul hzr)))).add
      (hnZ.mul (((p 0).mul hur).add ((p 1).mul hzr)))).mul hur)
/-- `η₁` is real. -/
theorem isReal_eta1 : IsReal (F.eta1 ι u z) :=
  (H.isReal_Wi hur hzr).mul
    ((hzr.mul (H.isReal_EhR hur hzr)).sub (hur.mul (H.isReal_EhZ hur hzr)))
/-- `η₂` is real. -/
theorem isReal_eta2 : IsReal (F.eta2 ι u z) :=
  ((H.isReal_D hur hzr).mul ((H.isReal_Ri hur).pow 3)).mul
    (((isReal_dTh hur).mul (H.isReal_EhZ hur hzr)).sub
      ((isReal_dTh hzr).mul (H.isReal_EhR hur hzr)))
/-- `T` is real. -/
theorem isReal_Tor : IsReal (F.Tor ι u z) :=
  (((((IsReal.one.add hur).pow 3).mul ((H.isReal_Di hur hzr).pow 3)).mul
    ((H.isReal_Wi hur hzr).pow 2)).mul (H.isReal_Pof hur hzr)).add
    (((((IsReal.one.add hur).pow 3).mul (H.isReal_Di hur hzr)).mul
      ((H.isReal_Wi hur hzr).pow 2)).mul
      (((H.isReal_EhR hur hzr).mul hzr).sub ((H.isReal_EhZ hur hzr).mul hur)))

/-- `ξ₂⁰` is real. -/
theorem isReal_xi20 : IsReal (F.xi20 ι u z) := by
  have := ((H.isReal_eta2 (ι := ι) hur hzr).coh (ι / 2)).smul (-(1 / 2))
  rw [xi20]; simpa using this

/-- `c̄` is real. -/
theorem conj_cbar : (starRingEnd ℂ) (F.cbar ι u z) = F.cbar ι u z := by
  rw [cbar, map_div₀, map_neg, ((H.isReal_eta1 hur hzr).add
    ((H.isReal_Tor hur hzr).mul (H.isReal_xi20 hur hzr))).conj_avg,
    (H.isReal_Tor hur hzr).conj_avg]

/-- `ξ₂` is real. -/
theorem isReal_xi2 : IsReal (F.xi2 ι u z) := by
  have hc : F.cbar ι u z = ((F.cbar ι u z).re : ℂ) := by
    apply Complex.ext
    · simp
    · have := congrArg Complex.im (H.conj_cbar (ι := ι) hur hzr)
      simp at this; simp; linarith
  rw [xi2, hc]
  exact (H.isReal_xi20 hur hzr).add (IsReal.algebraMap _)

/-- `ξ₁` is real. -/
theorem isReal_xi1 : IsReal (F.xi1 ι u z) := by
  have := (((H.isReal_eta1 (ι := ι) hur hzr).add ((H.isReal_Tor (ι := ι) hur hzr).mul
    (H.isReal_xi2 (ι := ι) hur hzr))).coh (ι / 2)).smul (-(1 / 2))
  rw [xi1]; simpa using this

/-- **The correction is real.** -/
theorem isReal_dRs : IsReal (F.dRs ι u z) ∧ IsReal (F.dZs ι u z) := by
  have hh : IsReal (F.hN u z) :=
    (((IsReal.one.add hur).pow 3).mul (H.isReal_Di hur hzr)).mul (H.isReal_Wi hur hzr)
  exact ⟨((H.isReal_xi1 hur hzr).mul (isReal_dTh hur)).add
      ((H.isReal_xi2 hur hzr).mul (hh.mul hur)),
    ((H.isReal_xi1 hur hzr).mul (isReal_dTh hzr)).add ((H.isReal_xi2 hur hzr).mul (hh.mul hzr))⟩

end FrameHyp

end FlowFieldS

end PlasmaLean.Design.KamNewton
