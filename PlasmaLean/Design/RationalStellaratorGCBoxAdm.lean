/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCBoxPert
public import PlasmaLean.Certificates.KernelFact

/-!
# Residual and admissibility over the box of gyro-lengths and pitch parameters

For every gyro-length `ρ` with `|ρ − 1/256| ≤ 2⁻⁸⁶` and every pitch parameter `λ = lamF c ∈
[0, 1/16]`, the **same** approximate torus `K(λ)` (the family centre of the pitch-angle family
`Design/RationalStellaratorGCMu*`) satisfies the hypotheses of the KAM theorem for the field
`gcFlowMu ρ λ` with the **same** constants `cM`:

* the residual (`boxResR`, `boxResZ`): `‖D̃ 𝓛K − ñ‖_{r_A} ≤ e₀ = 3.4 × 10⁻²¹`; the certified
  residual at `ρ₀ = 1/256` is `2.03 × 10⁻²¹` (`R`) and `3.31 × 10⁻²¹` (`z`), and the field
  changes by `(ρ − ρ₀)·F Y` (`resR_gcFlowMu_sub`), at most `2⁻⁸⁶ · 1131 ≈ 1.5 × 10⁻²³`;
* **admissibility** (`boxAdm`) of every torus `μ = 10⁻¹¹`-close to `K(λ)`: the bounds of the
  certified chain at `ρ₀` have slack, and the field quantities `D̃, ñ` and their derivatives move
  by at most `2⁻⁸⁶ · 30768`; the inverse `D̃⁻¹`, the torsion numerator (`FlowFieldS.Pof`,
  propagated with `DBd`) and the twist are re-bounded with the perturbation.

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `boxResR_center`: at `ρ = 1/256` the residual bound is that of the pitch-angle family.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-- A component moved by `(ρ − 1/256) Y` with `‖Y‖ ≤ M`. -/
theorem dbd_of_sub {r : ℝ} (hr : 0 ≤ r) {ρ : ℝ} (hρ : |ρ - 1 / 256| ≤ dRhoB) {X X' Y : FA}
    {B M : ℝ} (hX : Bd r X B) (he : X' - X = dA ρ * Y) (hY : Bd r Y M) :
    DBd r X X' B (dRhoB * M) := by
  refine ⟨hX, ?_⟩
  rw [he]
  exact ((Bd_dA r ρ).mul hr hY).le (mul_le_mul_of_nonneg_right hρ hY.nonneg)

/-- The torus variables `xB u z` are bounded by `avM` when `u, z` are. -/
theorem xB_bd_avM {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {u z : FA}
    (tu : Bd r u auM) (tz : Bd r z azM) : ∀ i, Bd r (xB u z i) (avM i) := by
  have hcq : Real.exp r ≤ acG := by push_cast at hq; rw [acG]; linarith
  intro i
  fin_cases i
  · exact tu
  · exact tz
  · exact (Bd_cS r).le hcq
  · exact (Bd_sS r).le hcq
  · exact Bd_zero r
  · exact Bd_zero r

/-! ## The residual over the box -/

section Res

variable {ρ : ℝ} (hρ : |ρ - 1 / 256| ≤ dRhoB) {c : ℂ} (hc : ‖c‖ = 1)
include hρ hc

omit hρ in
/-- The correction bounds at the family torus `K(λ)` on the strip `r_A`. -/
theorem corr_at_K :
    Bd KamTorusA.rA (PolyExprS.eval (xB (xHM c 4) (xHM c 5)) (eYDF (lamF c))) 177 ∧
    Bd KamTorusA.rA (PolyExprS.eval (xB (xHM c 4) (xHM c 5)) (eYRF (lamF c))) 91 ∧
    Bd KamTorusA.rA (PolyExprS.eval (xB (xHM c 4) (xHM c 5)) (eYZF (lamF c))) 1113 := by
  have hx := xB_bd_avM exp_rA_le' ((Bd_uM hc).le (by rw [auM, μM]; norm_num))
    ((Bd_zM hc).le (by rw [azM, μM]; norm_num))
  obtain ⟨h1, -, -, h4, -, -, h7, -, -⟩ := Bd_corr rA_nonneg' avM_le.1 avM_le.2 hx
    (abs_lamF_le hc)
  exact ⟨h1, h4, h7⟩

/-- **The residual of the family torus over the box** (`R`-component): `≤ e₀`. -/
theorem boxResR :
    Bd KamTorusA.rA ((gcFlowMu ρ (lamF c)).resR KamTorusA.iota (xHM c 4) (xHM c 5)) e0M := by
  have h := normHM_resR rA_nonneg' exp_rA_le' hc
  rw [eval_trHMN_resR c hc] at h
  have hF := Bd_inv_pow96 h
  obtain ⟨hD, hR, -⟩ := corr_at_K hc
  have hd := dbd_of_sub rA_nonneg' hρ hF (resR_gcFlowMu_sub ρ (lamF c) KamTorusA.iota _ _)
    ((hD.mul rA_nonneg' (Bd_Lt_uM hc)).sub hR)
  refine hd.bd'.le ?_
  norm_num [dRhoB, e0M]

/-- **The residual of the family torus over the box** (`z`-component): `≤ e₀`. -/
theorem boxResZ :
    Bd KamTorusA.rA ((gcFlowMu ρ (lamF c)).resZ KamTorusA.iota (xHM c 4) (xHM c 5)) e0M := by
  have h := normHM_resZ rA_nonneg' exp_rA_le' hc
  rw [eval_trHMN_resZ c hc] at h
  have hF := Bd_inv_pow96 h
  obtain ⟨hD, -, hZ⟩ := corr_at_K hc
  have hd := dbd_of_sub rA_nonneg' hρ hF (resZ_gcFlowMu_sub ρ (lamF c) KamTorusA.iota _ _)
    ((hD.mul rA_nonneg' (Bd_Lt_zM hc)).sub hZ)
  refine hd.bd'.le ?_
  norm_num [dRhoB, e0M]

end Res

/-- **Sanity**: at the centre `ρ = 1/256` the box residual is the family residual. -/
theorem boxResR_center {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA ((gcFlowMu (1 / 256) (lamF c)).resR KamTorusA.iota (xHM c 4) (xHM c 5))
      e0M :=
  boxResR (by rw [sub_self, abs_zero]; norm_num [dRhoB]) hc

/-! ## Admissibility over the box -/

section Adm

variable {ρ : ℝ} (hρ : |ρ - 1 / 256| ≤ dRhoB) {r : ℝ} (hr0 : 0 < r)
  (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
  {u z : FA} (hU : Bd r (u - xLM c 4) (ELM 4)) (hZ : Bd r (z - xLM c 5) (ELM 5))
  (hA : Bd r (dTh u - xLM c 6) (ELM 6)) (hB : Bd r (dTh z - xLM c 7) (ELM 7))
  (tu : Bd r u auM) (tz : Bd r z azM)
include hρ hr0 hq hc hU hZ hA hB tu tz

/-- The nine field components (`D̃, ∂_uD̃, ∂_zD̃, ñ_R, …`) of `gcFlowMu ρ λ` against those of
`gcFlowMu (1/256) λ`, with the bounds of the certified chain at `1/256`. -/
theorem box_components :
    DBd r (PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcDM ρ (lamF c))) ((BLM 154 + ELM 154 : ℚ) : ℝ)
      (dRhoB * 177) ∧
    DBd r (pdS (xB u z) 0 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcDM ρ (lamF c)))
      ((BLM 160 + ELM 160 : ℚ) : ℝ) (dRhoB * 4997) ∧
    DBd r (pdS (xB u z) 1 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcDM ρ (lamF c)))
      ((BLM 162 + ELM 162 : ℚ) : ℝ) (dRhoB * 1620) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNRM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNRM ρ (lamF c))) ((BLM 156 + ELM 156 : ℚ) : ℝ)
      (dRhoB * 91) ∧
    DBd r (pdS (xB u z) 0 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNRM ρ (lamF c)))
      ((BLM 164 + ELM 164 : ℚ) : ℝ) (dRhoB * 2623) ∧
    DBd r (pdS (xB u z) 1 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNRM ρ (lamF c)))
      ((BLM 166 + ELM 166 : ℚ) : ℝ) (dRhoB * 861) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNZM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNZM ρ (lamF c))) ((BLM 158 + ELM 158 : ℚ) : ℝ)
      (dRhoB * 1113) ∧
    DBd r (pdS (xB u z) 0 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNZM ρ (lamF c)))
      ((BLM 168 + ELM 168 : ℚ) : ℝ) (dRhoB * 30768) ∧
    DBd r (pdS (xB u z) 1 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNZM ρ (lamF c)))
      ((BLM 170 + ELM 170 : ℚ) : ℝ) (dRhoB * 6181) := by
  have hr := hr0.le
  have v := valLM_le hr hq hc hU hZ hA hB
  have hx := xB_bd_avM hq tu tz
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := Bd_corr hr avM_le.1 avM_le.2 hx
    (abs_lamF_le hc)
  refine ⟨dbd_of_sub hr hρ (v 154 (by norm_num)) (eval_gcDM_sub _ _ _) m1,
    dbd_of_sub hr hρ (v 160 (by norm_num)) (pdS_gcDM_sub _ _ _ _) m2,
    dbd_of_sub hr hρ (v 162 (by norm_num)) (pdS_gcDM_sub _ _ _ _) m3,
    dbd_of_sub hr hρ (v 156 (by norm_num)) (eval_gcNRM_sub _ _ _) m4,
    dbd_of_sub hr hρ (v 164 (by norm_num)) (pdS_gcNRM_sub _ _ _ _) m5,
    dbd_of_sub hr hρ (v 166 (by norm_num)) (pdS_gcNRM_sub _ _ _ _) m6,
    dbd_of_sub hr hρ (v 158 (by norm_num)) (eval_gcNZM_sub _ _ _) m7,
    dbd_of_sub hr hρ (v 168 (by norm_num)) (pdS_gcNZM_sub _ _ _ _) m8,
    dbd_of_sub hr hρ (v 170 (by norm_num)) (pdS_gcNZM_sub _ _ _ _) m9⟩

/-- The nine components with rounded rational bounds (`cM`-sized). -/
theorem box_components' :
    DBd r (PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcDM ρ (lamF c))) (13 / 10) (1 / 2 ^ 70) ∧
    DBd r (pdS (xB u z) 0 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcDM ρ (lamF c)))
      (23 / 10) (1 / 2 ^ 70) ∧
    DBd r (pdS (xB u z) 1 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcDM ρ (lamF c)))
      (21 / 100) (1 / 2 ^ 70) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNRM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNRM ρ (lamF c))) (11 / 100) (1 / 2 ^ 70) ∧
    DBd r (pdS (xB u z) 0 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNRM ρ (lamF c)))
      (95 / 100) (1 / 2 ^ 70) ∧
    DBd r (pdS (xB u z) 1 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNRM ρ (lamF c)))
      (75 / 100) (1 / 2 ^ 70) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNZM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNZM ρ (lamF c))) (11 / 100) (1 / 2 ^ 70) ∧
    DBd r (pdS (xB u z) 0 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNZM ρ (lamF c)))
      (87 / 100) (1 / 2 ^ 70) ∧
    DBd r (pdS (xB u z) 1 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNZM ρ (lamF c)))
      (82 / 100) (1 / 2 ^ 70) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
    box_components hρ hr0 hq hc hU hZ hA hB tu tz
  have f : ∀ {i : ℕ} {s : ℚ}, BLM i + ELM i ≤ s → ((BLM i + ELM i : ℚ) : ℝ) ≤ (s : ℝ) :=
    fun h => qle h
  have g : ∀ {M : ℝ}, M ≤ 30768 → dRhoB * M ≤ 1 / 2 ^ 70 := fun h => by
    rw [dRhoB]; nlinarith
  refine ⟨d1.le ?_ (g (by norm_num)), d2.le ?_ (g (by norm_num)), d3.le ?_ (g (by norm_num)),
    d4.le ?_ (g (by norm_num)), d5.le ?_ (g (by norm_num)), d6.le ?_ (g (by norm_num)),
    d7.le ?_ (g (by norm_num)), d8.le ?_ (g le_rfl), d9.le ?_ (g (by norm_num))⟩
  · exact (f (i := 154) (s := 13 / 10) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 160) (s := 23 / 10) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 162) (s := 21 / 100) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 156) (s := 11 / 100) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 164) (s := 95 / 100) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 166) (s := 75 / 100) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 158) (s := 11 / 100) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 168) (s := 87 / 100) (by kernel_fact)).trans (by norm_num)
  · exact (f (i := 170) (s := 82 / 100) (by kernel_fact)).trans (by norm_num)

/-- **The torsion numerator over the box**: `‖P(ρ) − P(1/256)‖ ≤ 2⁻⁶⁵`, `‖P(1/256)‖ ≤ 1`. -/
theorem box_Pof :
    DBd r ((gcFlowMu (1 / 256) (lamF c)).Pof u z) ((gcFlowMu ρ (lamF c)).Pof u z) 1
      (1 / 2 ^ 65) := by
  have hr := hr0.le
  obtain ⟨dD, dDu, dDz, dR, dRu, dRz, dZ, dZu, dZz⟩ :=
    box_components' hρ hr0 hq hc hU hZ hA hB tu tz
  have hu := DBd.of_eq tu
  have hz := DBd.of_eq tz
  have hP := (((dR.mul hr dD).sub (dD.mul hr ((dRu.mul hr hu).add (dRz.mul hr hz)))).add
      (dR.mul hr ((dDu.mul hr hu).add (dDz.mul hr hz)))).mul hr hz |>.sub
    ((((dZ.mul hr dD).sub (dD.mul hr ((dZu.mul hr hu).add (dZz.mul hr hz)))).add
      (dZ.mul hr ((dDu.mul hr hu).add (dDz.mul hr hz)))).mul hr hu)
  exact hP.le (by norm_num [auM, azM, μM]) (by norm_num [auM, azM, μM])

/-- `D̃` over the box: `‖D̃(ρ) − d₀‖ ≤ 0.33035`. -/
theorem box_Ddev : Bd r ((gcFlowMu ρ (lamF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ))
    (743900000000000 / 2 ^ 51 + 1 / 2 ^ 70) := by
  have h := Bd_DdevM hr0.le hq hc hU hZ hA hB
  obtain ⟨dD, -⟩ := box_components' hρ hr0 hq hc hU hZ hA hB tu tz
  have e : (gcFlowMu ρ (lamF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ) =
      ((gcFlowMu (1 / 256) (lamF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ)) +
        (PolyExprS.eval (xB u z) (gcDM ρ (lamF c)) -
          PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c))) := by
    simp only [FlowFieldS.Dof, gcFlowMu]; ring
  rw [e]; exact h.add dD.2

/-- **`D̃(ρ)` is invertible**, `‖D̃(ρ)⁻¹‖ ≤ sDM`. -/
theorem box_Di : IsUnit ((gcFlowMu ρ (lamF c)).Dof u z) ∧
    Bd r (Ring.inverse ((gcFlowMu ρ (lamF c)).Dof u z)) sDM := by
  have h := box_Ddev hρ hr0 hq hc hU hZ hA hB tu tz
  have hn : ‖((d0G : ℝ) : ℂ)‖ = d0G := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num [d0G])]
  obtain ⟨hu, hb⟩ := Bd.inverse hr0.le h (by rw [hn]; norm_num [d0G])
  exact ⟨hu, hb.le (by rw [hn]; norm_num [d0G, sDM])⟩

/-- **Torsion and twist over the box**: `‖T₀(ρ)‖ ≤ tTM`, `|⟨T₀(ρ)⟩| ≥ τM`. -/
theorem box_T : Bd r ((gcFlowMu ρ (lamF c)).Talg u z) tTM ∧
    τM ≤ ‖avg ((gcFlowMu ρ (lamF c)).Talg u z)‖ := by
  have hr := hr0.le
  set q := xLM c 174 with hq_def
  have hqb : Bd r q 28660 := by
    have h := valLM_le hr hq hc hU hZ hA hB 174 (by norm_num)
    exact h.le ((qle (show BLM 174 + ELM 174 ≤ 28660 by kernel_fact)).trans (by norm_num))
  have hWb : Bd r (W0of u z) (13 / 1000) := by
    have h := valLM_le hr hq hc hU hZ hA hB 108 (by norm_num)
    exact h.le ((qle (show BLM 108 + ELM 108 ≤ 13 / 1000 by kernel_fact)).trans
      (by norm_num))
  obtain ⟨dD, -⟩ := box_components' hρ hr0 hq hc hU hZ hA hB tu tz
  -- the factor `F = D̃³ W₀²`
  have hF3 := ((dD.mul hr dD).mul hr dD).mul hr (DBd.of_eq (hWb.pow hr 2))
  have e3 : ∀ a w : FA, a * a * a * w ^ 2 = a ^ 3 * w ^ 2 := fun a w => by ring
  have hdF : Bd r ((gcFlowMu ρ (lamF c)).Dof u z ^ 3 * W0of u z ^ 2 -
      PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)) ^ 3 * W0of u z ^ 2) (1 / 2 ^ 60) := by
    have h2 := hF3.2
    rw [e3, e3] at h2
    exact h2.le (by norm_num)
  set F := (gcFlowMu ρ (lamF c)).Dof u z ^ 3 * W0of u z ^ 2 with hF
  have hX : Bd r (q * F - algebraMap ℂ FA 1) ((313 / 25000000 + 28660 / 2 ^ 60 : ℝ)) := by
    rw [map_one]
    have h0 := Bd_XtorM hr hq hc hU hZ hA hB
    have h1 := h0.add (hqb.mul hr hdF)
    have e : q * F - 1 = xLM c 174 * (PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)) ^ 3 *
        W0of u z ^ 2) - 1 + q * (F - PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)) ^ 3 *
          W0of u z ^ 2) := by rw [hq_def]; ring
    rw [e]
    exact h1.le (by norm_num)
  obtain ⟨hUq, hInv⟩ := Bd.inverse hr hX (by rw [norm_one]; norm_num)
  rw [norm_one] at hInv
  have hXe : Bd r (q * F - 1) ((313 / 25000000 + 28660 / 2 ^ 60 : ℝ)) := by rwa [map_one] at hX
  -- the numerator `Y = (1 + u)³ P q`
  have hu3 : Bd r ((1 + u) ^ 3) ((1 + auM) ^ 3) := ((Bd_one r).add tu).pow hr 3
  have hYd := ((DBd.of_eq hu3).mul hr (box_Pof hρ hr0 hq hc hU hZ hA hB tu tz)).mul hr
    (DBd.of_eq hqb)
  set Y := (1 + u) ^ 3 * (gcFlowMu ρ (lamF c)).Pof u z * q with hY_def
  have hY0e : XLM c u z 175 = (1 + u) ^ 3 * (gcFlowMu (1 / 256) (lamF c)).Pof u z * q := rfl
  have hdY : Bd r (Y - XLM c u z 175) (1 / 2 ^ 40) := by
    rw [hY0e]; exact hYd.2.le (by norm_num [auM, μM])
  have hY0 := valLM_le hr hq hc hU hZ hA hB 175 (by norm_num)
  have hY0c := (ballLM_all hr hq hc hU hZ hA hB) 175 (by norm_num)
  have hYb : Bd r Y (((BLM 175 + ELM 175 : ℚ) : ℝ) + 1 / 2 ^ 40) := by
    have := hY0.add hdY; rwa [add_sub_cancel] at this
  have hYc : Bd r (Y - xLM c 175) (((ELM 175 : ℚ) : ℝ) + 1 / 2 ^ 40) := by
    have := hY0c.add hdY
    rwa [show XLM c u z 175 - xLM c 175 + (Y - XLM c u z 175) = Y - xLM c 175 by ring] at this
  obtain ⟨hDu, -⟩ := box_Di hρ hr0 hq hc hU hZ hA hB tu tz
  obtain ⟨hWu, -⟩ := adm_Wi_M hr0 hq hc hU hZ hA hB
  have hrep : (gcFlowMu ρ (lamF c)).Talg u z = Y * Ring.inverse (q * F) := by
    refine ext_eval fun θ ψ => ?_
    have hD := eval_ne_zero_of_unit hDu θ ψ
    have hW := eval_ne_zero_of_unit hWu θ ψ
    have hQ := eval_ne_zero_of_unit hUq θ ψ
    rw [eval_mul, eval_inverse hUq, hY_def]
    rw [hF] at hQ ⊢
    simp only [FlowFieldS.Talg, FlowFieldS.Di, Wi, eval_mul, eval_pow', eval_inverse hDu,
      eval_inverse hWu, eval_add', eval_one] at hQ ⊢
    have hq0 : eval q θ ψ ≠ 0 := left_ne_zero_of_mul hQ
    field_simp
  have hB1 := qle (show BLM 175 + ELM 175 ≤ 74271 / 2000 by kernel_fact)
  have hE1 := qle (show ELM 175 ≤ 51 / 2000 by kernel_fact)
  push_cast at hB1 hE1
  refine ⟨?_, ?_⟩
  · rw [hrep]
    refine (hYb.mul hr hInv).le ?_
    push_cast
    rw [tTM]
    calc ((BLM 175 : ℝ) + ELM 175 + 1 / 2 ^ 40) * (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 60)))
        ≤ (74271 / 2000 + 1 / 2 ^ 40) * (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 60))) := by
          gcongr
      _ ≤ 4642 / 125 := by norm_num
  · have hI : Ring.inverse (q * F) = 1 - (q * F - 1) * Ring.inverse (q * F) := by
      have := Ring.mul_inverse_cancel _ hUq
      linear_combination this
    have e : (gcFlowMu ρ (lamF c)).Talg u z = Y - Y * (q * F - 1) * Ring.inverse (q * F) := by
      rw [hrep]; nth_rewrite 1 [hI]; ring
    rw [e, avg_sub]
    have h1 : ‖avg (Y * (q * F - 1) * Ring.inverse (q * F))‖ ≤
        (((BLM 175 + ELM 175 : ℚ) : ℝ) + 1 / 2 ^ 40) * (313 / 25000000 + 28660 / 2 ^ 60) *
          (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 60))) :=
      ((hYb.mul hr hXe).mul hr hInv).norm_avg_le hr
    have h2 : ‖avg (Y - xLM c 175)‖ ≤ ((ELM 175 : ℚ) : ℝ) + 1 / 2 ^ 40 := hYc.norm_avg_le hr
    rw [avg_sub] at h2
    have hav := avg_xLM_Y hc
    have h3 : (509184485886532820 / 2 ^ 60 : ℝ) - 15897089878618 / 2 ^ 59 -
        (((ELM 175 : ℚ) : ℝ) + 1 / 2 ^ 40) ≤ ‖avg Y‖ := by
      have h4 := norm_sub_norm_le (((509184485886532820 / 2 ^ 60 : ℝ) : ℂ))
        (((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) - avg Y)
      rw [sub_sub_cancel, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at h4
      have h5 : ‖((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) - avg Y‖ ≤
          15897089878618 / 2 ^ 59 + (((ELM 175 : ℚ) : ℝ) + 1 / 2 ^ 40) := by
        have := norm_add_le (avg (xLM c 175) - ((509184485886532820 / 2 ^ 60 : ℝ) : ℂ))
          (avg Y - avg (xLM c 175))
        rw [show avg (xLM c 175) - ((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) +
          (avg Y - avg (xLM c 175)) = -(((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) - avg Y) by ring,
          norm_neg] at this
        linarith
      linarith
    have h5 := norm_sub_norm_le (avg Y) (avg (Y * (q * F - 1) * Ring.inverse (q * F)))
    push_cast at h1 h3
    have h6 : ((BLM 175 : ℝ) + ELM 175 + 1 / 2 ^ 40) * (313 / 25000000 + 28660 / 2 ^ 60) *
        (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 60))) ≤
        (74271 / 2000 + 1 / 2 ^ 40) * (313 / 25000000 + 28660 / 2 ^ 60) *
          (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 60))) := by gcongr
    rw [τM]
    norm_num at h6 h3 ⊢
    linarith

/-- **Admissibility of every torus `μ`-close to the family torus, over the box**: for
`|ρ − 1/256| ≤ 2⁻⁸⁶`, every analytic torus `μ = 10⁻¹¹`-close to `K(λ)` (`λ = lamF c`) on a strip
`0 < r ≤ r_A` satisfies the bounds of the Newton step for `gcFlowMu ρ λ` with the constants `cM`.
-/
theorem boxAdm_core (hu : Ana u) (hz : Ana z) (tRt : Bd r (dTh u) aRtM) (tzt : Bd r (dTh z) aztM)
    (tLR : Bd r (Lt KamTorusA.iota u) aLRM) (tLz : Bd r (Lt KamTorusA.iota z) aLzM) :
    (gcFlowMu ρ (lamF c)).AdmBounds cM KamTorusA.iota r u z := by
  have hr := hr0.le
  obtain ⟨hDu, hDb⟩ := box_Di hρ hr0 hq hc hU hZ hA hB tu tz
  obtain ⟨hWu, hWb⟩ := adm_Wi_M hr0 hq hc hU hZ hA hB
  have hR1 : Bd r ((1 + u) - algebraMap ℂ FA 1) auM := by
    rw [map_one, add_sub_cancel_left]; exact tu
  obtain ⟨hRu, hRb⟩ := Bd.inverse hr hR1 (by rw [norm_one]; norm_num [auM, μM])
  rw [norm_one] at hRb
  obtain ⟨hT, hτ⟩ := box_T hρ hr0 hq hc hU hZ hA hB tu tz
  have hgood : (gcFlowMu ρ (lamF c)).Good u z := by
    obtain ⟨hE, hE4, hN⟩ :=
      RationalStellaratorGCMu.mu_node_bounds avM_le.1 avM_le.2 (abs_lamF_le hc)
    exact ⟨r, hr0, avM, xB_bd_avM hq tu tz, (gcFlowMu_valid ρ (lamF c) avM hE hE4 hN).1⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
    box_components hρ hr0 hq hc hU hZ hA hB tu tz
  have fb : ∀ {X X' : FA} {i : ℕ} {M : ℝ} {s : ℚ},
      DBd r X X' ((BLM i + ELM i : ℚ) : ℝ) (dRhoB * M) → M ≤ 30768 →
      BLM i + ELM i + 30768 / 2 ^ 86 ≤ s → Bd r X' (s : ℝ) := fun {X X' i M s} h hM hs => by
    refine h.bd'.le ?_
    have h1 := qle hs
    push_cast at h1 ⊢
    have h2 : dRhoB * M ≤ 30768 / 2 ^ 86 := by rw [dRhoB]; nlinarith
    linarith
  exact
  { frame := ⟨hu, hz, hDu, hRu, hWu, ⟨r, _, hr0, hDb⟩, ⟨r, _, hr0, hRb⟩, ⟨r, _, hr0, hWb⟩, hgood⟩
    hu := tu
    hz := tz
    hRt := tRt
    hzt := tzt
    hLR := tLR
    hLz := tLz
    hbD := by
      have := fb d1 (by norm_num) (s := 12751 / 10000) (by kernel_fact)
      push_cast at this; exact this
    hbDu := by
      have := fb d2 (by norm_num) (s := 22351 / 10000) (by kernel_fact)
      push_cast at this; exact this
    hbDz := by
      have := fb d3 (by norm_num) (s := 20231 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnR := by
      have := fb d4 (by norm_num) (s := 10071 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnRu := by
      have := fb d5 (by norm_num) (s := 94511 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnRz := by
      have := fb d6 (by norm_num) (s := 74451 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnZ := by
      have := fb d7 (by norm_num) (s := 10461 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnZu := by
      have := fb d8 le_rfl (s := 86851 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnZz := by
      have := fb d9 (by norm_num) (s := 81681 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hsD := hDb
    hsR := hRb
    hsW := hWb
    hT := hT
    hτ := hτ }

end Adm

/-- **Admissibility over the box** (from `μ`-closeness to the family torus). -/
theorem boxAdm {ρ : ℝ} (hρ : |ρ - 1 / 256| ≤ dRhoB) {r : ℝ} (hr : 0 < r)
    (hrA : r ≤ KamTorusA.rA) {c : ℂ} (hc : ‖c‖ = 1) {u z : FA} (hu : Ana u) (hz : Ana z)
    (hC : Close r KamTorusA.iota u z (xHM c 4) (xHM c 5) μM) :
    (gcFlowMu ρ (lamF c)).AdmBounds cM KamTorusA.iota r u z := by
  have hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16 := (Real.exp_le_exp.2 hrA).trans exp_rA_le'
  obtain ⟨hU, hZ, hA, hB⟩ := inputs_LM hrA hc hC
  have tu : Bd r u auM := by
    have := hC.du.add ((Bd_uM hc).strip hrA); rw [sub_add_cancel] at this
    exact this.le (by rw [auM]; linarith)
  have tz : Bd r z azM := by
    have := hC.dz.add ((Bd_zM hc).strip hrA); rw [sub_add_cancel] at this
    exact this.le (by rw [azM]; linarith)
  have tRt : Bd r (dTh u) aRtM := by
    have := hC.dut.add ((Bd_dTh_uM hc).strip hrA); rw [sub_add_cancel] at this
    exact this.le (by rw [aRtM]; linarith)
  have tzt : Bd r (dTh z) aztM := by
    have := hC.dzt.add ((Bd_dTh_zM hc).strip hrA); rw [sub_add_cancel] at this
    exact this.le (by rw [aztM]; linarith)
  have tLR : Bd r (Lt KamTorusA.iota u) aLRM := by
    have := hC.duL.add ((Bd_Lt_uM hc).strip hrA); rw [sub_add_cancel] at this
    exact this.le (by rw [aLRM]; linarith)
  have tLz : Bd r (Lt KamTorusA.iota z) aLzM := by
    have := hC.dzL.add ((Bd_Lt_zM hc).strip hrA); rw [sub_add_cancel] at this
    exact this.le (by rw [aLzM]; linarith)
  exact boxAdm_core hρ hr hq hc hU hZ hA hB tu tz hu hz tRt tzt tLR tLz

end PlasmaLean.Design.RationalStellaratorGC
