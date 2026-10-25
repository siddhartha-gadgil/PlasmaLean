/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuAdm
public import PlasmaLean.Design.RationalStellaratorGCEwInterp

/-!
# Admissibility over the energy window of gyro-lengths

For every gyro-length `ρ` with `|ρ − 1/256| ≤ hEw = 2⁻³²` and every pitch parameter
`λ = lamF c ∈ [0, 1/16]`, every analytic torus in the admissibility balls of the certified
low-resolution chain at `1/256` (`Design/RationalStellaratorGCMu*L`, radius `≈ 1.2 × 10⁻⁸`)
satisfies the bounds of the Newton step for `gcFlowMu ρ λ` with the constants `cE`
(`ewAdm_core`). As in `Design/RationalStellaratorGCBoxAdm` the field quantities `D̃, ñ` and their
derivatives move by `(ρ − 1/256)` times the corrections (`‖∂_u(F Y_z)‖ ≤ 30768`, …), i.e. by at
most `2⁻³² · 30768 ≈ 7.2 × 10⁻⁶`; the inverse `D̃⁻¹`, the torsion numerator (`DBd` bookkeeping,
`‖ΔP‖ ≤ 6 × 10⁻⁷`) and the twist are re-bounded. The constants `cE` differ from `cM` of the
pitch-angle family by `b_{n_z,u} = 0.86852`, the torsion bound `tT = 37.17`, the twist
`τ = 0.38`, the step constants `c_K ≤ 6400`, `c_L ≤ 21900`, the Taylor constant
`C₂ = 1.2 × 10¹¹` and the error `e₀ = 7 × 10⁻²¹`.

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `cE_au`: the torus bounds are those of `cM`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-- The initial error over the energy window, `e₀ = 7 × 10⁻²¹`. -/
def e0E : ℝ := 7 / 10 ^ 21

/-- The torsion bound over the window. -/
def tTE : ℝ := 3717 / 100

/-- The twist bound over the window. -/
def τE : ℝ := 38 / 100

/-- **The step constants over the energy window.** -/
def cE : SC where
  ρ := KamTorusA.rA
  δ0 := δ0G
  γ := 687 / 10000
  θ := e0E / δ0G ^ 4
  au := auM
  az := azM
  aRt := aRtM
  azt := aztM
  aLR := aLRM
  aLz := aLzM
  ac := acG
  bD := 12751 / 10000
  bDu := 22351 / 10000
  bDz := 20231 / 100000
  bnR := 10071 / 100000
  bnRu := 94511 / 100000
  bnRz := 74451 / 100000
  bnZ := 10461 / 100000
  bnZu := 86852 / 100000
  bnZz := 81681 / 100000
  sD := sDM
  sR := sRM
  sW := sWM
  tT := tTE
  τ := τE
  C2 := 120000000000
  E1 := 2718 / 1000
  cKb := 6400
  cLb := 21900

/-- **Sanity**: the torus bound of `cE` is that of `cM`. -/
theorem cE_au : cE.au = cM.au := rfl

/-- A component moved by `(ρ − 1/256) Y` with `‖Y‖ ≤ M`, `|ρ − 1/256| ≤ hEw`. -/
theorem dbd_of_subE {r : ℝ} (hr : 0 ≤ r) {ρ : ℝ} (hρ : |ρ - 1 / 256| ≤ hEw) {X X' Y : FA}
    {B M : ℝ} (hX : Bd r X B) (he : X' - X = dA ρ * Y) (hY : Bd r Y M) :
    DBd r X X' B (hEw * M) := by
  refine ⟨hX, ?_⟩
  rw [he]
  exact ((Bd_dA r ρ).mul hr hY).le (mul_le_mul_of_nonneg_right hρ hY.nonneg)

/-- The torus variables `xB u z` are bounded by `avM` when `u, z` are. -/
theorem xB_bd_avE {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {u z : FA}
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

/-! ## Admissibility over the energy window -/

section Adm

variable {ρ : ℝ} (hρ : |ρ - 1 / 256| ≤ hEw) {r : ℝ} (hr0 : 0 < r)
  (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
  {u z : FA} (hU : Bd r (u - xLM c 4) (ELM 4)) (hZ : Bd r (z - xLM c 5) (ELM 5))
  (hA : Bd r (dTh u - xLM c 6) (ELM 6)) (hB : Bd r (dTh z - xLM c 7) (ELM 7))
  (tu : Bd r u auM) (tz : Bd r z azM)
include hρ hr0 hq hc hU hZ hA hB tu tz

/-- The nine field components (`D̃, ∂_uD̃, ∂_zD̃, ñ_R, …`) of `gcFlowMu ρ λ` against those of
`gcFlowMu (1/256) λ`, with the bounds of the certified chain at `1/256`. -/
theorem ew_components :
    DBd r (PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcDM ρ (lamF c))) ((BLM 154 + ELM 154 : ℚ) : ℝ)
      (hEw * 177) ∧
    DBd r (pdS (xB u z) 0 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcDM ρ (lamF c)))
      ((BLM 160 + ELM 160 : ℚ) : ℝ) (hEw * 4997) ∧
    DBd r (pdS (xB u z) 1 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcDM ρ (lamF c)))
      ((BLM 162 + ELM 162 : ℚ) : ℝ) (hEw * 1620) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNRM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNRM ρ (lamF c))) ((BLM 156 + ELM 156 : ℚ) : ℝ)
      (hEw * 91) ∧
    DBd r (pdS (xB u z) 0 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNRM ρ (lamF c)))
      ((BLM 164 + ELM 164 : ℚ) : ℝ) (hEw * 2623) ∧
    DBd r (pdS (xB u z) 1 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNRM ρ (lamF c)))
      ((BLM 166 + ELM 166 : ℚ) : ℝ) (hEw * 861) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNZM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNZM ρ (lamF c))) ((BLM 158 + ELM 158 : ℚ) : ℝ)
      (hEw * 1113) ∧
    DBd r (pdS (xB u z) 0 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNZM ρ (lamF c)))
      ((BLM 168 + ELM 168 : ℚ) : ℝ) (hEw * 30768) ∧
    DBd r (pdS (xB u z) 1 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNZM ρ (lamF c)))
      ((BLM 170 + ELM 170 : ℚ) : ℝ) (hEw * 6181) := by
  have hr := hr0.le
  have v := valLM_le hr hq hc hU hZ hA hB
  have hx := xB_bd_avE hq tu tz
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := Bd_corr hr avM_le.1 avM_le.2 hx
    (abs_lamF_le hc)
  refine ⟨dbd_of_subE hr hρ (v 154 (by norm_num)) (eval_gcDM_sub _ _ _) m1,
    dbd_of_subE hr hρ (v 160 (by norm_num)) (pdS_gcDM_sub _ _ _ _) m2,
    dbd_of_subE hr hρ (v 162 (by norm_num)) (pdS_gcDM_sub _ _ _ _) m3,
    dbd_of_subE hr hρ (v 156 (by norm_num)) (eval_gcNRM_sub _ _ _) m4,
    dbd_of_subE hr hρ (v 164 (by norm_num)) (pdS_gcNRM_sub _ _ _ _) m5,
    dbd_of_subE hr hρ (v 166 (by norm_num)) (pdS_gcNRM_sub _ _ _ _) m6,
    dbd_of_subE hr hρ (v 158 (by norm_num)) (eval_gcNZM_sub _ _ _) m7,
    dbd_of_subE hr hρ (v 168 (by norm_num)) (pdS_gcNZM_sub _ _ _ _) m8,
    dbd_of_subE hr hρ (v 170 (by norm_num)) (pdS_gcNZM_sub _ _ _ _) m9⟩

/-- The nine components with rounded rational bounds (rounded). -/
theorem ew_components' :
    DBd r (PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcDM ρ (lamF c))) (13 / 10) (hEw * 177) ∧
    DBd r (pdS (xB u z) 0 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcDM ρ (lamF c)))
      (23 / 10) (hEw * 4997) ∧
    DBd r (pdS (xB u z) 1 (gcDM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcDM ρ (lamF c)))
      (21 / 100) (hEw * 1620) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNRM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNRM ρ (lamF c))) (11 / 100) (hEw * 91) ∧
    DBd r (pdS (xB u z) 0 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNRM ρ (lamF c)))
      (95 / 100) (hEw * 2623) ∧
    DBd r (pdS (xB u z) 1 (gcNRM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNRM ρ (lamF c)))
      (75 / 100) (hEw * 861) ∧
    DBd r (PolyExprS.eval (xB u z) (gcNZM (1 / 256) (lamF c)))
      (PolyExprS.eval (xB u z) (gcNZM ρ (lamF c))) (11 / 100) (hEw * 1113) ∧
    DBd r (pdS (xB u z) 0 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 0 (gcNZM ρ (lamF c)))
      (87 / 100) (hEw * 30768) ∧
    DBd r (pdS (xB u z) 1 (gcNZM (1 / 256) (lamF c))) (pdS (xB u z) 1 (gcNZM ρ (lamF c)))
      (82 / 100) (hEw * 6181) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
    ew_components hρ hr0 hq hc hU hZ hA hB tu tz
  have f : ∀ {i : ℕ} {s : ℚ}, BLM i + ELM i ≤ s → ((BLM i + ELM i : ℚ) : ℝ) ≤ (s : ℝ) :=
    fun h => qle h
  refine ⟨d1.le ?_ le_rfl, d2.le ?_ le_rfl, d3.le ?_ le_rfl,
    d4.le ?_ le_rfl, d5.le ?_ le_rfl, d6.le ?_ le_rfl,
    d7.le ?_ le_rfl, d8.le ?_ le_rfl, d9.le ?_ le_rfl⟩
  · exact (f (i := 154) (s := 13 / 10) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 160) (s := 23 / 10) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 162) (s := 21 / 100) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 156) (s := 11 / 100) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 164) (s := 95 / 100) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 166) (s := 75 / 100) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 158) (s := 11 / 100) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 168) (s := 87 / 100) (by decide +kernel)).trans (by norm_num)
  · exact (f (i := 170) (s := 82 / 100) (by decide +kernel)).trans (by norm_num)

/-- **The torsion numerator over the window**: `‖P(ρ) − P(1/256)‖ ≤ 6 × 10⁻⁷`, `‖P(1/256)‖ ≤ 1`. -/
theorem ew_Pof :
    DBd r ((gcFlowMu (1 / 256) (lamF c)).Pof u z) ((gcFlowMu ρ (lamF c)).Pof u z) 1
      (6 / 10 ^ 7) := by
  have hr := hr0.le
  obtain ⟨dD, dDu, dDz, dR, dRu, dRz, dZ, dZu, dZz⟩ :=
    ew_components' hρ hr0 hq hc hU hZ hA hB tu tz
  have hu := DBd.of_eq tu
  have hz := DBd.of_eq tz
  have hP := (((dR.mul hr dD).sub (dD.mul hr ((dRu.mul hr hu).add (dRz.mul hr hz)))).add
      (dR.mul hr ((dDu.mul hr hu).add (dDz.mul hr hz)))).mul hr hz |>.sub
    ((((dZ.mul hr dD).sub (dD.mul hr ((dZu.mul hr hu).add (dZz.mul hr hz)))).add
      (dZ.mul hr ((dDu.mul hr hu).add (dDz.mul hr hz)))).mul hr hu)
  exact hP.le (by norm_num [auM, azM, μM]) (by norm_num [auM, azM, μM, hEw])

/-- `D̃` over the window: `‖D̃(ρ) − d₀‖ ≤ 0.33035`. -/
theorem ew_Ddev : Bd r ((gcFlowMu ρ (lamF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ))
    (743900000000000 / 2 ^ 51 + hEw * 177) := by
  have h := Bd_DdevM hr0.le hq hc hU hZ hA hB
  obtain ⟨dD, -⟩ := ew_components' hρ hr0 hq hc hU hZ hA hB tu tz
  have e : (gcFlowMu ρ (lamF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ) =
      ((gcFlowMu (1 / 256) (lamF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ)) +
        (PolyExprS.eval (xB u z) (gcDM ρ (lamF c)) -
          PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c))) := by
    simp only [FlowFieldS.Dof, gcFlowMu]; ring
  rw [e]; exact h.add dD.2

/-- **`D̃(ρ)` is invertible**, `‖D̃(ρ)⁻¹‖ ≤ sDM`. -/
theorem ew_Di : IsUnit ((gcFlowMu ρ (lamF c)).Dof u z) ∧
    Bd r (Ring.inverse ((gcFlowMu ρ (lamF c)).Dof u z)) sDM := by
  have h := ew_Ddev hρ hr0 hq hc hU hZ hA hB tu tz
  have hn : ‖((d0G : ℝ) : ℂ)‖ = d0G := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num [d0G])]
  obtain ⟨hu, hb⟩ := Bd.inverse hr0.le h (by rw [hn]; norm_num [d0G, hEw])
  exact ⟨hu, hb.le (by rw [hn]; norm_num [d0G, sDM, hEw])⟩

/-- **Torsion and twist over the window**: `‖T₀(ρ)‖ ≤ tTE`, `|⟨T₀(ρ)⟩| ≥ τE`. -/
theorem ew_T : Bd r ((gcFlowMu ρ (lamF c)).Talg u z) tTE ∧
    τE ≤ ‖avg ((gcFlowMu ρ (lamF c)).Talg u z)‖ := by
  have hr := hr0.le
  set q := xLM c 174 with hq_def
  have hqb : Bd r q 28660 := by
    have h := valLM_le hr hq hc hU hZ hA hB 174 (by norm_num)
    exact h.le ((qle (show BLM 174 + ELM 174 ≤ 28660 by decide +kernel)).trans (by norm_num))
  have hWb : Bd r (W0of u z) (13 / 1000) := by
    have h := valLM_le hr hq hc hU hZ hA hB 108 (by norm_num)
    exact h.le ((qle (show BLM 108 + ELM 108 ≤ 13 / 1000 by decide +kernel)).trans
      (by norm_num))
  obtain ⟨dD, -⟩ := ew_components' hρ hr0 hq hc hU hZ hA hB tu tz
  -- the factor `F = D̃³ W₀²`
  have hF3 := ((dD.mul hr dD).mul hr dD).mul hr (DBd.of_eq (hWb.pow hr 2))
  have e3 : ∀ a w : FA, a * a * a * w ^ 2 = a ^ 3 * w ^ 2 := fun a w => by ring
  have hdF : Bd r ((gcFlowMu ρ (lamF c)).Dof u z ^ 3 * W0of u z ^ 2 -
      PolyExprS.eval (xB u z) (gcDM (1 / 256) (lamF c)) ^ 3 * W0of u z ^ 2) (1 / 2 ^ 34) := by
    have h2 := hF3.2
    rw [e3, e3] at h2
    exact h2.le (by norm_num [hEw])
  set F := (gcFlowMu ρ (lamF c)).Dof u z ^ 3 * W0of u z ^ 2 with hF
  have hX : Bd r (q * F - algebraMap ℂ FA 1) ((313 / 25000000 + 28660 / 2 ^ 34 : ℝ)) := by
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
  have hXe : Bd r (q * F - 1) ((313 / 25000000 + 28660 / 2 ^ 34 : ℝ)) := by rwa [map_one] at hX
  -- the numerator `Y = (1 + u)³ P q`
  have hu3 : Bd r ((1 + u) ^ 3) ((1 + auM) ^ 3) := ((Bd_one r).add tu).pow hr 3
  have hYd := ((DBd.of_eq hu3).mul hr (ew_Pof hρ hr0 hq hc hU hZ hA hB tu tz)).mul hr
    (DBd.of_eq hqb)
  set Y := (1 + u) ^ 3 * (gcFlowMu ρ (lamF c)).Pof u z * q with hY_def
  have hY0e : XLM c u z 175 = (1 + u) ^ 3 * (gcFlowMu (1 / 256) (lamF c)).Pof u z * q := rfl
  have hdY : Bd r (Y - XLM c u z 175) (3 / 100) := by
    rw [hY0e]; exact hYd.2.le (by norm_num [auM, μM, hEw])
  have hY0 := valLM_le hr hq hc hU hZ hA hB 175 (by norm_num)
  have hY0c := (ballLM_all hr hq hc hU hZ hA hB) 175 (by norm_num)
  have hYb : Bd r Y (((BLM 175 + ELM 175 : ℚ) : ℝ) + 3 / 100) := by
    have := hY0.add hdY; rwa [add_sub_cancel] at this
  have hYc : Bd r (Y - xLM c 175) (((ELM 175 : ℚ) : ℝ) + 3 / 100) := by
    have := hY0c.add hdY
    rwa [show XLM c u z 175 - xLM c 175 + (Y - XLM c u z 175) = Y - xLM c 175 by ring] at this
  obtain ⟨hDu, -⟩ := ew_Di hρ hr0 hq hc hU hZ hA hB tu tz
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
  have hB1 := qle (show BLM 175 + ELM 175 ≤ 74271 / 2000 by decide +kernel)
  have hE1 := qle (show ELM 175 ≤ 51 / 2000 by decide +kernel)
  push_cast at hB1 hE1
  refine ⟨?_, ?_⟩
  · rw [hrep]
    refine (hYb.mul hr hInv).le ?_
    push_cast
    rw [tTE]
    calc ((BLM 175 : ℝ) + ELM 175 + 3 / 100) * (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 34)))
        ≤ (74271 / 2000 + 3 / 100) * (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 34))) := by
          gcongr
      _ ≤ 3717 / 100 := by norm_num
  · have hI : Ring.inverse (q * F) = 1 - (q * F - 1) * Ring.inverse (q * F) := by
      have := Ring.mul_inverse_cancel _ hUq
      linear_combination this
    have e : (gcFlowMu ρ (lamF c)).Talg u z = Y - Y * (q * F - 1) * Ring.inverse (q * F) := by
      rw [hrep]; nth_rewrite 1 [hI]; ring
    rw [e, avg_sub]
    have h1 : ‖avg (Y * (q * F - 1) * Ring.inverse (q * F))‖ ≤
        (((BLM 175 + ELM 175 : ℚ) : ℝ) + 3 / 100) * (313 / 25000000 + 28660 / 2 ^ 34) *
          (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 34))) :=
      ((hYb.mul hr hXe).mul hr hInv).norm_avg_le hr
    have h2 : ‖avg (Y - xLM c 175)‖ ≤ ((ELM 175 : ℚ) : ℝ) + 3 / 100 := hYc.norm_avg_le hr
    rw [avg_sub] at h2
    have hav := avg_xLM_Y hc
    have h3 : (509184485886532820 / 2 ^ 60 : ℝ) - 15897089878618 / 2 ^ 59 -
        (((ELM 175 : ℚ) : ℝ) + 3 / 100) ≤ ‖avg Y‖ := by
      have h4 := norm_sub_norm_le (((509184485886532820 / 2 ^ 60 : ℝ) : ℂ))
        (((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) - avg Y)
      rw [sub_sub_cancel, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at h4
      have h5 : ‖((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) - avg Y‖ ≤
          15897089878618 / 2 ^ 59 + (((ELM 175 : ℚ) : ℝ) + 3 / 100) := by
        have := norm_add_le (avg (xLM c 175) - ((509184485886532820 / 2 ^ 60 : ℝ) : ℂ))
          (avg Y - avg (xLM c 175))
        rw [show avg (xLM c 175) - ((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) +
          (avg Y - avg (xLM c 175)) = -(((509184485886532820 / 2 ^ 60 : ℝ) : ℂ) - avg Y) by ring,
          norm_neg] at this
        linarith
      linarith
    have h5 := norm_sub_norm_le (avg Y) (avg (Y * (q * F - 1) * Ring.inverse (q * F)))
    push_cast at h1 h3
    have h6 : ((BLM 175 : ℝ) + ELM 175 + 3 / 100) * (313 / 25000000 + 28660 / 2 ^ 34) *
        (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 34))) ≤
        (74271 / 2000 + 3 / 100) * (313 / 25000000 + 28660 / 2 ^ 34) *
          (1 / (1 - (313 / 25000000 + 28660 / 2 ^ 34))) := by gcongr
    rw [τE]
    norm_num at h6 h3 ⊢
    linarith

/-- **Admissibility of every torus `μ`-close to the family torus, over the window**: for
`|ρ − 1/256| ≤ 2⁻³²`, every analytic torus `μ = 10⁻¹¹`-close to `K(λ)` (`λ = lamF c`) on a strip
`0 < r ≤ r_A` satisfies the bounds of the Newton step for `gcFlowMu ρ λ` with the constants `cE`.
-/
theorem ewAdm_core (hu : Ana u) (hz : Ana z) (tRt : Bd r (dTh u) aRtM) (tzt : Bd r (dTh z) aztM)
    (tLR : Bd r (Lt KamTorusA.iota u) aLRM) (tLz : Bd r (Lt KamTorusA.iota z) aLzM) :
    (gcFlowMu ρ (lamF c)).AdmBounds cE KamTorusA.iota r u z := by
  have hr := hr0.le
  obtain ⟨hDu, hDb⟩ := ew_Di hρ hr0 hq hc hU hZ hA hB tu tz
  obtain ⟨hWu, hWb⟩ := adm_Wi_M hr0 hq hc hU hZ hA hB
  have hR1 : Bd r ((1 + u) - algebraMap ℂ FA 1) auM := by
    rw [map_one, add_sub_cancel_left]; exact tu
  obtain ⟨hRu, hRb⟩ := Bd.inverse hr hR1 (by rw [norm_one]; norm_num [auM, μM])
  rw [norm_one] at hRb
  obtain ⟨hT, hτ⟩ := ew_T hρ hr0 hq hc hU hZ hA hB tu tz
  have hgood : (gcFlowMu ρ (lamF c)).Good u z := by
    obtain ⟨hE, hE4, hN⟩ :=
      RationalStellaratorGCMu.mu_node_bounds avM_le.1 avM_le.2 (abs_lamF_le hc)
    exact ⟨r, hr0, avM, xB_bd_avE hq tu tz, (gcFlowMu_valid ρ (lamF c) avM hE hE4 hN).1⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
    ew_components hρ hr0 hq hc hU hZ hA hB tu tz
  have fb : ∀ {X X' : FA} {i : ℕ} {M : ℝ} {s : ℚ},
      DBd r X X' ((BLM i + ELM i : ℚ) : ℝ) (hEw * M) → M ≤ 30768 →
      BLM i + ELM i + 30768 / 2 ^ 32 ≤ s → Bd r X' (s : ℝ) := fun {X X' i M s} h hM hs => by
    refine h.bd'.le ?_
    have h1 := qle hs
    push_cast at h1 ⊢
    have h2 : hEw * M ≤ 30768 / 2 ^ 32 := by rw [hEw]; nlinarith
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
      have := fb d1 (by norm_num) (s := 12751 / 10000) (by decide +kernel)
      push_cast at this; exact this
    hbDu := by
      have := fb d2 (by norm_num) (s := 22351 / 10000) (by decide +kernel)
      push_cast at this; exact this
    hbDz := by
      have := fb d3 (by norm_num) (s := 20231 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnR := by
      have := fb d4 (by norm_num) (s := 10071 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnRu := by
      have := fb d5 (by norm_num) (s := 94511 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnRz := by
      have := fb d6 (by norm_num) (s := 74451 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnZ := by
      have := fb d7 (by norm_num) (s := 10461 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnZu := by
      have := fb d8 le_rfl (s := 86852 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnZz := by
      have := fb d9 (by norm_num) (s := 81681 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hsD := hDb
    hsR := hRb
    hsW := hWb
    hT := hT
    hτ := hτ }

end Adm


end PlasmaLean.Design.RationalStellaratorGC
