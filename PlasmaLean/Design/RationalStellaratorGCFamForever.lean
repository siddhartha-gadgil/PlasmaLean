/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCFamExact
public import PlasmaLean.Design.RationalStellaratorGCConfined

/-!
# All-time confinement for a whole interval of `ρ` (`gc_family_field_confined_forever`)

For every `ρ ∈ [63/16384, 65/16384]` the exact guiding-centre torus of `gc_family_torus` is a flow
torus of `gcField ρ` with `0.03 ≤ rt ≤ 0.255`, so it traps the field lines of `gcField ρ` and of
all its time changes (`gc_family_master`).

**The profile.** Star-shapedness and positive winding of the exact torus follow from the
certificate for the `ρ = 1/256` torus `K₀` (`gc_radial_ge`, `gc_winding_ge`,
`Design/RationalStellaratorGCStar`), with margins `0.035` and `0.0064`, and the distance of the
family torus `K(ρ)` to `K₀`: `‖K(ρ) − K₀‖ ≤ 1.85 × 10⁻³` in `u, z, ∂_θu, ∂_θz` on the strip `r_A`
(`famOld_u`, …), from the low-resolution family chain (`normLF_dUo`, …: the family torus against
the stored `ρ = 1/256` low-resolution torus) and the old distances (`dist_u`, …). The outer bound
`r_out ≤ 0.255 < 0.3` keeps the torus in the tube of `norm_field_ge`.

**Sanity.** `famOld_u`: the family torus is within `1.85 × 10⁻³` of `K₀`.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 WithLp
  PlasmaLean.Kinetic.GCLittlejohn PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBallCheb PlasmaLean.Certificates.KronBall

/-! ## The family torus is close to the `ρ = 1/256` torus -/

/-- The three-step triangle inequality. -/
theorem Bd_three {r : ℝ} {a b x y : FA} {A B C : ℝ} (h1 : Bd r (a - b) A) (h2 : Bd r (b - x) B)
    (h3 : Bd r (y - x) C) : Bd r (a - y) (A + B + C) := by
  have := (h1.add h2).add h3.neg
  rw [show a - b + (b - x) + -(y - x) = a - y by ring] at this
  exact this

/-- The perturbation margin `1.85 × 10⁻³`. -/
theorem margin_le {A B C : ℚ} (h : A + B + C ≤ 185 / 100000) :
    (A : ℝ) + B + C ≤ 185 / 100000 := by
  have h' := (Rat.cast_le (K := ℝ)).2 h
  push_cast at h'
  linarith


section Old

variable {c : ℂ} (hc : ‖c‖ = 1)
include hc

/-- The low-resolution family chain at its own centre. -/
theorem famL_inputs : Bd KamTorusA.rA (xLF c 4 - xLF c 4) (ELF 4) ∧
    Bd KamTorusA.rA (xLF c 5 - xLF c 5) (ELF 5) ∧
    Bd KamTorusA.rA (dTh (xLF c 4) - xLF c 6) (ELF 6) ∧
    Bd KamTorusA.rA (dTh (xLF c 5) - xLF c 7) (ELF 7) := by
  have hc0 := ne_zero_of_norm_one hc
  have hA6 : xLF c 6 = dTh (xLF c 4) := by rw [xLF_der_A hc0]; simp [dTh]
  have hB7 : xLF c 7 = dTh (xLF c 5) := by rw [xLF_der_B hc0]; simp [dTh]
  have z : ∀ i, Bd KamTorusA.rA (0 : FA) (ELF i) := fun i => (Bd_zero _).le (by
    have := (show ∀ i, (0 : ℚ) ≤ ELF i from getD_prop (Pr := fun q : ℚ => 0 ≤ q)
      (by decide +kernel) le_rfl) i
    exact_mod_cast this)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sub_self]; exact z 4
  · rw [sub_self]; exact z 5
  · rw [hA6, sub_self]; exact z 6
  · rw [hB7, sub_self]; exact z 7

/-- `‖u_L − u_S‖ ≤ 1.839 × 10⁻³`: the low-resolution family torus against the stored `ρ = 1/256`
low-resolution torus. -/
theorem famL_old_u : Bd KamTorusA.rA (xLF c 4 - xL 4) ((1839 / 10 ^ 6 : ℚ) : ℝ) := by
  obtain ⟨hU, hZ, hA, hB⟩ := famL_inputs hc
  have h := normLF_dUo rA_nonneg' exp_rA_le' hc hU hZ hA hB
  have e4 : XLF c (xLF c 4) (xLF c 5) 4 = xLF c 4 := rfl
  have e138 : XLF c (xLF c 4) (xLF c 5) 138 = xL 4 := rfl
  simpa [trLFN_dUo, toEx, Ex.eval, e4, e138] using h

/-- `‖z_L − z_S‖ ≤ 1.337 × 10⁻³`. -/
theorem famL_old_z : Bd KamTorusA.rA (xLF c 5 - xL 5) ((1337 / 10 ^ 6 : ℚ) : ℝ) := by
  obtain ⟨hU, hZ, hA, hB⟩ := famL_inputs hc
  have h := normLF_dZo rA_nonneg' exp_rA_le' hc hU hZ hA hB
  have e5 : XLF c (xLF c 4) (xLF c 5) 5 = xLF c 5 := rfl
  have e139 : XLF c (xLF c 4) (xLF c 5) 139 = xL 5 := rfl
  simpa [trLFN_dZo, toEx, Ex.eval, e5, e139] using h

/-- `‖∂_θ u_L − ∂_θ u_S‖ ≤ 1.316 × 10⁻³`. -/
theorem famL_old_a : Bd KamTorusA.rA (dTh (xLF c 4) - dTh (xL 4)) ((329 / 250000 : ℚ) : ℝ) := by
  obtain ⟨hU, hZ, hA, hB⟩ := famL_inputs hc
  have h := normLF_dAo rA_nonneg' exp_rA_le' hc hU hZ hA hB
  have e6 : XLF c (xLF c 4) (xLF c 5) 6 = dTh (xLF c 4) := rfl
  have e140 : XLF c (xLF c 4) (xLF c 5) 140 = dTh (xL 4) := rfl
  simpa [trLFN_dAo, toEx, Ex.eval, e6, e140] using h

/-- `‖∂_θ z_L − ∂_θ z_S‖ ≤ 1.259 × 10⁻³`. -/
theorem famL_old_b : Bd KamTorusA.rA (dTh (xLF c 5) - dTh (xL 5)) ((1259 / 10 ^ 6 : ℚ) : ℝ) := by
  obtain ⟨hU, hZ, hA, hB⟩ := famL_inputs hc
  have h := normLF_dBo rA_nonneg' exp_rA_le' hc hU hZ hA hB
  have e7 : XLF c (xLF c 4) (xLF c 5) 7 = dTh (xLF c 5) := rfl
  have e141 : XLF c (xLF c 4) (xLF c 5) 141 = dTh (xL 5) := rfl
  simpa [trLFN_dBo, toEx, Ex.eval, e7, e141] using h

/-- **`‖u(ρ) − u₀‖ ≤ 1.85 × 10⁻³`**: the family torus is close to the `ρ = 1/256` torus. -/
theorem famOld_u : Bd KamTorusA.rA (xHF c 4 - u₀G) (185 / 100000) :=
  (Bd_three (fdist_u hc) (famL_old_u hc) dist_u).le (margin_le (by decide +kernel))

/-- `‖z(ρ) − z₀‖ ≤ 1.85 × 10⁻³`. -/
theorem famOld_z : Bd KamTorusA.rA (xHF c 5 - z₀G) (185 / 100000) :=
  (Bd_three (fdist_z hc) (famL_old_z hc) dist_z).le (margin_le (by decide +kernel))

/-- `‖∂_θ u(ρ) − ∂_θ u₀‖ ≤ 1.85 × 10⁻³`. -/
theorem famOld_a : Bd KamTorusA.rA (dTh (xHF c 4) - dTh u₀G) (185 / 100000) :=
  (Bd_three (fdist_a hc) (famL_old_a hc) dist_a).le (margin_le (by decide +kernel))

/-- `‖∂_θ z(ρ) − ∂_θ z₀‖ ≤ 1.85 × 10⁻³`. -/
theorem famOld_b : Bd KamTorusA.rA (dTh (xHF c 5) - dTh z₀G) (185 / 100000) :=
  (Bd_three (fdist_b hc) (famL_old_b hc) dist_b).le (margin_le (by decide +kernel))

end Old

/-! ## The exact tori in real form -/

/-- Bounds of the residual variables of a torus close to the family torus (strip `0`). -/
def aResF : Fin 6 → ℝ := ![auF, azF, 1, 1, aLRF, aLzF]

/-- The residual variable bounds are below the validity bounds of the family. -/
theorem aResF_le : (∀ i, 0 ≤ aResF i) ∧ ∀ i, aResF i ≤ (RationalStellaratorGCFamily.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    norm_num [aResF, RationalStellaratorGCFamily.aTQ, auF, azF, aLRF, aLzF, μF]

/-- The residual variables of a torus `μ`-close to the family torus on the strip `r_A/7` are
bounded by `aResF` in the norm of `𝔸`. -/
theorem norm_xK_leF {c : ℂ} (hc : ‖c‖ = 1) {u z : FA}
    (hC : Close (KamTorusA.rA / 7) KamTorusA.iota u z (xHF c 4) (xHF c 5) μF) :
    ∀ i, ‖xK KamTorusA.iota u z i‖ ≤ aResF i := by
  have h7 : KamTorusA.rA / 7 ≤ KamTorusA.rA := by norm_num [KamTorusA.rA]
  have h0 : (0 : ℝ) ≤ KamTorusA.rA / 7 := by norm_num [KamTorusA.rA]
  have hn : ∀ {x : FA} {B : ℝ}, Bd (KamTorusA.rA / 7) x B → ‖x‖ ≤ B := fun h =>
    PolyExprS.norm_le_of_Bd le_rfl (h.strip h0)
  intro i
  fin_cases i
  · have := hC.du.add ((Bd_uF hc).strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aResF]; simp [auF]; linarith)
  · have := hC.dz.add ((Bd_zF hc).strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aResF]; simp [azF]; linarith)
  · have := PolyExprS.norm_le_of_Bd le_rfl (Bd_cS 0)
    simpa [aResF, xK] using this
  · have := PolyExprS.norm_le_of_Bd le_rfl (Bd_sS 0)
    simpa [aResF, xK] using this
  · have := hC.duL.add ((Bd_Lt_uF hc).strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aResF]; simp [aLRF]; linarith)
  · have := hC.dzL.add ((Bd_Lt_zF hc).strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aResF]; simp [aLzF]; linarith)

/-- **The exact guiding-centre torus of `ρ` in real form** (`ρ ∈ [63/16384, 65/16384]`): `C²`
periodic functions `Rk, zk` solving `D̃ (∂_φ K + ι ∂_θ K) = (ñ_R, ñ_z)` for `gcField ρ`, with
`D̃ ≥ 0.6`, `q > 0` on the torus, and `10⁻¹¹`-close in `C¹` to the family torus `K(ρ)`. -/
theorem gc_family_exact_data {ρ : ℝ} (hρ : ρ ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384)) :
    ∃ Rk zk : ℝ → ℝ → ℝ,
    ContDiff ℝ 2 (fun p : ℝ × ℝ => Rk p.1 p.2) ∧ ContDiff ℝ 2 (fun p : ℝ × ℝ => zk p.1 p.2) ∧
    (∀ θ φ, Rk (θ + 2 * π) φ = Rk θ φ) ∧ (∀ θ φ, zk (θ + 2 * π) φ = zk θ φ) ∧
    (∀ θ φ, Rk θ (φ + π) = Rk θ φ) ∧ (∀ θ φ, zk θ (φ + π) = zk θ φ) ∧
    (∀ θ φ, gcDr ρ (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
        (deriv (fun φ' => Rk θ φ') φ + iota * deriv (fun θ' => Rk θ' φ) θ) =
      gcNRr ρ (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, gcDr ρ (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
        (deriv (fun φ' => zk θ φ') φ + iota * deriv (fun θ' => zk θ' φ) θ) =
      gcNZr ρ (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, 3 / 5 ≤ gcDr ρ (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, 0 < qr (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, |Rk θ φ - Rof (uFam ρ) θ φ| ≤ μF) ∧ (∀ θ φ, |zk θ φ - Zof (zFam ρ) θ φ| ≤ μF) ∧
    (∀ θ φ, |deriv (fun θ' => Rk θ' φ) θ - (WEll1Z2.eval (dTh (uFam ρ)) θ (psi φ)).re| ≤ μF) ∧
    (∀ θ φ, |deriv (fun θ' => zk θ' φ) θ - (WEll1Z2.eval (dTh (zFam ρ)) θ (psi φ)).re| ≤ μF) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := gc_family_torus hρ
  set c := cOf ρ with hcdef
  have hc : ‖c‖ = 1 := cOf_norm ρ
  replace hC : Close (KamTorusA.rA / 7) KamTorusA.iota u z (xHF c 4) (xHF c 5) μF := hC
  have hρc : ρF c = ρ := ρF_cOf hρ
  have hx := norm_xK_leF hc hC
  have hv := RationalStellaratorGCFamily.gc_valid_res_cell aResF_le.1 aResF_le.2 ρ
  have hE := RationalStellaratorGCFamily.gc_maj_E_lt aResF_le.1 aResF_le.2
  have hn := gc_noW ρ
  have h0 : (0 : ℝ) ≤ KamTorusA.rA / 7 := by norm_num [KamTorusA.rA]
  have h7 : KamTorusA.rA / 7 ≤ KamTorusA.rA := by norm_num [KamTorusA.rA]
  have tu : Bd (KamTorusA.rA / 7) u auF := by
    have := hC.du.add ((Bd_uF hc).strip h7); rw [sub_add_cancel] at this
    exact this.le (by rw [auF]; linarith)
  have tz : Bd (KamTorusA.rA / 7) z azF := by
    have := hC.dz.add ((Bd_zF hc).strip h7); rw [sub_add_cancel] at this
    exact this.le (by rw [azF]; linarith)
  have hpt : ∀ θ φ, ∀ i, ‖ptC (Rof u θ φ - 1) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) 0 0 i‖ ≤
      aResF i := by
    intro θ φ i
    fin_cases i
    · change ‖((Rof u θ φ - 1 : ℝ) : ℂ)‖ ≤ auF
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Rof_sub_one_le h0 tu θ φ
    · change ‖((Zof z θ φ : ℝ) : ℂ)‖ ≤ azF
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Zof_le h0 tz θ φ
    · change ‖((cos (2 * φ) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_le_one _
    · change ‖((sin (2 * φ) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sin_le_one _
    · change ‖((0 : ℝ) : ℂ)‖ ≤ aLRF
      rw [Complex.ofReal_zero, norm_zero]; norm_num [aLRF, μF]
    · change ‖((0 : ℝ) : ℂ)‖ ≤ aLzF
      rw [Complex.ofReal_zero, norm_zero]; norm_num [aLzF, μF]
  have hu4 : ∀ θ φ, |Rof u θ φ - 1| ≤ 1 / 4 := fun θ φ =>
    (abs_Rof_sub_one_le h0 tu θ φ).trans (by norm_num [auF, μF])
  have e1 : ∀ θ φ, 1 + (Rof u θ φ - 1) = Rof u θ φ := fun _ _ => by ring
  have hD : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcD ρ) =
      (gcDr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcD_ptC _ (hpt θ φ) hE (hu4 θ φ), e1]
  have hNR : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcNR ρ) =
      (gcNRr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcNR_ptC _ (hpt θ φ) hE (hu4 θ φ), e1]
  have hNZ : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcNZ ρ) =
      (gcNZr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcNZ_ptC _ (hpt θ φ) hE (hu4 θ φ), e1]
  have hq7 : Real.exp (KamTorusA.rA / 7) ≤ (74315 : ℕ) / 2 ^ 16 :=
    (Real.exp_le_exp.2 h7).trans exp_rA_le'
  obtain ⟨hU, hZ', hA, hB⟩ := inputs_LF h7 hc hC
  have hDdev := Bd_DdevF h0 hq7 hc hU hZ' hA hB
  rw [hρc] at hDdev
  have hDval : ∀ θ φ, WEll1Z2.eval ((gcFlow ρ).Dof u z) θ (psi φ) =
      (gcDr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := by
    intro θ φ
    have hvD : PolyExprS.Valid aResF (gcD ρ) :=
      (gcFlow_valid ρ aResF hE).1.1
    have hxB : FlowFieldS.Dof (gcFlow ρ) u z =
        PolyExprS.eval (xK KamTorusA.iota u z) (gcD ρ) :=
      eval_congr_noWS (fun i hi => by fin_cases i <;> simp_all [xB, xK]) _ hn.1
    rw [hxB, ← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hvD]
    simp only [PolyExprS.evalAlg_apply]
    rw [eval_xK_real hu hz hur hzr, eval_gc_noW hn.1, hD]
  refine ⟨Rof u, Zof z, contDiff_Rof hu, contDiff_Zof hz, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_⟩
  · simp only [Rof, eval_periodic_θ]
  · simp only [Zof, eval_periodic_θ]
  · simp only [Rof, psi_add_pi, eval_periodic_ψ]
  · simp only [Zof, psi_add_pi, eval_periodic_ψ]
  · have h := congrArg (fun x => WEll1Z2.eval x θ (KamTorusA.psi φ)) hR
    simp only [FlowFieldS.resR, eval_zero'] at h
    rw [← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hv.1] at h
    simp only [PolyExprS.evalAlg_apply] at h
    rw [eval_xK_real hu hz hur hzr] at h
    simp only [FlowFieldS.resRp, gcFlow, PolyExprS.eval] at h
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.1, hD, hNR] at h
    simp only [ptC, Matrix.cons_val] at h
    have h' : (gcDr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) *
        ((deriv (fun φ' => Rof u θ φ') φ + iota * deriv (fun θ' => Rof u θ' φ) θ : ℝ) : ℂ) =
        (gcNRr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := by
      linear_combination h
    exact_mod_cast h'
  · have h := congrArg (fun x => WEll1Z2.eval x θ (KamTorusA.psi φ)) hZ
    simp only [FlowFieldS.resZ, eval_zero'] at h
    rw [← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hv.2] at h
    simp only [PolyExprS.evalAlg_apply] at h
    rw [eval_xK_real hu hz hur hzr] at h
    simp only [FlowFieldS.resZp, gcFlow, PolyExprS.eval] at h
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.2, hD, hNZ] at h
    simp only [ptC, Matrix.cons_val] at h
    have h' : (gcDr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) *
        ((deriv (fun φ' => Zof z θ φ') φ + iota * deriv (fun θ' => Zof z θ' φ) θ : ℝ) : ℂ) =
        (gcNZr ρ (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := by
      linear_combination h
    exact_mod_cast h'
  · have h1 := KamNewton.norm_eval_le_of_Bd h0 hDdev θ (psi φ)
    rw [eval_sub', hDval, PlasmaLean.Theory.KAM.eval_algebraMap] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    have hd := d0G_bounds.1
    have := (abs_le.mp h2).1
    norm_num at this ⊢
    linarith
  · obtain ⟨hq, -⟩ := eval_eV_ptC (hpt θ φ) hE (hu4 θ φ)
    rwa [e1] at hq
  · have h1 := abs_re_sub_le h0 hC.du θ (psi φ)
    simp only [Rof]
    rw [show 1 + (WEll1Z2.eval u θ (psi φ)).re - (1 + (WEll1Z2.eval (uFam ρ) θ (psi φ)).re) =
      (WEll1Z2.eval u θ (psi φ)).re - (WEll1Z2.eval (uFam ρ) θ (psi φ)).re by ring]
    exact h1
  · exact abs_re_sub_le h0 hC.dz θ (psi φ)
  · rw [(hasDerivAt_Rof_θ hu θ φ).deriv]
    exact abs_re_sub_le h0 hC.dut θ (psi φ)
  · rw [(hasDerivAt_Zof_θ hz θ φ).deriv]
    exact abs_re_sub_le h0 hC.dzt θ (psi φ)

/-- **The exact guiding-centre torus of `ρ` is a flow torus of `gcField ρ`** with rotational
transform `ι = (75 + √5)/562` and `0.03 ≤ rt ≤ 0.255`, for every `ρ ∈ [63/16384, 65/16384]`. -/
theorem gc_family_flowTorus {ρ : ℝ} (hρ : ρ ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384)) :
    ∃ Rk zk : ℝ → ℝ → ℝ, FlowTorus (gcField ρ) iota (3 / 100) (255 / 1000) Rk zk := by
  obtain ⟨Rk, zk, hR2, hz2, p1, p2, p3, p4, iR, iZ, hD, hq, cR0, cZ0, cRθ, cZθ⟩ :=
    gc_family_exact_data hρ
  have hc : ‖cOf ρ‖ = 1 := cOf_norm ρ
  have hμ : μF = 1 / 10 ^ 11 := rfl
  set δ : ℝ := μF + 185 / 100000 with hδ
  have r0 : (0 : ℝ) ≤ KamTorusA.rA := rA_nonneg'
  -- the family torus against `K₀`, pointwise
  have fu : ∀ θ φ, |Rof (uFam ρ) θ φ - Rof u₀G θ φ| ≤ 185 / 100000 := fun θ φ => by
    have := abs_re_sub_le r0 (famOld_u hc) θ (psi φ)
    simp only [Rof]
    rw [show 1 + (WEll1Z2.eval (uFam ρ) θ (psi φ)).re - (1 + (WEll1Z2.eval u₀G θ (psi φ)).re) =
      (WEll1Z2.eval (xHF (cOf ρ) 4) θ (psi φ)).re - (WEll1Z2.eval u₀G θ (psi φ)).re by
        simp only [uFam]; ring]
    exact this
  have fz : ∀ θ φ, |Zof (zFam ρ) θ φ - Zof z₀G θ φ| ≤ 185 / 100000 := fun θ φ =>
    abs_re_sub_le r0 (famOld_z hc) θ (psi φ)
  have fa : ∀ θ φ, |(WEll1Z2.eval (dTh (uFam ρ)) θ (psi φ)).re -
      (WEll1Z2.eval (dTh u₀G) θ (psi φ)).re| ≤ 185 / 100000 := fun θ φ =>
    abs_re_sub_le r0 (famOld_a hc) θ (psi φ)
  have fb : ∀ θ φ, |(WEll1Z2.eval (dTh (zFam ρ)) θ (psi φ)).re -
      (WEll1Z2.eval (dTh z₀G) θ (psi φ)).re| ≤ 185 / 100000 := fun θ φ =>
    abs_re_sub_le r0 (famOld_b hc) θ (psi φ)
  have tri : ∀ {a b c x y : ℝ}, |a - b| ≤ x → |b - c| ≤ y → |a - c| ≤ x + y :=
    fun {a b c x y} h1 h2 => by
      have := abs_add_le (a - b) (b - c); rw [sub_add_sub_cancel] at this; linarith
  have ha : ∀ θ φ, |(Rk θ φ - 1) - (Rof u₀G θ φ - 1)| ≤ δ := fun θ φ => by
    rw [show Rk θ φ - 1 - (Rof u₀G θ φ - 1) = Rk θ φ - Rof u₀G θ φ by ring]
    exact tri (cR0 θ φ) (fu θ φ)
  have hzz : ∀ θ φ, |zk θ φ - Zof z₀G θ φ| ≤ δ := fun θ φ => tri (cZ0 θ φ) (fz θ φ)
  have haθ : ∀ θ φ, |deriv (fun θ' => Rk θ' φ) θ - (WEll1Z2.eval (dTh u₀G) θ (psi φ)).re| ≤ δ :=
    fun θ φ => tri (cRθ θ φ) (fa θ φ)
  have hbθ : ∀ θ φ, |deriv (fun θ' => zk θ' φ) θ - (WEll1Z2.eval (dTh z₀G) θ (psi φ)).re| ≤ δ :=
    fun θ φ => tri (cZθ θ φ) (fb θ φ)
  have hδv : δ = 1 / 10 ^ 11 + 185 / 100000 := by rw [hδ, hμ]
  have hRpos : ∀ θ φ, 0 < Rk θ φ := fun θ φ => by
    have h1 := abs_le.mp (ha θ φ)
    have h2 := abs_le.mp (K₀G_bounds θ φ).1
    rw [hδv] at h1; linarith [h1.1, h2.1]
  have hrad : ∀ θ φ, 7 / 200 - 2 * δ ≤ (Rk θ φ - 1) * cos θ + zk θ φ * sin θ := fun θ φ => by
    have h0 := gc_radial_ge θ φ
    have hδ0 : 0 ≤ δ := by rw [hδv]; positivity
    have h1 : |(Rk θ φ - Rof u₀G θ φ) * cos θ| ≤ δ := by
      rw [abs_mul]
      calc |Rk θ φ - Rof u₀G θ φ| * |cos θ| ≤ δ * 1 := by
            refine mul_le_mul ?_ (abs_cos_le_one θ) (abs_nonneg _) hδ0
            have := ha θ φ
            rwa [show Rk θ φ - 1 - (Rof u₀G θ φ - 1) = Rk θ φ - Rof u₀G θ φ by ring] at this
        _ = δ := by ring
    have h2 : |(zk θ φ - Zof z₀G θ φ) * sin θ| ≤ δ := by
      rw [abs_mul]
      calc |zk θ φ - Zof z₀G θ φ| * |sin θ| ≤ δ * 1 :=
            mul_le_mul (hzz θ φ) (abs_sin_le_one θ) (abs_nonneg _) hδ0
        _ = δ := by ring
    have e : (Rk θ φ - 1) * cos θ + zk θ φ * sin θ = radG θ φ +
        (Rk θ φ - Rof u₀G θ φ) * cos θ + (zk θ φ - Zof z₀G θ φ) * sin θ := by
      rw [radG]; ring
    rw [e]
    linarith [(abs_le.mp h1).1, (abs_le.mp h2).1]
  have hrt_ge : ∀ θ φ, 3 / 100 ≤ rtK Rk zk θ φ := fun θ φ => by
    have h1 := hrad θ φ
    have hcs := cos_sq_add_sin_sq θ
    have hcsq : ((Rk θ φ - 1) * cos θ + zk θ φ * sin θ) ^ 2 ≤ (Rk θ φ - 1) ^ 2 + zk θ φ ^ 2 := by
      nlinarith [sq_nonneg ((Rk θ φ - 1) * sin θ - zk θ φ * cos θ)]
    rw [rtK, Real.le_sqrt (by norm_num) (by positivity)]
    rw [hδv] at h1
    nlinarith
  have hrt_le : ∀ θ φ, rtK Rk zk θ φ ≤ 255 / 1000 := fun θ φ => by
    have h1 := abs_le.mp (ha θ φ)
    have h2 := abs_le.mp (K₀G_bounds θ φ).1
    have h3 := abs_le.mp (hzz θ φ)
    have h4 := abs_le.mp (K₀G_bounds θ φ).2.1
    rw [hδv] at h1 h3
    rw [rtK, Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hwind : ∀ θ φ, 0 < windK Rk zk θ φ := fun θ φ => by
    have hw := gc_winding_ge θ φ
    obtain ⟨b1, b2, b3, b4⟩ := K₀G_bounds θ φ
    have h1 := abs_mul_sub_mul_le (ha θ φ) (hbθ θ φ) b1 b4
    have h2 := abs_mul_sub_mul_le (hzz θ φ) (haθ θ φ) b2 b3
    rw [windK]
    rw [windG] at hw
    have a1 := (abs_le.mp h1).1
    have a2 := (abs_le.mp h2).2
    rw [hδv] at a1 a2
    nlinarith
  refine ⟨Rk, zk, hR2, hz2, p1, p2, p3, p4, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, hwind, hrt_ge, hrt_le, by norm_num, by norm_num⟩
  · obtain ⟨h1, h2, -⟩ := cRTZ_gcField ρ (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h1, h2, ← iR θ φ]
    ring
  · obtain ⟨-, h2, h3⟩ := cRTZ_gcField ρ (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h3, h2, ← iZ θ φ]
    ring
  · obtain ⟨-, h2, -⟩ := cRTZ_gcField ρ (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h2]
    have := hD θ φ
    have := hRpos θ φ
    positivity
  · have := hrad θ φ
    rw [hδv] at this
    linarith

/-! ## Time changes and the master theorem -/

/-- The guiding-centre velocity field `(c/|B|) · gcField ρ` (`c = v_∥` in model units). -/
def VgcF (ρ c : ℝ) (x : Space) : Space := (c / ‖field (1 / 4) x‖) • gcField ρ x

/-- `VgcF ρ c` is `C¹` on the region `{r₂ > 0, B ≠ 0}`. -/
theorem VgcF_contDiffOn (ρ c : ℝ) : ContDiffOn ℝ 1 (VgcF ρ c) gcRegion := by
  have hB : ContDiffOn ℝ 1 (field (1 / 4)) gcRegion :=
    (field_contDiffOn_n (1 / 4) 1).mono fun x hx => hx.1
  have hn : ContDiffOn ℝ 1 (fun x => ‖field (1 / 4) x‖) gcRegion :=
    hB.norm ℝ fun x hx => hx.2
  have hl : ContDiffOn ℝ 1 (fun x => c / ‖field (1 / 4) x‖) gcRegion :=
    contDiffOn_const.div hn fun x hx => norm_ne_zero_iff.2 hx.2
  exact hl.smul (gcField_contDiffOn_one ρ)

/-- **The master confinement theorem for the cell**: for every `ρ ∈ [63/16384, 65/16384]` one torus
profile (the exact guiding-centre torus of `ρ`) traps the field lines of `gcField ρ` and of every
time change `(c/|B|) gcField ρ`, `c ≠ 0`. -/
theorem gc_family_master {ρ : ℝ} (hρ : ρ ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384)) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃! γ : ℝ → Space, IsFieldLine (gcField ρ) γ ∧ γ 0 = x₀) ∧
      (∀ γ : ℝ → Space, IsFieldLine (gcField ρ) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < P (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 255 / 1000 ∧ (rt (γ t) = 0 ∨ rt (γ t) < P (θs (γ t)) (φs (γ t)))) ∧
      (∀ c : ℝ, c ≠ 0 → ∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃! Y : ℝ → Space, IsFieldLine (VgcF ρ c) Y ∧ Y 0 = x₀) ∧
      ∀ c : ℝ, c ≠ 0 → ∀ Y : ℝ → Space, IsFieldLine (VgcF ρ c) Y →
        (rt (Y 0) = 0 ∨ rt (Y 0) < P (θs (Y 0)) (φs (Y 0))) →
        ∀ t, rt (Y t) ≤ 255 / 1000 ∧ (rt (Y t) = 0 ∨ rt (Y t) < P (θs (Y t)) (φs (Y t))) := by
  obtain ⟨Rk, zk, hK⟩ := gc_family_flowTorus hρ
  have hKU : ∀ y : Space, rt y ≤ 27 / 100 → y ∈ gcRegion :=
    fun y hy => tube_subset_gcRegion (by linarith)
  obtain ⟨h1, h2⟩ := hK.confined_existsUnique isOpen_gcRegion (gcField_contDiffOn_one ρ)
    (R₁ := 27 / 100) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hKU
  have hK' : ∀ c : ℝ, c ≠ 0 → FlowTorus (VgcF ρ c) iota (3 / 100) (255 / 1000) Rk zk := by
    intro c hc
    refine hK.smul (fun x => c / ‖field (1 / 4) x‖) ?_
    intro θ φ
    have hRp : 0 < Rk θ φ := by linarith [hK.R_gt θ φ]
    have hrt : rt (cylPt (Rk θ φ) φ (zk θ φ)) = rtK Rk zk θ φ := by
      rw [rt, Rc_cylPt hRp.le, cylPt_two]; rfl
    have hB := norm_field_ge (y := cylPt (Rk θ φ) φ (zk θ φ))
      (by rw [hrt]; linarith [hK.rt_le θ φ])
    exact div_ne_zero hc (by linarith)
  exact ⟨hK.profile, hK.torusProfile, fun a b => (hK.profile_bounds a b).1,
    fun a b => (hK.profile_bounds a b).2, h1, h2,
    fun c hc => ((hK' c hc).confined_existsUnique isOpen_gcRegion (VgcF_contDiffOn ρ c)
      (R₁ := 27 / 100) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).1,
    fun c hc => ((hK' c hc).confined_existsUnique isOpen_gcRegion (VgcF_contDiffOn ρ c)
      (R₁ := 27 / 100) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).2⟩

/-- **All-time confinement of the field lines of the guiding-centre fields of the cell**: for every
`ρ ∈ [63/16384, 65/16384]` there is a torus profile `P` with `0.03 ≤ P ≤ 0.255` such that from
every point on the axis or inside the torus there is exactly one two-sided field line of
`gcField ρ`, and every field line of `gcField ρ` starting there stays inside the torus for all
time. -/
theorem gc_family_field_confined_forever {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384)) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃! γ : ℝ → Space, IsFieldLine (gcField ρ) γ ∧ γ 0 = x₀) ∧
      ∀ γ : ℝ → Space, IsFieldLine (gcField ρ) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < P (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 255 / 1000 ∧ (rt (γ t) = 0 ∨ rt (γ t) < P (θs (γ t)) (φs (γ t))) := by
  obtain ⟨P, hP, h1, h2, h3, h4, -, -⟩ := gc_family_master hρ
  exact ⟨P, hP, h1, h2, h3, h4⟩

end PlasmaLean.Design.RationalStellaratorGC
