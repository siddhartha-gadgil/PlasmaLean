/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCBoxExact
public import PlasmaLean.Design.RationalStellaratorGCMuForever

/-!
# All-time confinement for the `μ > 0` passing fields over the box of energies and pitch angles

For every gyro-length `ρ ∈ rhoBox = [1/256 − 2⁻⁸⁶, 1/256]` and every pitch parameter
`λ = μB₀/E ∈ [0, 1/16]`, the exact torus of `box_family_torus` is a flow torus of the `μ > 0`
passing field `gcFieldMu ρ λ = B + ∇×(ρ(x) b)`, `ρ(x) = ρ√(1 − λ|B|)`, with `0.03 ≤ rt ≤ 0.255`,
so it traps the field lines of that field and of the passing guiding-centre velocity field
`VmuF c ρ λ` (`box_family_master`).

The proof is that of `Design/RationalStellaratorGCMuForever` with `ρ₀ = 1/256` replaced by `ρ`:
the cylindrical form of the field (`cRTZ_gcFieldMuB`), the real form of the exact torus
(`box_family_exact_data`, with `D̃ ≥ 0.6` from `box_Ddev`), and the profile bounds and winding,
which only use the distance of the family torus `K(λ)` to the `μ = 0` torus `K₀` (independent of
`ρ`, because the approximate torus is the same for the whole box).

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `rMB_zero`: at `λ = 0` the effective gyro-length is `ρ`; `rMB_center`: at
`ρ = 1/256` it is that of the pitch-angle family.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 WithLp
  PlasmaLean.Kinetic.GCLittlejohn PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBallCheb PlasmaLean.Certificates.KronBall

/-- The effective gyroradius scale `ρ F` of the `μ > 0` passing field at a point of the
cylindrical variables (gyro-length `ρ`). -/
def rMB (ρ lm R z φ : ℝ) : ℝ := ρ * Fr lm R z (cos (2 * φ)) (sin (2 * φ))

/-- **Sanity**: `ρ F = ρ` for `λ = 0`. -/
theorem rMB_zero (ρ R z φ : ℝ) : rMB ρ 0 R z φ = ρ := by simp [rMB, Fr_zero]

/-- **Sanity**: at `ρ = 1/256` the scale is that of the pitch-angle family. -/
theorem rMB_center (lm R z φ : ℝ) : rMB (1 / 256) lm R z φ = rM lm R z φ := rfl

/-- **Cylindrical components of the `μ > 0` passing field**: for `R > 0`, `q > 0`, those of
`gcField (ρ F)` at the point. -/
theorem cRTZ_gcFieldMuB (ρ lm : ℝ) {R : ℝ} (hR : 0 < R) (φ z : ℝ)
    (hq : 0 < qr R z (cos (2 * φ)) (sin (2 * φ))) :
    cR (gcFieldMu ρ lm) R φ z =
        gcNRr (rMB ρ lm R z φ) R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 ∧
      cT (gcFieldMu ρ lm) R φ z =
        gcDr (rMB ρ lm R z φ) R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 ∧
      cZ (gcFieldMu ρ lm) R φ z =
        gcNZr (rMB ρ lm R z φ) R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 := by
  have hF : Fmu lm (cylPt R φ z) = Fr lm R z (cos (2 * φ)) (sin (2 * φ)) := by
    rw [Fmu, Fr, norm_field_cylPt hR]
  have e1 : cR (gcFieldMu ρ lm) R φ z = cR (gcField (rMB ρ lm R z φ)) R φ z := by
    rw [rMB, ← hF]; rfl
  have e2 : cT (gcFieldMu ρ lm) R φ z = cT (gcField (rMB ρ lm R z φ)) R φ z := by
    rw [rMB, ← hF]; rfl
  have e3 : cZ (gcFieldMu ρ lm) R φ z = cZ (gcField (rMB ρ lm R z φ)) R φ z := by
    rw [rMB, ← hF]; rfl
  rw [e1, e2, e3]
  exact cRTZ_gcField _ hR φ z hq

/-- **The exact `μ > 0` passing torus of `(ρ, λ)` in real form** (`ρ ∈ rhoBox`,
`λ ∈ [0, 1/16]`): `C²` periodic functions `Rk, zk` solving `D̃ (∂_φ K + ι ∂_θ K) = (ñ_R, ñ_z)`
for `gcFieldMu ρ λ`, with
`D̃ ≥ 0.6`, `q > 0` on the torus, and `10⁻¹¹`-close in `C¹` to the family torus `K(λ)`. -/
theorem box_family_exact_data {ρ lm : ℝ} (hρ : ρ ∈ rhoBox) (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ Rk zk : ℝ → ℝ → ℝ,
    ContDiff ℝ 2 (fun p : ℝ × ℝ => Rk p.1 p.2) ∧ ContDiff ℝ 2 (fun p : ℝ × ℝ => zk p.1 p.2) ∧
    (∀ θ φ, Rk (θ + 2 * π) φ = Rk θ φ) ∧ (∀ θ φ, zk (θ + 2 * π) φ = zk θ φ) ∧
    (∀ θ φ, Rk θ (φ + π) = Rk θ φ) ∧ (∀ θ φ, zk θ (φ + π) = zk θ φ) ∧
    (∀ θ φ, gcDr (rMB ρ lm (Rk θ φ) (zk θ φ) φ) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
        (deriv (fun φ' => Rk θ φ') φ + iota * deriv (fun θ' => Rk θ' φ) θ) =
      gcNRr (rMB ρ lm (Rk θ φ) (zk θ φ) φ) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, gcDr (rMB ρ lm (Rk θ φ) (zk θ φ) φ) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
        (deriv (fun φ' => zk θ φ') φ + iota * deriv (fun θ' => zk θ' φ) θ) =
      gcNZr (rMB ρ lm (Rk θ φ) (zk θ φ) φ) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, 3 / 5 ≤
      gcDr (rMB ρ lm (Rk θ φ) (zk θ φ) φ) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, 0 < qr (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, |Rk θ φ - Rof (uFamM lm) θ φ| ≤ μM) ∧ (∀ θ φ, |zk θ φ - Zof (zFamM lm) θ φ| ≤ μM) ∧
    (∀ θ φ, |deriv (fun θ' => Rk θ' φ) θ - (WEll1Z2.eval (dTh (uFamM lm)) θ (psi φ)).re| ≤ μM) ∧
    (∀ θ φ, |deriv (fun θ' => zk θ' φ) θ - (WEll1Z2.eval (dTh (zFamM lm)) θ (psi φ)).re| ≤
      μM) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := box_family_torus hρ hlm
  set c := cOfM lm with hcdef
  have hc : ‖c‖ = 1 := cOfM_norm lm
  replace hC : Close (KamTorusA.rA / 7) KamTorusA.iota u z (xHM c 4) (xHM c 5) μM := hC
  have hlc : lamF c = lm := lamF_cOfM hlm
  have hl1 : |lm| ≤ RationalStellaratorGCMu.lam1 := by
    rw [abs_of_nonneg hlm.1, RationalStellaratorGCMu.lam1]; exact hlm.2
  have hx := norm_xK_leM hc hC
  obtain ⟨hv6, hvR, hvZ⟩ := box_valid aResM_le.1 aResM_le.2 ρ hl1
  have hv : PolyExprS.Valid aResM (gcFlowMu ρ lm).resRp ∧
      PolyExprS.Valid aResM (gcFlowMu ρ lm).resZp := ⟨hvR, hvZ⟩
  obtain ⟨hE, hE4, hN⟩ := RationalStellaratorGCMu.mu_node_bounds aResM_le.1 aResM_le.2 hl1
  have hn := gcMu_noW ρ lm
  have h0 : (0 : ℝ) ≤ KamTorusA.rA / 7 := by norm_num [KamTorusA.rA]
  have h7 : KamTorusA.rA / 7 ≤ KamTorusA.rA := by norm_num [KamTorusA.rA]
  have tu : Bd (KamTorusA.rA / 7) u auM := by
    have := hC.du.add ((Bd_uM hc).strip h7); rw [sub_add_cancel] at this
    exact this.le (by rw [auM]; linarith)
  have tz : Bd (KamTorusA.rA / 7) z azM := by
    have := hC.dz.add ((Bd_zM hc).strip h7); rw [sub_add_cancel] at this
    exact this.le (by rw [azM]; linarith)
  have hpt : ∀ θ φ, ∀ i, ‖ptC (Rof u θ φ - 1) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) 0 0 i‖ ≤
      aResM i := by
    intro θ φ i
    fin_cases i
    · change ‖((Rof u θ φ - 1 : ℝ) : ℂ)‖ ≤ auM
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Rof_sub_one_le h0 tu θ φ
    · change ‖((Zof z θ φ : ℝ) : ℂ)‖ ≤ azM
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Zof_le h0 tz θ φ
    · change ‖((cos (2 * φ) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_le_one _
    · change ‖((sin (2 * φ) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sin_le_one _
    · change ‖((0 : ℝ) : ℂ)‖ ≤ aLRM
      rw [Complex.ofReal_zero, norm_zero]; norm_num [aLRM, μM]
    · change ‖((0 : ℝ) : ℂ)‖ ≤ aLzM
      rw [Complex.ofReal_zero, norm_zero]; norm_num [aLzM, μM]
  have hu4 : ∀ θ φ, |Rof u θ φ - 1| ≤ 1 / 4 := fun θ φ =>
    (abs_Rof_sub_one_le h0 tu θ φ).trans (by norm_num [auM, μM])
  have e1 : ∀ θ φ, 1 + (Rof u θ φ - 1) = Rof u θ φ := fun _ _ => by ring
  have hD : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcDM ρ lm) =
      (gcDr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
        (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcDM_ptC _ (hpt θ φ) hE hE4 hN (hu4 θ φ), e1, rMB]
  have hNR : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcNRM ρ lm) =
      (gcNRr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
        (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcNRM_ptC _ (hpt θ φ) hE hE4 hN (hu4 θ φ), e1, rMB]
  have hNZ : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcNZM ρ lm) =
      (gcNZr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
        (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcNZM_ptC _ (hpt θ φ) hE hE4 hN (hu4 θ φ), e1, rMB]
  have hq7 : Real.exp (KamTorusA.rA / 7) ≤ (74315 : ℕ) / 2 ^ 16 :=
    (Real.exp_le_exp.2 h7).trans exp_rA_le'
  obtain ⟨hU, hZ', hA, hB⟩ := inputs_LM h7 hc hC
  have hDdev := box_Ddev (abs_sub_le_of_rhoBox hρ) (by norm_num [KamTorusA.rA]) hq7 hc hU hZ' hA hB
    tu tz
  rw [hlc] at hDdev
  have hDval : ∀ θ φ, WEll1Z2.eval ((gcFlowMu ρ lm).Dof u z) θ (psi φ) =
      (gcDr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
        (sin (2 * φ)) : ℂ) := by
    intro θ φ
    have hvD : PolyExprS.Valid aResM (gcDM ρ lm) := hv6.1
    have hxB : FlowFieldS.Dof (gcFlowMu ρ lm) u z =
        PolyExprS.eval (xK KamTorusA.iota u z) (gcDM ρ lm) :=
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
    simp only [FlowFieldS.resRp, gcFlowMu, PolyExprS.eval] at h
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.1, hD, hNR] at h
    simp only [ptC, Matrix.cons_val] at h
    have h' : (gcDr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
        (sin (2 * φ)) : ℂ) *
        ((deriv (fun φ' => Rof u θ φ') φ + iota * deriv (fun θ' => Rof u θ' φ) θ : ℝ) : ℂ) =
        (gcNRr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
          (sin (2 * φ)) : ℂ) := by
      linear_combination h
    exact_mod_cast h'
  · have h := congrArg (fun x => WEll1Z2.eval x θ (KamTorusA.psi φ)) hZ
    simp only [FlowFieldS.resZ, eval_zero'] at h
    rw [← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hv.2] at h
    simp only [PolyExprS.evalAlg_apply] at h
    rw [eval_xK_real hu hz hur hzr] at h
    simp only [FlowFieldS.resZp, gcFlowMu, PolyExprS.eval] at h
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.2, hD, hNZ] at h
    simp only [ptC, Matrix.cons_val] at h
    have h' : (gcDr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
        (sin (2 * φ)) : ℂ) *
        ((deriv (fun φ' => Zof z θ φ') φ + iota * deriv (fun θ' => Zof z θ' φ) θ : ℝ) : ℂ) =
        (gcNZr (rMB ρ lm (Rof u θ φ) (Zof z θ φ) φ) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ))
          (sin (2 * φ)) : ℂ) := by
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
    rw [show 1 + (WEll1Z2.eval u θ (psi φ)).re - (1 + (WEll1Z2.eval (uFamM lm) θ (psi φ)).re) =
      (WEll1Z2.eval u θ (psi φ)).re - (WEll1Z2.eval (uFamM lm) θ (psi φ)).re by ring]
    exact h1
  · exact abs_re_sub_le h0 hC.dz θ (psi φ)
  · rw [(hasDerivAt_Rof_θ hu θ φ).deriv]
    exact abs_re_sub_le h0 hC.dut θ (psi φ)
  · rw [(hasDerivAt_Zof_θ hz θ φ).deriv]
    exact abs_re_sub_le h0 hC.dzt θ (psi φ)

/-- **The exact `μ > 0` passing torus of `(ρ, λ)` is a flow torus of `gcFieldMu ρ λ`**
with rotational transform `ι = (75 + √5)/562` and `0.03 ≤ rt ≤ 0.255`, for every `ρ ∈ rhoBox`
and every `λ ∈ [0, 1/16]`. -/
theorem box_family_flowTorus {ρ lm : ℝ} (hρ : ρ ∈ rhoBox) (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ Rk zk : ℝ → ℝ → ℝ, FlowTorus (gcFieldMu ρ lm) iota (3 / 100) (255 / 1000) Rk zk := by
  obtain ⟨Rk, zk, hR2, hz2, p1, p2, p3, p4, iR, iZ, hD, hq, cR0, cZ0, cRθ, cZθ⟩ :=
    box_family_exact_data hρ hlm
  have hc : ‖cOfM lm‖ = 1 := cOfM_norm lm
  have hμ : μM = 1 / 10 ^ 11 := rfl
  set δ : ℝ := μM + 185 / 100000 with hδ
  have r0 : (0 : ℝ) ≤ KamTorusA.rA := rA_nonneg'
  -- the family torus against `K₀`, pointwise
  have fu : ∀ θ φ, |Rof (uFamM lm) θ φ - Rof u₀G θ φ| ≤ 185 / 100000 := fun θ φ => by
    have := abs_re_sub_le r0 (muOld_u hc) θ (psi φ)
    simp only [Rof]
    rw [show 1 + (WEll1Z2.eval (uFamM lm) θ (psi φ)).re - (1 + (WEll1Z2.eval u₀G θ (psi φ)).re) =
      (WEll1Z2.eval (xHM (cOfM lm) 4) θ (psi φ)).re - (WEll1Z2.eval u₀G θ (psi φ)).re by
        simp only [uFamM]; ring]
    exact this
  have fz : ∀ θ φ, |Zof (zFamM lm) θ φ - Zof z₀G θ φ| ≤ 185 / 100000 := fun θ φ =>
    abs_re_sub_le r0 (muOld_z hc) θ (psi φ)
  have fa : ∀ θ φ, |(WEll1Z2.eval (dTh (uFamM lm)) θ (psi φ)).re -
      (WEll1Z2.eval (dTh u₀G) θ (psi φ)).re| ≤ 185 / 100000 := fun θ φ =>
    abs_re_sub_le r0 (muOld_a hc) θ (psi φ)
  have fb : ∀ θ φ, |(WEll1Z2.eval (dTh (zFamM lm)) θ (psi φ)).re -
      (WEll1Z2.eval (dTh z₀G) θ (psi φ)).re| ≤ 185 / 100000 := fun θ φ =>
    abs_re_sub_le r0 (muOld_b hc) θ (psi φ)
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
  · obtain ⟨h1, h2, -⟩ := cRTZ_gcFieldMuB ρ lm (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h1, h2, ← iR θ φ]
    ring
  · obtain ⟨-, h2, h3⟩ := cRTZ_gcFieldMuB ρ lm (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h3, h2, ← iZ θ φ]
    ring
  · obtain ⟨-, h2, -⟩ := cRTZ_gcFieldMuB ρ lm (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h2]
    have := hD θ φ
    have := hRpos θ φ
    positivity
  · have := hrad θ φ
    rw [hδv] at this
    linarith

/-! ## The time change and the master theorem -/

/-- **The master confinement theorem for the box**: for every `ρ ∈ rhoBox` and every
`λ ∈ [0, 1/16]` one torus profile (the exact passing torus of `(ρ, λ)`) traps the field lines of
`gcFieldMu ρ λ` and of every time change `VmuF c ρ λ`, `c ≠ 0` (the `μ > 0` passing
guiding-centre velocity field). -/
theorem box_family_master {ρ lm : ℝ} (hρ : ρ ∈ rhoBox) (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃! γ : ℝ → Space, IsFieldLine (gcFieldMu ρ lm) γ ∧ γ 0 = x₀) ∧
      (∀ γ : ℝ → Space, IsFieldLine (gcFieldMu ρ lm) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < P (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 255 / 1000 ∧ (rt (γ t) = 0 ∨ rt (γ t) < P (θs (γ t)) (φs (γ t)))) ∧
      (∀ c : ℝ, c ≠ 0 → ∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃! Y : ℝ → Space, IsFieldLine (VmuF c ρ lm) Y ∧ Y 0 = x₀) ∧
      ∀ c : ℝ, c ≠ 0 → ∀ Y : ℝ → Space, IsFieldLine (VmuF c ρ lm) Y →
        (rt (Y 0) = 0 ∨ rt (Y 0) < P (θs (Y 0)) (φs (Y 0))) →
        ∀ t, rt (Y t) ≤ 255 / 1000 ∧ (rt (Y t) = 0 ∨ rt (Y t) < P (θs (Y t)) (φs (Y t))) := by
  obtain ⟨Rk, zk, hK⟩ := box_family_flowTorus hρ hlm
  have hKU := tube27_subset_muRegion hlm
  obtain ⟨h1, h2⟩ := hK.confined_existsUnique (isOpen_muRegion lm)
    (gcFieldMu_contDiffOn ρ lm)
    (R₁ := 27 / 100) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hKU
  have hK' : ∀ c : ℝ, c ≠ 0 →
      FlowTorus (VmuF c ρ lm) iota (3 / 100) (255 / 1000) Rk zk := by
    intro c hc
    refine hK.smul (fun x => c * √(1 - lm * ‖field (1 / 4) x‖) / ‖field (1 / 4) x‖) ?_
    intro θ φ
    have hRp : 0 < Rk θ φ := by linarith [hK.R_gt θ φ]
    have hrt : rt (cylPt (Rk θ φ) φ (zk θ φ)) = rtK Rk zk θ φ := by
      rw [rt, Rc_cylPt hRp.le, cylPt_two]; rfl
    have hle : rt (cylPt (Rk θ φ) φ (zk θ φ)) ≤ 27 / 100 := by
      rw [hrt]; linarith [hK.rt_le θ φ]
    have hB := norm_field_ge (y := cylPt (Rk θ φ) φ (zk θ φ)) (by linarith)
    have hm := (hKU _ hle).2
    have hs : 0 < √(1 - lm * ‖field (1 / 4) (cylPt (Rk θ φ) φ (zk θ φ))‖) :=
      Real.sqrt_pos.2 (by linarith)
    exact div_ne_zero (mul_ne_zero hc hs.ne') (by linarith)
  exact ⟨hK.profile, hK.torusProfile, fun a b => (hK.profile_bounds a b).1,
    fun a b => (hK.profile_bounds a b).2, h1, h2,
    fun c hc => ((hK' c hc).confined_existsUnique (isOpen_muRegion lm) (VmuF_contDiffOn c ρ lm)
      (R₁ := 27 / 100) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).1,
    fun c hc => ((hK' c hc).confined_existsUnique (isOpen_muRegion lm) (VmuF_contDiffOn c ρ lm)
      (R₁ := 27 / 100) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).2⟩


end PlasmaLean.Design.RationalStellaratorGC
