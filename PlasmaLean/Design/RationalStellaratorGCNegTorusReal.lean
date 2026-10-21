/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCNegTorusExact
public import PlasmaLean.Design.RationalStellaratorConfinedForever

/-!
# The exact `v∥ < 0` guiding-centre torus as a real `C²` torus

The exact invariant torus of the guiding-centre flow form (`gc_exact_torus_neg`,
`ρ_s = −1/256`, `ι_B = (161 − √5)/1178`) turned into real functions
`R(θ, φ) = 1 + Re F_u(θ, ψ(φ))`, `z(θ, φ) = Re F_z(θ, ψ(φ))` (`KamNewton.Rof`, `KamNewton.Zof`),
which are `C²`, periodic, `μ = 10⁻¹²`-close to the certified torus `K₀`, and
solve the flow-form invariance equations of the guiding-centre field **pointwise**
(`gc_exact_torus_real`):

`D̃(R, z, φ) (∂_φ R + ι ∂_θ R) = ñ_R(R, z, φ)`, `D̃(R, z, φ) (∂_φ z + ι ∂_θ z) = ñ_z(R, z, φ)`,

where `D̃, ñ_R, ñ_z` are the guiding-centre expressions `gcD, gcNR, gcNZ (−1/256)` evaluated at the
real point `(R − 1, z, cos 2φ, sin 2φ)` (`gcPt`); their node `(1 + E)^{−1/2}` is the positive
inverse square root there (`PolyExprS.eval_isqrt_point`).

This is the analogue, for the guiding-centre field, of `KamNewton.exactTorus` (the input of the
trapping theorem of `Design/RationalStellaratorForever`). The identification of `D̃, ñ` with the
cylindrical components of `gcField (−1/256)` and the trapping argument are in
`Design/RationalStellaratorGCNegForever`.

**Sanity.** `continuous_evalAlg`: evaluation at a point is continuous on `𝔸`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 Real

/-- Evaluation at a point is continuous on `𝔸`. -/
theorem continuous_evalAlg (θ ψ : ℝ) : Continuous (PolyExprS.evalAlg θ ψ) :=
  AddMonoidHomClass.continuous_of_bound (PolyExprS.evalAlg θ ψ) 1 fun x => by
    rw [one_mul, PolyExprS.evalAlg_apply]
    exact WEll1Z2.norm_eval_le le_rfl x θ ψ

/-- The real point `(R − 1, z, cos 2φ, sin 2φ, 0, 0)`. -/
def gcPt (R z φ : ℝ) : Fin 6 → ℂ := ptC (R - 1) z (Real.cos (2 * φ)) (Real.sin (2 * φ)) 0 0

/-- Bounds of the residual variables of a torus close to `K₀` (strip `0`). -/
def aRes : Fin 6 → ℝ := ![auG, azG, 1, 1, aLRG, aLzG]

/-- The residual variable bounds are below the validity bounds. -/
theorem aRes_le : (∀ i, 0 ≤ aRes i) ∧ ∀ i, aRes i ≤ (aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    norm_num [aRes, aTQ, auG, azG, aLRG, aLzG, μG]

/-- The residual variables of a torus `μ`-close to `K₀` on the strip `r_A/7` are bounded by
`aRes` in the norm of `𝔸`. -/
theorem norm_xK_le {u z : FA}
    (hC : Close (KamTorusA.rA / 7) iotaB u z u₀G z₀G μG) :
    ∀ i, ‖xK iotaB u z i‖ ≤ aRes i := by
  have h7 : KamTorusA.rA / 7 ≤ KamTorusA.rA := by norm_num [KamTorusA.rA]
  have h0 : (0 : ℝ) ≤ KamTorusA.rA / 7 := by norm_num [KamTorusA.rA]
  have hn : ∀ {x : FA} {B : ℝ}, Bd (KamTorusA.rA / 7) x B → ‖x‖ ≤ B := fun h =>
    PolyExprS.norm_le_of_Bd le_rfl (h.strip h0)
  intro i
  fin_cases i
  · have := hC.du.add (Bd_u₀G.strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aRes]; simp [auG]; linarith)
  · have := hC.dz.add (Bd_z₀G.strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aRes]; simp [azG]; linarith)
  · have := PolyExprS.norm_le_of_Bd le_rfl (Bd_cS 0)
    simpa [aRes, xK] using this
  · have := PolyExprS.norm_le_of_Bd le_rfl (Bd_sS 0)
    simpa [aRes, xK] using this
  · have := hC.duL.add (Bd_Lt_u₀G.strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aRes]; simp [aLRG]; linarith)
  · have := hC.dzL.add (Bd_Lt_z₀G.strip h7); rw [sub_add_cancel] at this
    exact (hn this).trans (by rw [aRes]; simp [aLzG]; linarith)

/-- The guiding-centre expressions see only `(u, z, c, s)`. -/
theorem eval_gc_noW {e : PolyExprS ℂ (Fin 6)} (he : NoWS e) (R z φ wR wZ : ℝ) :
    PolyExprS.eval (ptC (R - 1) z (Real.cos (2 * φ)) (Real.sin (2 * φ)) wR wZ) e =
      PolyExprS.eval (gcPt R z φ) e :=
  eval_congr_noWS (fun i hi => by fin_cases i <;> simp_all [ptC, gcPt]) e he

/-- **The exact guiding-centre torus as a real `C²` torus** (`ρ_s = −1/256`): `C²` periodic
functions `R, z` of `(θ, φ)`, `10⁻¹²`-close to the certified torus `K₀`, solving the flow-form
invariance equations of the guiding-centre field pointwise with rotational transform
`ι_B = (161 − √5)/1178`. -/
theorem gc_exact_torus_real : ∃ Rk zk : ℝ → ℝ → ℝ,
    ContDiff ℝ 2 (fun p : ℝ × ℝ => Rk p.1 p.2) ∧ ContDiff ℝ 2 (fun p : ℝ × ℝ => zk p.1 p.2) ∧
    (∀ θ φ, Rk (θ + 2 * π) φ = Rk θ φ) ∧ (∀ θ φ, zk (θ + 2 * π) φ = zk θ φ) ∧
    (∀ θ φ, Rk θ (φ + π) = Rk θ φ) ∧ (∀ θ φ, zk θ (φ + π) = zk θ φ) ∧
    (∀ θ φ, PolyExprS.eval (gcPt (Rk θ φ) (zk θ φ) φ) (gcD (-1 / 256)) *
        ((deriv (fun φ' => Rk θ φ') φ + iotaB * deriv (fun θ' => Rk θ' φ) θ : ℝ) : ℂ) =
      PolyExprS.eval (gcPt (Rk θ φ) (zk θ φ) φ) (gcNR (-1 / 256))) ∧
    (∀ θ φ, PolyExprS.eval (gcPt (Rk θ φ) (zk θ φ) φ) (gcD (-1 / 256)) *
        ((deriv (fun φ' => zk θ φ') φ + iotaB * deriv (fun θ' => zk θ' φ) θ : ℝ) : ℂ) =
      PolyExprS.eval (gcPt (Rk θ φ) (zk θ φ) φ) (gcNZ (-1 / 256))) ∧
    (∀ θ φ, |Rk θ φ - Rof u₀G θ φ| ≤ μG) ∧ (∀ θ φ, |zk θ φ - Zof z₀G θ φ| ≤ μG) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := gc_exact_torus_neg
  have hx := norm_xK_le hC
  have hv := gc_valid_res aRes_le.1 aRes_le.2
  have hn := gc_noW (-1 / 256)
  have h0 : (0 : ℝ) ≤ KamTorusA.rA / 7 := by norm_num [KamTorusA.rA]
  refine ⟨Rof u, Zof z, contDiff_Rof hu, contDiff_Zof hz, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_⟩
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
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.1] at h
    simp only [ptC, Matrix.cons_val] at h
    linear_combination h
  · have h := congrArg (fun x => WEll1Z2.eval x θ (KamTorusA.psi φ)) hZ
    simp only [FlowFieldS.resZ, eval_zero'] at h
    rw [← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hv.2] at h
    simp only [PolyExprS.evalAlg_apply] at h
    rw [eval_xK_real hu hz hur hzr] at h
    simp only [FlowFieldS.resZp, gcFlow, PolyExprS.eval] at h
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.2] at h
    simp only [ptC, Matrix.cons_val] at h
    linear_combination h
  · have h1 := norm_eval_le_of_Bd h0 hC.du θ (KamTorusA.psi φ)
    rw [eval_sub'] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re] at h2
    simp only [Rof]
    rw [show 1 + (WEll1Z2.eval u θ (KamTorusA.psi φ)).re -
        (1 + (WEll1Z2.eval u₀G θ (KamTorusA.psi φ)).re) =
      (WEll1Z2.eval u θ (KamTorusA.psi φ)).re - (WEll1Z2.eval u₀G θ (KamTorusA.psi φ)).re by ring]
    exact h2
  · have h1 := norm_eval_le_of_Bd h0 hC.dz θ (KamTorusA.psi φ)
    rw [eval_sub'] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re] at h2
    exact h2

end PlasmaLean.Design.RationalStellaratorGCNeg
