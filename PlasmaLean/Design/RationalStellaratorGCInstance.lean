/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCFlow
public import PlasmaLean.Design.KamFlowIterationS

/-!
# The guiding-centre field as an instance of the KAM interface (`gcFlow`)

`gcFlow ρ : FlowFieldS` packages the flow form of the guiding-centre field
`B̃ = field (1/4) + ρ ∇×b` (`Design/RationalStellaratorGCFlow`) as a field for the KAM theorem with
an inverse-square-root node (`Design/KamFlowIterationS`, `FlowFieldS.KamH.kam_flow_torus`):

* the expressions `gcD ρ, gcNR ρ, gcNZ ρ` (flow form) and `gcPa ρ, gcPb ρ, gcPc ρ` (primitive
  `α̃ = α − ρ b♭` of the flux form, with a `dφ`-component);
* the identities hold at every strip-valid torus: validity of `P̃_c` contains the validity of the
  node `(1 + E)^{−1/2}`, which gives the node identity `W² q = 1` (`gc_node_sq`) used by
  `gc_divFree`, `gc_flux_a`, `gc_flux_b`, `gc_flux_c`.

**Sanity.** `gcFlow_resR_zero`: for `ρ = 0` the residual of `gcFlow` is the residual of
`field (1/4)` (`KamNewton.resR`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton Complex WEll1Z2

/-- Validity of `P̃_c` contains the validity of the node. -/
theorem valid_eV_of_gcPc {ρ : ℝ} {a : Fin 6 → ℝ} (h : PolyExprS.Valid a (gcPc ρ)) :
    PolyExprS.Valid a eV := by
  simp only [gcPc, eR, eW, PolyExprS.Valid] at h
  exact h.2.2.2.2.1.2

/-- **The node identity** `W²(1 + E) = 1` at a strip-valid torus. -/
theorem gc_node_sq {ρ : ℝ} {u z : FA}
    (hg : ∃ r : ℝ, 0 < r ∧ ∃ a : Fin 6 → ℝ, (∀ i, Bd r (xB u z i) (a i)) ∧
      PolyExprS.Valid a (gcPc ρ)) :
    PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1 := by
  obtain ⟨r, hr, a, hx, hv⟩ := hg
  have h := PolyExprS.eval_isqrt_sq hr.le hx (valid_eV_of_gcPc hv)
  rw [PolyExprS.eval_ofPoly, Complex.ofReal_one, map_one] at h
  exact h

/-- The guiding-centre expressions do not involve the velocities. -/
theorem gc_noW (ρ : ℝ) : NoWS (gcD ρ) ∧ NoWS (gcNR ρ) ∧ NoWS (gcNZ ρ) := by
  have b := noW_new
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [gcD, gcNR, gcNZ, eKD, eKR, eKZ, eW3, eW, eV, eR, eq, eqR, eqz, eqph, NoWS,
    noWS_ofPoly _ KamNewton.noW_Dp, noWS_ofPoly _ KamNewton.noW_nRp,
    noWS_ofPoly _ KamNewton.noW_nZp, noWS_ofPoly _ b.1, noWS_ofPoly _ b.2.1,
    noWS_ofPoly _ b.2.2.1, noWS_ofPoly _ b.2.2.2.1, noWS_ofPoly _ b.2.2.2.2.1,
    noWS_ofPoly _ b.2.2.2.2.2.1, noWS_ofPoly _ b.2.2.2.2.2.2.1, noWS_ofPoly _ b.2.2.2.2.2.2.2.1,
    noWS_ofPoly _ b.2.2.2.2.2.2.2.2.1, noWS_ofPoly _ b.2.2.2.2.2.2.2.2.2.1,
    noWS_ofPoly _ b.2.2.2.2.2.2.2.2.2.2] <;> simp

/-- The guiding-centre expressions have real constants. -/
theorem gc_real (ρ : ℝ) : PolyExprS.RealConstsS (gcD ρ) ∧ PolyExprS.RealConstsS (gcNR ρ) ∧
    PolyExprS.RealConstsS (gcNZ ρ) := by
  have b := realConsts_new
  have k := KamNewton.realConsts_all
  have r1 : (starRingEnd ℂ) (ρ : ℂ) = ρ := Complex.conj_ofReal ρ
  have r2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [gcD, gcNR, gcNZ, eKD, eKR, eKZ, eW3, eW, eV, eR, eq, eqR, eqz, eqph,
    PolyExprS.RealConstsS, PolyExprS.realConstsS_ofPoly _ k.1,
    PolyExprS.realConstsS_ofPoly _ k.2.1, PolyExprS.realConstsS_ofPoly _ k.2.2.1,
    PolyExprS.realConstsS_ofPoly _ b.1, PolyExprS.realConstsS_ofPoly _ b.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.1, PolyExprS.realConstsS_ofPoly _ b.2.2.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.2.2.1, PolyExprS.realConstsS_ofPoly _ b.2.2.2.2.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.2.2.2.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.2.2.2.2.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.2.2.2.2.2.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.2.2.2.2.2.2.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.2.2.2.2.2.2.2.2, r1, r2, map_one, map_ofNat] <;>
  simp

/-- **The guiding-centre field of the rational stellarator as a field for the KAM theorem**
(`ρ = ρ_s` in model units). -/
def gcFlow (ρ : ℝ) : FlowFieldS where
  Dp := gcD ρ
  nRp := gcNR ρ
  nZp := gcNZ ρ
  Pap := gcPa ρ
  Pbp := gcPb ρ
  Pcp := gcPc ρ
  noW_Dp := (gc_noW ρ).1
  noW_nRp := (gc_noW ρ).2.1
  noW_nZp := (gc_noW ρ).2.2
  real_Dp := (gc_real ρ).1
  real_nRp := (gc_real ρ).2.1
  real_nZp := (gc_real ρ).2.2
  divFree := fun u z hg => by
    obtain ⟨r, hr, a, hx, -, -, -, -, -, hc⟩ := hg
    exact gc_divFree ρ u z (gc_node_sq ⟨r, hr, a, hx, hc⟩)
  flux_a := fun u z hg => by
    obtain ⟨r, hr, a, hx, -, -, -, -, -, hc⟩ := hg
    exact gc_flux_a ρ u z (gc_node_sq ⟨r, hr, a, hx, hc⟩)
  flux_b := fun u z hg => by
    obtain ⟨r, hr, a, hx, -, -, -, -, -, hc⟩ := hg
    exact gc_flux_b ρ u z (gc_node_sq ⟨r, hr, a, hx, hc⟩)
  flux_c := fun u z _ => gc_flux_c ρ u z

/-- **Sanity**: for `ρ = 0` the `R`-residual of `gcFlow` is the residual of `field (1/4)`. -/
theorem gcFlow_resR_zero (ι : ℝ) (u z : FA) : (gcFlow 0).resR ι u z = KamNewton.resR ι u z := by
  rw [FlowFieldS.resR_eq, KamNewton.resR_eq]
  simp [gcFlow, FlowFieldS.Dof, KamNewton.Dof, gcD, gcNR, PolyExprS.eval, PolyExprS.eval_ofPoly]

/-- **Validity reduces to one inequality**: all expressions of `gcFlow ρ` (and its residuals) are
valid at the bounds `a` as soon as the polynomial majorant of the deviation `E` is below `1`
(every node of the guiding-centre expressions is the same node `(1 + E)^{−1/2}`). -/
theorem gcFlow_valid (ρ : ℝ) (a : Fin 6 → ℝ) (h : PolyExpr.maj a EpP < 1) :
    (gcFlow ρ).Valid6 a ∧ PolyExprS.Valid a (gcFlow ρ).resRp ∧
      PolyExprS.Valid a (gcFlow ρ).resZp := by
  have hV : PolyExprS.Valid a eV := ⟨PolyExprS.valid_ofPoly _ _, by
    rw [PolyExprS.maj_ofPoly]; exact h⟩
  simp only [FlowFieldS.Valid6, FlowFieldS.resRp, FlowFieldS.resZp, gcFlow, gcD, gcNR, gcNZ, gcPa,
    gcPb, gcPc, eKD, eKR, eKZ, eW3, eW, eR, eq, eqR, eqz, eqph, PolyExprS.Valid,
    PolyExprS.valid_ofPoly, hV, and_self]

/-- **The KAM theorem for the guiding-centre field** (the generic theorem
`FlowFieldS.KamH.kam_flow_torus` for `gcFlow ρ`): under the explicit-constant hypotheses `KamH`
the approximate torus `(u₀, z₀)` is `μ`-close to an exact, real analytic invariant torus of the
guiding-centre flow form with rotational transform `ι`. -/
theorem gc_kam_torus {ρ ι e₀ μ : ℝ} {c : SC} {u₀ z₀ : FA}
    (K : (gcFlow ρ).KamH c ι u₀ z₀ e₀ μ) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ (gcFlow ρ).resR ι u z = 0 ∧
      (gcFlow ρ).resZ ι u z = 0 ∧ Close (rInf c) ι u z u₀ z₀ μ :=
  K.kam_flow_torus

end PlasmaLean.Design.RationalStellaratorGC
