/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuFlow

/-!
# The `μ > 0` passing guiding-centre field as an instance of the KAM interface (`gcFlowMu`)

`gcFlowMu ρ λ : FlowFieldS` packages the flow form of the passing guiding-centre field
`B̃ = B + ∇×(ρ(x) b)`, `ρ(x) = ρ √(1 − λ|B(x)|)` (`Design/RationalStellaratorGCMuFlow`) as a field
for the KAM theorem with inverse-square-root nodes (`FlowFieldS.KamH.kam_flow_torus`):

* the expressions `gcDM, gcNRM, gcNZM` (flow form) and `gcPaM, gcPbM, gcPcM` (primitive);
* validity of `P̃_c` contains the validity of the three nodes `(1 + E)^{−1/2}`,
  `(1 + E₄)^{−1/2}` and `(1 − λ|B|)^{−1/2}`, which gives the node identities used by
  `gcMu_divFree`, `gcMu_flux_*`.

**Validity** (`gcFlowMu_valid`) reduces to three inequalities: the polynomial majorants of `E`
and `E₄` below `1`, and `|λ| · maj |B| < 1`.

**Sanity.** `gcDM_rho_zero`: for `ρ = 0` the flow form is that of the vacuum field.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton Complex WEll1Z2

/-- Validity of `P̃_c` contains the validity of the three nodes. -/
theorem valid_nodes_of_gcPcM {ρ lm : ℝ} {a : Fin 6 → ℝ} (h : PolyExprS.Valid a (gcPcM ρ lm)) :
    PolyExprS.Valid a eV ∧ PolyExprS.Valid a eV4 ∧ PolyExprS.Valid a (eN lm) := by
  simp only [gcPcM, eS, eBm, PolyExprS.Valid] at h
  exact ⟨h.2.2.1.1.2.2.2.1, h.2.2.1.1.2.2.2.2, h.2.2.1.2⟩

/-- **The three node identities** at a strip-valid torus. -/
theorem gcMu_nodes {ρ lm : ℝ} {u z : FA}
    (hg : ∃ r : ℝ, 0 < r ∧ ∃ a : Fin 6 → ℝ, (∀ i, Bd r (xB u z i) (a i)) ∧
      PolyExprS.Valid a (gcPcM ρ lm)) :
    PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1 ∧
    PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1 ∧
    PolyExprS.eval (xB u z) (eN lm) ^ 2 * (1 + -algebraMap ℂ FA (lm : ℂ) *
      PolyExprS.eval (xB u z) eBm) = 1 := by
  obtain ⟨r, hr, a, hx, hv⟩ := hg
  obtain ⟨h1, h2, h3⟩ := valid_nodes_of_gcPcM hv
  have e1 : PolyExprS.eval (xB u z) eV ^ 2 * (algebraMap ℂ FA ((1 : ℝ) : ℂ) +
      PolyExprS.eval (xB u z) (PolyExprS.ofPoly EpP)) = 1 := PolyExprS.eval_isqrt_sq hr.le hx h1
  have e2 : PolyExprS.eval (xB u z) eV4 ^ 2 * (algebraMap ℂ FA ((1 : ℝ) : ℂ) +
      PolyExprS.eval (xB u z) (PolyExprS.ofPoly E4P)) = 1 := PolyExprS.eval_isqrt_sq hr.le hx h2
  have e3 : PolyExprS.eval (xB u z) (eN lm) ^ 2 * (algebraMap ℂ FA ((1 : ℝ) : ℂ) +
      PolyExprS.eval (xB u z) (.mul (.const (-(lm : ℂ))) eBm)) = 1 :=
    PolyExprS.eval_isqrt_sq hr.le hx h3
  simp only [PolyExprS.eval_ofPoly, Complex.ofReal_one, map_one] at e1 e2
  simp only [PolyExprS.eval, Complex.ofReal_one, map_one, map_neg] at e3
  exact ⟨e1, e2, e3⟩

/-- The new leaves of `|B|` do not involve the velocities. -/
theorem noWS_eBm : NoWS eBm := by
  have b := noW_mu
  have c := noW_new
  simp only [eBm, eV4, eV, NoWS, noWS_ofPoly _ b.2.1, noWS_ofPoly _ b.2.2.2.1,
    noWS_ofPoly _ c.2.2.2.2.2.2.2.2.2.2, and_self]

/-- The `μ > 0` expressions do not involve the velocities. -/
theorem gcMu_noW (ρ lm : ℝ) : NoWS (gcDM ρ lm) ∧ NoWS (gcNRM ρ lm) ∧ NoWS (gcNZM ρ lm) := by
  have h := gc_noW 1
  rw [gcD_eq, gcNR_eq, gcNZ_eq] at h
  obtain ⟨⟨hD, -, hYD⟩, ⟨hR, -, hYR⟩, ⟨hZ, -, hYZ⟩⟩ := h
  have hB := noWS_eBm
  exact ⟨⟨hD, trivial, ⟨⟨trivial, trivial, hB⟩, trivial, hB⟩, hYD⟩,
    ⟨hR, trivial, ⟨⟨trivial, trivial, hB⟩, trivial, hB⟩, hYR⟩,
    ⟨hZ, trivial, ⟨⟨trivial, trivial, hB⟩, trivial, hB⟩, hYZ⟩⟩

/-- The new leaves of `|B|` have real constants. -/
theorem realS_eBm : PolyExprS.RealConstsS eBm := by
  have b := realConsts_mu
  have c := realConsts_new
  simp only [eBm, eV4, eV, PolyExprS.RealConstsS, PolyExprS.realConstsS_ofPoly _ b.2.1,
    PolyExprS.realConstsS_ofPoly _ b.2.2.2.1,
    PolyExprS.realConstsS_ofPoly _ c.2.2.2.2.2.2.2.2.2.2, and_self]

/-- The `μ > 0` expressions have real constants. -/
theorem gcMu_real (ρ lm : ℝ) : PolyExprS.RealConstsS (gcDM ρ lm) ∧
    PolyExprS.RealConstsS (gcNRM ρ lm) ∧ PolyExprS.RealConstsS (gcNZM ρ lm) := by
  have h := gc_real 1
  rw [gcD_eq, gcNR_eq, gcNZ_eq] at h
  obtain ⟨⟨hD, -, hYD⟩, ⟨hR, -, hYR⟩, ⟨hZ, -, hYZ⟩⟩ := h
  have hB := realS_eBm
  have r1 : (starRingEnd ℂ) (ρ : ℂ) = ρ := Complex.conj_ofReal ρ
  have r2 : (starRingEnd ℂ) ((lm : ℂ) / 2) = (lm : ℂ) / 2 := by
    rw [map_div₀, Complex.conj_ofReal, map_ofNat]
  have r3 : (starRingEnd ℂ) (-(lm : ℂ)) = -(lm : ℂ) := by rw [map_neg, Complex.conj_ofReal]
  have r4 : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
  exact ⟨⟨hD, r1, ⟨⟨r4, r2, hB⟩, r3, hB⟩, hYD⟩, ⟨hR, r1, ⟨⟨r4, r2, hB⟩, r3, hB⟩, hYR⟩,
    ⟨hZ, r1, ⟨⟨r4, r2, hB⟩, r3, hB⟩, hYZ⟩⟩

/-- **The `μ > 0` passing guiding-centre field of the rational stellarator as a field for the KAM
theorem** (`ρ = ρ₀` the gyro-length at energy `E`, `λ = μ B₀/E` the pitch parameter, model
units). -/
def gcFlowMu (ρ lm : ℝ) : FlowFieldS where
  Dp := gcDM ρ lm
  nRp := gcNRM ρ lm
  nZp := gcNZM ρ lm
  Pap := gcPaM ρ lm
  Pbp := gcPbM ρ lm
  Pcp := gcPcM ρ lm
  noW_Dp := (gcMu_noW ρ lm).1
  noW_nRp := (gcMu_noW ρ lm).2.1
  noW_nZp := (gcMu_noW ρ lm).2.2
  real_Dp := (gcMu_real ρ lm).1
  real_nRp := (gcMu_real ρ lm).2.1
  real_nZp := (gcMu_real ρ lm).2.2
  divFree := fun u z hg => by
    obtain ⟨r, hr, a, hx, -, -, -, -, -, hc⟩ := hg
    obtain ⟨h1, h2, -⟩ := gcMu_nodes ⟨r, hr, a, hx, hc⟩
    exact gcMu_divFree ρ lm u z h1 h2
  flux_a := fun u z hg => by
    obtain ⟨r, hr, a, hx, -, -, -, -, -, hc⟩ := hg
    obtain ⟨h1, h2, h3⟩ := gcMu_nodes ⟨r, hr, a, hx, hc⟩
    exact gcMu_flux_a ρ lm u z h1 h2 h3
  flux_b := fun u z hg => by
    obtain ⟨r, hr, a, hx, -, -, -, -, -, hc⟩ := hg
    obtain ⟨h1, h2, h3⟩ := gcMu_nodes ⟨r, hr, a, hx, hc⟩
    exact gcMu_flux_b ρ lm u z h1 h2 h3
  flux_c := fun u z hg => by
    obtain ⟨r, hr, a, hx, -, -, -, -, -, hc⟩ := hg
    obtain ⟨h1, -, h3⟩ := gcMu_nodes ⟨r, hr, a, hx, hc⟩
    exact gcMu_flux_c ρ lm u z h1 h3

/-- **Validity reduces to three inequalities**: all expressions of `gcFlowMu ρ λ` (and its
residuals) are valid at the bounds `a` as soon as the polynomial majorants of `E` and `E₄` are
below `1` and `|λ| · maj |B| < 1`. -/
theorem gcFlowMu_valid (ρ lm : ℝ) (a : Fin 6 → ℝ) (hE : PolyExpr.maj a EpP < 1)
    (hE4 : PolyExpr.maj a E4P < 1) (hN : |lm| * PolyExprS.maj a eBm < 1) :
    (gcFlowMu ρ lm).Valid6 a ∧ PolyExprS.Valid a (gcFlowMu ρ lm).resRp ∧
      PolyExprS.Valid a (gcFlowMu ρ lm).resZp := by
  have hV : PolyExprS.Valid a eV := ⟨PolyExprS.valid_ofPoly _ _, by
    rw [PolyExprS.maj_ofPoly]; exact hE⟩
  have hV4 : PolyExprS.Valid a eV4 := ⟨PolyExprS.valid_ofPoly _ _, by
    rw [PolyExprS.maj_ofPoly]; exact hE4⟩
  have hB : PolyExprS.Valid a eBm := ⟨PolyExprS.valid_ofPoly _ _, hV, hV4⟩
  have hNv : PolyExprS.Valid a (eN lm) := ⟨⟨trivial, hB⟩, by
    simp only [PolyExprS.maj, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hN⟩
  simp only [FlowFieldS.Valid6, FlowFieldS.resRp, FlowFieldS.resZp, gcFlowMu, gcDM, gcNRM, gcNZM,
    gcPaM, gcPbM, gcPcM, eF, eS, eYD, eYR, eYZ, eXa, eXb, eXc, eKD, eKR, eKZ, eW3, eW, eR, eq, eqR,
    eqz, eqph, PolyExprS.Valid, PolyExprS.valid_ofPoly, hV, hB, hNv, and_self]

/-- **The KAM theorem for the `μ > 0` passing guiding-centre field**: under the explicit-constant
hypotheses `KamH` the approximate torus `(u₀, z₀)` is `μ`-close to an exact, real analytic
invariant torus of the flow form of `gcFlowMu ρ λ` with rotational transform `ι`. -/
theorem gcMu_kam_torus {ρ lm ι e₀ μ : ℝ} {c : SC} {u₀ z₀ : FA}
    (K : (gcFlowMu ρ lm).KamH c ι u₀ z₀ e₀ μ) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ (gcFlowMu ρ lm).resR ι u z = 0 ∧
      (gcFlowMu ρ lm).resZ ι u z = 0 ∧ Close (rInf c) ι u z u₀ z₀ μ :=
  K.kam_flow_torus

/-- `E4_d0u` in derivative form. -/
theorem dpd0_E4 (x : Fin 6 → FA) :
    PolyExpr.deriv x (Pi.single 0 1) E4P = PolyExpr.eval x E4uP := E4_d0u x

/-- `E4_d1` in derivative form. -/
theorem dpd1_E4 (x : Fin 6 → FA) : PolyExpr.deriv x (Pi.single 1 1) E4P = 0 := E4_d1 x

/-- `QPP4_d0u` in derivative form. -/
theorem dpd0_QPP4 (x : Fin 6 → FA) :
    PolyExpr.deriv x (Pi.single 0 1) QPP4P = PolyExpr.eval x QPP4uP := QPP4_d0u x

/-- `QPP4_d1z` in derivative form. -/
theorem dpd1_QPP4 (x : Fin 6 → FA) :
    PolyExpr.deriv x (Pi.single 1 1) QPP4P = PolyExpr.eval x QPP4zP := QPP4_d1z x

/-- **Sanity**: for `ρ = 0` the `D̃` of the flow form is that of the vacuum field. -/
theorem gcDM_rho_zero (lm : ℝ) (x : Fin 6 → FA) :
    PolyExprS.eval x (gcDM 0 lm) = PolyExpr.eval x KamNewton.Dp := by
  simp [gcDM, PolyExprS.eval, PolyExprS.eval_ofPoly]

end PlasmaLean.Design.RationalStellaratorGC
