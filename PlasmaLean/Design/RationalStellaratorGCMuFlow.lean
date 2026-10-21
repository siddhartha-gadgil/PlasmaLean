/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuPoly
public import PlasmaLean.Design.RationalStellaratorGCInstance

/-!
# The `μ > 0` passing guiding-centre field in flow form (`gcFlowMu ρ λ`)

Passing guiding centres with magnetic moment `μ ≥ 0` and energy `E` move along the field lines of
`B̃ = B + ∇×(ρ(x) b)` with `ρ(x) = ρ₀ √(1 − λ |B(x)|)`, `λ = μ B₀/E`
(`Theory/Kinetic/GuidingCentrePassing`, `littlejohn_passing_isFieldLine`). For the curl-free field
`B = field (1/4)` of the rational stellarator, `∇×b = ½|B|⁻³ B × ∇|B|²` and
`∇ρ × b = −(ρ₀ λ/(2√(1 − λ|B|))) ∇|B| × b` is parallel to the same vector `B × ∇|B|²`, so
pointwise `B̃ = gcField (ρ₀ F)` with the scalar

`F = (1 − λ|B|/2)(1 − λ|B|)^{−1/2}`  (`F − 1 ≈ λ²|B|²/8`).

In the variables of the flow form (`Design/RationalStellaratorGCFlow`) this is the guiding-centre
flow form with `ρ` replaced by the expression tree `ρ₀ F`:

* `D̃ = D + ρ₀ F · ½ W³ κ_D`, `ñ_R = n_R + ρ₀ F · ½ W³ κ_R`, `ñ_z = n_z + ρ₀ F · ½ W³ κ_z`;
* the primitive of the flux form is `α̃ = α − ρ(x) b♭`:
  `P̃ = P − ρ₀ S (R W n_R, R² W n_z, R² W D)` with `S = (1 − λ|B|)(1 − λ|B|)^{−1/2} = √(1 − λ|B|)`.

**The nodes.** `|B| = √q R^{−4}` is the tree `eBm = (q P P₄) · (1 + E)^{−1/2} (1 + E₄)^{−1/2}` with
the node `(1 + E)^{−1/2}` of `gcFlow`, a node `(1 + E₄)^{−1/2}` in `u` only (`E₄ = R⁸P₄² − 1`,
`Design/RationalStellaratorGCMuPoly`), and `eN λ = (1 − λ|B|)^{−1/2}` is a third node, nested
around `eBm`.

**Results.**
* `gcMu_divFree`, `gcMu_flux_a`, `gcMu_flux_b`, `gcMu_flux_c`: the identities of `FlowFieldS` at
  every torus point where the three node identities hold. They follow from those of `gcFlow`
  (`gc_divFree`, `gc_flux_*` at `ρ = 0, 1`) and two identities for the derivatives of `|B|`:
  `∇|B| · κ = 0` (`gcMu_gradBm`, i.e. `∇|B| ⊥ B × ∇|B|²`) and the three components of
  `|B| · ½W³κ = R³ W (∇|B| × (n_R, R D, n_z))` (`gcMu_bmY_*`).
* `gcFlowMu ρ λ : FlowFieldS`, so the KAM theorem `FlowFieldS.KamH.kam_flow_torus` applies.

**Sanity.** `gcFlowMu_zero`: for `λ = 0` the flow form is that of `gcFlow ρ` (`F = 1`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton Complex WEll1Z2

/-! ## The expressions -/

/-- The node `(1 + E₄)^{−1/2}`, so that `P₄ (1 + E₄)^{−1/2} = R^{−4}`. -/
def eV4 : PolyExprS ℂ (Fin 6) := .isqrt 1 (PolyExprS.ofPoly E4P)

/-- `|B| = (q P P₄) · (1 + E)^{−1/2} (1 + E₄)^{−1/2} = √q R^{−4}`. -/
def eBm : PolyExprS ℂ (Fin 6) := .mul (PolyExprS.ofPoly QPP4P) (.mul eV eV4)

/-- The node `(1 − λ|B|)^{−1/2}`. -/
def eN (lm : ℝ) : PolyExprS ℂ (Fin 6) := .isqrt 1 (.mul (.const (-(lm : ℂ))) eBm)

/-- The scalar `F = (1 − λ|B|/2)(1 − λ|B|)^{−1/2}` of the guiding-centre correction. -/
def eF (lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .mul (.sub (.const 1) (.mul (.const ((lm : ℂ) / 2)) eBm)) (eN lm)

/-- The scalar `S = (1 − λ|B|)(1 − λ|B|)^{−1/2} = √(1 − λ|B|)` of the primitive. -/
def eS (lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .mul (.sub (.const 1) (.mul (.const (lm : ℂ)) eBm)) (eN lm)

/-- The correction `½ W³ κ_D` of `D̃` per unit `ρ`. -/
def eYD : PolyExprS ℂ (Fin 6) := .mul (.const (1 / 2 : ℂ)) (.mul eW3 eKD)

/-- The correction `½ W³ κ_R` of `ñ_R` per unit `ρ`. -/
def eYR : PolyExprS ℂ (Fin 6) := .mul (.const (1 / 2 : ℂ)) (.mul eW3 eKR)

/-- The correction `½ W³ κ_z` of `ñ_z` per unit `ρ`. -/
def eYZ : PolyExprS ℂ (Fin 6) := .mul (.const (1 / 2 : ℂ)) (.mul eW3 eKZ)

/-- `R W n_R` (the `dR`-part of `b♭`, times `R`). -/
def eXa : PolyExprS ℂ (Fin 6) := .mul eR (.mul eW (PolyExprS.ofPoly KamNewton.nRp))

/-- `R² W n_z` (the `dz`-part of `b♭`, times `R²`). -/
def eXb : PolyExprS ℂ (Fin 6) := .mul eR (.mul eR (.mul eW (PolyExprS.ofPoly KamNewton.nZp)))

/-- `R² W D` (the `dφ`-part of `b♭`). -/
def eXc : PolyExprS ℂ (Fin 6) := .mul eR (.mul eR (.mul eW (PolyExprS.ofPoly KamNewton.Dp)))

/-- `D̃ = R³ B̃_φ` of the `μ > 0` passing field. -/
def gcDM (ρ lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .add (PolyExprS.ofPoly KamNewton.Dp) (.mul (.const (ρ : ℂ)) (.mul (eF lm) eYD))

/-- `ñ_R = R⁴ B̃^R` of the `μ > 0` passing field. -/
def gcNRM (ρ lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .add (PolyExprS.ofPoly KamNewton.nRp) (.mul (.const (ρ : ℂ)) (.mul (eF lm) eYR))

/-- `ñ_z = R⁴ B̃^z` of the `μ > 0` passing field. -/
def gcNZM (ρ lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .add (PolyExprS.ofPoly KamNewton.nZp) (.mul (.const (ρ : ℂ)) (.mul (eF lm) eYZ))

/-- `P̃_a = P_a − ρ₀ S R W n_R`. -/
def gcPaM (ρ lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .sub (PolyExprS.ofPoly KamNewton.Pap) (.mul (.const (ρ : ℂ)) (.mul (eS lm) eXa))

/-- `P̃_b = P_b − ρ₀ S R² W n_z`. -/
def gcPbM (ρ lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .sub (PolyExprS.ofPoly KamNewton.Pbp) (.mul (.const (ρ : ℂ)) (.mul (eS lm) eXb))

/-- `P̃_c = −ρ₀ S R² W D`. -/
def gcPcM (ρ lm : ℝ) : PolyExprS ℂ (Fin 6) :=
  .sub (.const 0) (.mul (.const (ρ : ℂ)) (.mul (eS lm) eXc))

/-- The trees of `gcFlow` in the factored form used here. -/
theorem gcD_eq (ρ : ℝ) : gcD ρ = .add (PolyExprS.ofPoly KamNewton.Dp) (.mul (.const (ρ : ℂ)) eYD) :=
  rfl

/-- The trees of `gcFlow` in the factored form used here. -/
theorem gcNR_eq (ρ : ℝ) :
    gcNR ρ = .add (PolyExprS.ofPoly KamNewton.nRp) (.mul (.const (ρ : ℂ)) eYR) := rfl

/-- The trees of `gcFlow` in the factored form used here. -/
theorem gcNZ_eq (ρ : ℝ) :
    gcNZ ρ = .add (PolyExprS.ofPoly KamNewton.nZp) (.mul (.const (ρ : ℂ)) eYZ) := rfl

/-- The trees of `gcFlow` in the factored form used here. -/
theorem gcPa_eq (ρ : ℝ) :
    gcPa ρ = .sub (PolyExprS.ofPoly KamNewton.Pap) (.mul (.const (ρ : ℂ)) eXa) := rfl

/-- The trees of `gcFlow` in the factored form used here. -/
theorem gcPb_eq (ρ : ℝ) :
    gcPb ρ = .sub (PolyExprS.ofPoly KamNewton.Pbp) (.mul (.const (ρ : ℂ)) eXb) := rfl

/-- The trees of `gcFlow` in the factored form used here. -/
theorem gcPc_eq (ρ : ℝ) : gcPc ρ = .sub (.const 0) (.mul (.const (ρ : ℂ)) eXc) := rfl

/-- `2 · (λ/2) = λ` in `𝔸`. -/
theorem half_lm (lm : ℝ) :
    2 * algebraMap ℂ FA ((lm : ℂ) / 2) = algebraMap ℂ FA (lm : ℂ) := by
  rw [← map_ofNat (algebraMap ℂ FA) 2, ← map_mul]; congr 1; ring

/-! ## Node derivatives -/

/-- Derivative of the node `(1 + E₄)^{−1/2}`. -/
theorem deriv_eV4 (x h : Fin 6 → FA) : PolyExprS.deriv x h eV4 =
    -(algebraMap ℂ FA (1 / 2) * PolyExprS.eval x eV4 ^ 3) * PolyExpr.deriv x h E4P := by
  simp only [eV4, PolyExprS.deriv, PolyExprS.deriv_ofPoly, smul_half]


/-- Derivative of the node `(1 − λ|B|)^{−1/2}`. -/
theorem deriv_eN (lm : ℝ) (x h : Fin 6 → FA) : PolyExprS.deriv x h (eN lm) =
    -(algebraMap ℂ FA (1 / 2) * PolyExprS.eval x (eN lm) ^ 3) *
      (algebraMap ℂ FA (-(lm : ℂ)) * PolyExprS.deriv x h eBm) := by
  simp only [eN, PolyExprS.deriv, PolyExprS.eval, smul_half, zero_mul, zero_add]

/-- `deriv` of the expanded `|B|`: `D|B| = D(qPP₄) V V₄ + qPP₄ (DV V₄ + V DV₄)`. -/
theorem deriv_eBm (x h : Fin 6 → FA) : PolyExprS.deriv x h eBm =
    PolyExpr.deriv x h QPP4P * (PolyExprS.eval x eV * PolyExprS.eval x eV4) +
      PolyExpr.eval x QPP4P * (-(algebraMap ℂ FA (1 / 2) * PolyExprS.eval x eV ^ 3) *
        PolyExpr.deriv x h EpP * PolyExprS.eval x eV4 + PolyExprS.eval x eV *
        (-(algebraMap ℂ FA (1 / 2) * PolyExprS.eval x eV4 ^ 3) * PolyExpr.deriv x h E4P)) := by
  simp only [eBm, PolyExprS.deriv, PolyExprS.eval, PolyExprS.deriv_ofPoly, PolyExprS.eval_ofPoly,
    deriv_eV, deriv_eV4]

/-! ## Evaluation of the pieces -/

/-- `|B| = (q P P₄) V V₄`. -/
theorem eval_eBm (x : Fin 6 → FA) :
    PolyExprS.eval x eBm =
      PolyExpr.eval x QPP4P * (PolyExprS.eval x eV * PolyExprS.eval x eV4) := by
  simp only [eBm, PolyExprS.eval, PolyExprS.eval_ofPoly]

/-- `½ W³ κ_D`. -/
theorem eval_eYD (x : Fin 6 → FA) : PolyExprS.eval x eYD =
    algebraMap ℂ FA (1 / 2) * (PolyExprS.eval x eW3 * PolyExprS.eval x eKD) := by
  simp only [eYD, PolyExprS.eval]

/-- `½ W³ κ_R`. -/
theorem eval_eYR (x : Fin 6 → FA) : PolyExprS.eval x eYR =
    algebraMap ℂ FA (1 / 2) * (PolyExprS.eval x eW3 * PolyExprS.eval x eKR) := by
  simp only [eYR, PolyExprS.eval]

/-- `½ W³ κ_z`. -/
theorem eval_eYZ (x : Fin 6 → FA) : PolyExprS.eval x eYZ =
    algebraMap ℂ FA (1 / 2) * (PolyExprS.eval x eW3 * PolyExprS.eval x eKZ) := by
  simp only [eYZ, PolyExprS.eval]

/-- `R W n_R`. -/
theorem eval_eXa (u z : FA) : PolyExprS.eval (xB u z) eXa = (1 + u) * (PolyExpr.eval (xB u z) PuP *
    PolyExprS.eval (xB u z) eV * PolyExpr.eval (xB u z) KamNewton.nRp) := by
  simp only [eXa, eR, eW, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one]

/-- `R² W n_z`. -/
theorem eval_eXb (u z : FA) : PolyExprS.eval (xB u z) eXb = (1 + u) * ((1 + u) *
    (PolyExpr.eval (xB u z) PuP * PolyExprS.eval (xB u z) eV *
      PolyExpr.eval (xB u z) KamNewton.nZp)) := by
  simp only [eXb, eR, eW, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one]

/-- `R² W D`. -/
theorem eval_eXc (u z : FA) : PolyExprS.eval (xB u z) eXc = (1 + u) * ((1 + u) *
    (PolyExpr.eval (xB u z) PuP * PolyExprS.eval (xB u z) eV *
      PolyExpr.eval (xB u z) KamNewton.Dp)) := by
  simp only [eXc, eR, eW, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one]

/-- `q = n_R² + R² D² + n_z²`. -/
theorem gc_eval_eq (u z : FA) : PolyExprS.eval (xB u z) eq =
    PolyExpr.eval (xB u z) KamNewton.nRp ^ 2 +
      (1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp ^ 2 +
      PolyExpr.eval (xB u z) KamNewton.nZp ^ 2 := by
  simp only [eq, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one]; ring

/-- `∂_u q` in terms of the partial derivatives of the field polynomials. -/
theorem gc_eval_eqR (u z : FA) : PolyExprS.eval (xB u z) eqR =
    2 * PolyExpr.eval (xB u z) KamNewton.nRp * pd (xB u z) 0 KamNewton.nRp +
    2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp * pd (xB u z) 0 KamNewton.Dp +
    2 * PolyExpr.eval (xB u z) KamNewton.nZp * pd (xB u z) 0 KamNewton.nZp +
    2 * (1 + u) * PolyExpr.eval (xB u z) KamNewton.Dp ^ 2 := by
  simp only [eqR, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one, map_ofNat,
    pd0_D, pd0_nR, pd0_nZ]; ring

/-- `∂_z q` in terms of the partial derivatives of the field polynomials. -/
theorem gc_eval_eqz (u z : FA) : PolyExprS.eval (xB u z) eqz =
    2 * PolyExpr.eval (xB u z) KamNewton.nRp * pd (xB u z) 1 KamNewton.nRp +
    2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp * pd (xB u z) 1 KamNewton.Dp +
    2 * PolyExpr.eval (xB u z) KamNewton.nZp * pd (xB u z) 1 KamNewton.nZp := by
  simp only [eqz, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one, map_ofNat,
    pd1_D, pd1_nR, pd1_nZ]; ring

/-- `∂_φ q` in terms of the partial derivatives of the field polynomials. -/
theorem gc_eval_eqph (u z : FA) : PolyExprS.eval (xB u z) eqph =
    2 * PolyExpr.eval (xB u z) KamNewton.nRp * phiD (xB u z) KamNewton.nRp +
    2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp * phiD (xB u z) KamNewton.Dp +
    2 * PolyExpr.eval (xB u z) KamNewton.nZp * phiD (xB u z) KamNewton.nZp := by
  simp only [eqph, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one, map_ofNat,
    phiD_D, phiD_nR, phiD_nZ]; ring

/-- `κ_D = R² (R n_z ∂_u q − 8 n_z q − R n_R ∂_z q)`. -/
theorem gc_eval_eKD (u z : FA) : PolyExprS.eval (xB u z) eKD = (1 + u) ^ 2 *
    ((1 + u) * PolyExpr.eval (xB u z) KamNewton.nZp * PolyExprS.eval (xB u z) eqR -
      8 * PolyExpr.eval (xB u z) KamNewton.nZp * PolyExprS.eval (xB u z) eq -
      (1 + u) * PolyExpr.eval (xB u z) KamNewton.nRp * PolyExprS.eval (xB u z) eqz) := by
  simp only [eKD, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one, map_ofNat]; ring

/-- `κ_R = R⁵ D ∂_z q − R³ n_z ∂_φ q`. -/
theorem gc_eval_eKR (u z : FA) : PolyExprS.eval (xB u z) eKR =
    (1 + u) ^ 5 * PolyExpr.eval (xB u z) KamNewton.Dp * PolyExprS.eval (xB u z) eqz -
      (1 + u) ^ 3 * PolyExpr.eval (xB u z) KamNewton.nZp * PolyExprS.eval (xB u z) eqph := by
  simp only [eKR, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one]; ring

/-- `κ_z = R³ n_R ∂_φ q − R⁵ D ∂_u q + 8 R⁴ D q`. -/
theorem gc_eval_eKZ (u z : FA) : PolyExprS.eval (xB u z) eKZ =
    (1 + u) ^ 3 * PolyExpr.eval (xB u z) KamNewton.nRp * PolyExprS.eval (xB u z) eqph -
      (1 + u) ^ 5 * PolyExpr.eval (xB u z) KamNewton.Dp * PolyExprS.eval (xB u z) eqR +
      8 * (1 + u) ^ 4 * PolyExpr.eval (xB u z) KamNewton.Dp * PolyExprS.eval (xB u z) eq := by
  simp only [eKZ, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one, map_ofNat]; ring

/-- `W³ = (P V)³`. -/
theorem gc_eval_eW3 (u z : FA) : PolyExprS.eval (xB u z) eW3 =
    (PolyExpr.eval (xB u z) PuP * PolyExprS.eval (xB u z) eV) ^ 3 := by
  simp only [eW3, eW, PolyExprS.eval, PolyExprS.eval_ofPoly]; ring

/-! ## The identities for `|B|` -/

-- BEGIN GENERATED

set_option linter.unusedSimpArgs false in
/-- `∇|B| · κ = 0` (`∇|B| ⊥ B × ∇|B|²`), at points with the node identities. -/
theorem gcMu_gradBm (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)
    (hV4 : PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1) :
    PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm * PolyExprS.eval (xB u z) eKD +
      PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm * PolyExprS.eval (xB u z) eKR +
      PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm * PolyExprS.eval (xB u z) eKZ = 0 := by
  simp only [deriv_eBm]
  simp only [deriv_single, deriv_phiDir]
  have h_Q := QPP4_val (xB u z)
  have h_Q0 := QPP4_d0 (xB u z)
  have h_Q1 := QPP4_d1 (xB u z)
  have h_Qph := QPP4_dph (xB u z)
  have h_E := E_val (xB u z)
  have h_E0 := E_d0 (xB u z)
  have h_E1 := E_d1 (xB u z)
  have h_Eph := E_dph (xB u z)
  have h_E4 := E4_val (xB u z)
  have h_E40 := E4_d0 (xB u z)
  have h_E41 := E4_d1 (xB u z)
  have h_E4ph := E4_dph (xB u z)
  have h_P1 := P_d1 (xB u z)
  have h_Pph := P_dph (xB u z)
  have h_P41 := P4_d1 (xB u z)
  have h_P4ph := P4_dph (xB u z)
  have hq := gc_eval_eq u z
  have hKD := gc_eval_eKD u z
  have hKR := gc_eval_eKR u z
  have hKZ := gc_eval_eKZ u z
  have hqR := gc_eval_eqR u z
  have hqz := gc_eval_eqz u z
  have hqph := gc_eval_eqph u z
  have h_half := half_rel
  simp only [xB_zero] at *
  rw [← hq] at h_Q h_Q0 h_Q1 h_Qph h_E h_E0 h_E1 h_Eph
  rw [h_E] at hV
  rw [h_E4] at hV4
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  linear_combination (KR*V*V4) * h_Q0 + (KZ*V*V4) * h_Q1 + (KD*V*V4) * h_Qph + (-E0*KR*V4*hA*V^3 -
    E1*KZ*V4*hA*V^3 - E40*KR*V*hA*V4^3 - E41*KZ*V*hA*V4^3 - E4ph*KD*V*hA*V4^3 - Eph*KD*V4*hA*V^3) *
    h_Q + (-KR*P*P4*V4*hA*qv*V^3) * h_E0 + (-KZ*P*P4*V4*hA*qv*V^3) * h_E1 + (-KD*P*P4*V4*hA*qv*V^3)
    * h_Eph + (-KR*P*P4*V*hA*qv*V4^3) * h_E40 + (-KZ*P*P4*V*hA*qv*V4^3) * h_E41 +
    (-KD*P*P4*V*hA*qv*V4^3) * h_E4ph + (KZ*P4*V*V4*qv - 2*KZ*P4*V4*hA*P^2*V^3*qv^2) * h_P1 +
    (KD*P4*V*V4*qv - 2*KD*P4*V4*hA*P^2*V^3*qv^2) * h_Pph + (KZ*P*V*V4*qv) * h_P41 + (KD*P*V*V4*qv)
    * h_P4ph + (2*D*Dph*P*P4*V*V4 + 2*P*P4*V*V4*nR*nRph + 2*P*P4*V*V4*nZ*nZph +
    2*D*Dph*P*P4*V*V4*u^2 + 4*D*Dph*P*P4*V*V4*u - 2*D*Dph*P4*V4*hA*qv*P^3*V^3 -
    2*P4*V4*hA*nR*nRph*qv*P^3*V^3 - 2*P4*V4*hA*nZ*nZph*qv*P^3*V^3 - 4*D*Dph*P4*V4*hA*qv*u*P^3*V^3 -
    2*D*Dph*P4*V4*hA*qv*P^3*V^3*u^2) * hKD + (P*P40*V*V4*qv + P0*P4*V*V4*qv + 2*P*P4*V*V4*D^2 -
    8*P*V*hA*qv*P4^3*V4^3 + 2*D*D0*P*P4*V*V4 + 2*P*P4*V*V4*nR*nR0 + 2*P*P4*V*V4*nZ*nZ0 +
    2*P*P4*V*V4*u*D^2 - 280*P*V*hA*qv*P4^3*V4^3*u^3 - 280*P*V*hA*qv*P4^3*V4^3*u^4 -
    168*P*V*hA*qv*P4^3*V4^3*u^2 - 168*P*V*hA*qv*P4^3*V4^3*u^5 - 56*P*V*hA*qv*u*P4^3*V4^3 -
    56*P*V*hA*qv*P4^3*V4^3*u^6 - 8*P*V*hA*qv*P4^3*V4^3*u^7 - 2*P*P40*V*hA*qv*P4^2*V4^3 -
    2*P0*P4*V4*hA*P^2*V^3*qv^2 - 2*P4*V4*hA*qv*D^2*P^3*V^3 + 2*D*D0*P*P4*V*V4*u^2 +
    4*D*D0*P*P4*V*V4*u - 140*P*P40*V*hA*qv*P4^2*V4^3*u^4 - 112*P*P40*V*hA*qv*P4^2*V4^3*u^3 -
    112*P*P40*V*hA*qv*P4^2*V4^3*u^5 - 56*P*P40*V*hA*qv*P4^2*V4^3*u^2 -
    56*P*P40*V*hA*qv*P4^2*V4^3*u^6 - 16*P*P40*V*hA*qv*u*P4^2*V4^3 - 16*P*P40*V*hA*qv*P4^2*V4^3*u^7
    - 2*D*D0*P4*V4*hA*qv*P^3*V^3 - 2*P*P40*V*hA*qv*P4^2*V4^3*u^8 - 2*P4*V4*hA*nR*nR0*qv*P^3*V^3 -
    2*P4*V4*hA*nZ*nZ0*qv*P^3*V^3 - 2*P4*V4*hA*qv*u*D^2*P^3*V^3 - 4*D*D0*P4*V4*hA*qv*u*P^3*V^3 -
    2*D*D0*P4*V4*hA*qv*P^3*V^3*u^2) * hKR + (2*D*D1*P*P4*V*V4 + 2*P*P4*V*V4*nR*nR1 +
    2*P*P4*V*V4*nZ*nZ1 + 2*D*D1*P*P4*V*V4*u^2 + 4*D*D1*P*P4*V*V4*u - 2*D*D1*P4*V4*hA*qv*P^3*V^3 -
    2*P4*V4*hA*nR*nR1*qv*P^3*V^3 - 2*P4*V4*hA*nZ*nZ1*qv*P^3*V^3 - 4*D*D1*P4*V4*hA*qv*u*P^3*V^3 -
    2*D*D1*P4*V4*hA*qv*P^3*V^3*u^2) * hKZ + (-2*D1*P*P4*V*V4*D^2 + 2*P*P4*V*V4*nZph*nZ^2 -
    70*D1*P*P4*V*V4*D^2*u^3 - 70*D1*P*P4*V*V4*D^2*u^4 - 42*D1*P*P4*V*V4*D^2*u^2 -
    42*D1*P*P4*V*V4*D^2*u^5 - 14*D1*P*P4*V*V4*u*D^2 - 14*D1*P*P4*V*V4*D^2*u^6 -
    2*D*P*P4*V*V4*nR*nR1 - 2*D*P*P4*V*V4*nZ*nZ1 - 2*D1*P*P4*V*V4*D^2*u^7 + 2*D*Dph*P*P4*V*V4*nZ +
    2*P*P4*V*V4*nR*nRph*nZ + 2*P*P4*V*V4*nZph*nZ^2*u^3 + 6*P*P4*V*V4*nZph*u*nZ^2 +
    6*P*P4*V*V4*nZph*nZ^2*u^2 - 20*D*P*P4*V*V4*nR*nR1*u^2 - 20*D*P*P4*V*V4*nR*nR1*u^3 -
    20*D*P*P4*V*V4*nZ*nZ1*u^2 - 20*D*P*P4*V*V4*nZ*nZ1*u^3 - 10*D*P*P4*V*V4*nR*nR1*u -
    10*D*P*P4*V*V4*nR*nR1*u^4 - 10*D*P*P4*V*V4*nZ*nZ1*u - 10*D*P*P4*V*V4*nZ*nZ1*u^4 -
    2*D*P*P4*V*V4*nR*nR1*u^5 - 2*D*P*P4*V*V4*nZ*nZ1*u^5 - 2*P4*V4*hA*nZph*qv*P^3*V^3*nZ^2 +
    2*D*Dph*P*P4*V*V4*nZ*u^5 + 2*D1*P4*V4*hA*qv*D^2*P^3*V^3 + 2*P*P4*V*V4*nR*nRph*nZ*u^3 +
    6*P*P4*V*V4*nR*nRph*nZ*u + 6*P*P4*V*V4*nR*nRph*nZ*u^2 + 10*D*Dph*P*P4*V*V4*nZ*u +
    10*D*Dph*P*P4*V*V4*nZ*u^4 + 20*D*Dph*P*P4*V*V4*nZ*u^2 + 20*D*Dph*P*P4*V*V4*nZ*u^3 -
    6*P4*V4*hA*nZph*qv*u*P^3*V^3*nZ^2 - 6*P4*V4*hA*nZph*qv*P^3*V^3*nZ^2*u^2 -
    2*D*Dph*P4*V4*hA*nZ*qv*P^3*V^3 - 2*P4*V4*hA*nR*nRph*nZ*qv*P^3*V^3 -
    2*P4*V4*hA*nZph*qv*P^3*V^3*nZ^2*u^3 + 2*D*P4*V4*hA*nR*nR1*qv*P^3*V^3 +
    2*D*P4*V4*hA*nZ*nZ1*qv*P^3*V^3 + 2*D1*P4*V4*hA*qv*D^2*P^3*V^3*u^7 +
    14*D1*P4*V4*hA*qv*u*D^2*P^3*V^3 + 14*D1*P4*V4*hA*qv*D^2*P^3*V^3*u^6 +
    42*D1*P4*V4*hA*qv*D^2*P^3*V^3*u^2 + 42*D1*P4*V4*hA*qv*D^2*P^3*V^3*u^5 +
    70*D1*P4*V4*hA*qv*D^2*P^3*V^3*u^3 + 70*D1*P4*V4*hA*qv*D^2*P^3*V^3*u^4 -
    20*D*Dph*P4*V4*hA*nZ*qv*P^3*V^3*u^2 - 20*D*Dph*P4*V4*hA*nZ*qv*P^3*V^3*u^3 -
    10*D*Dph*P4*V4*hA*nZ*qv*u*P^3*V^3 - 10*D*Dph*P4*V4*hA*nZ*qv*P^3*V^3*u^4 -
    6*P4*V4*hA*nR*nRph*nZ*qv*u*P^3*V^3 - 6*P4*V4*hA*nR*nRph*nZ*qv*P^3*V^3*u^2 -
    2*D*Dph*P4*V4*hA*nZ*qv*P^3*V^3*u^5 - 2*P4*V4*hA*nR*nRph*nZ*qv*P^3*V^3*u^3 +
    2*D*P4*V4*hA*nR*nR1*qv*P^3*V^3*u^5 + 2*D*P4*V4*hA*nZ*nZ1*qv*P^3*V^3*u^5 +
    10*D*P4*V4*hA*nR*nR1*qv*u*P^3*V^3 + 10*D*P4*V4*hA*nR*nR1*qv*P^3*V^3*u^4 +
    10*D*P4*V4*hA*nZ*nZ1*qv*u*P^3*V^3 + 10*D*P4*V4*hA*nZ*nZ1*qv*P^3*V^3*u^4 +
    20*D*P4*V4*hA*nR*nR1*qv*P^3*V^3*u^2 + 20*D*P4*V4*hA*nR*nR1*qv*P^3*V^3*u^3 +
    20*D*P4*V4*hA*nZ*nZ1*qv*P^3*V^3*u^2 + 20*D*P4*V4*hA*nZ*nZ1*qv*P^3*V^3*u^3) * hqR +
    (2*P*P4*V*V4*D^3 + D*P*P40*V*V4*qv + D*P0*P4*V*V4*qv - 2*P*P4*V*V4*nRph*nR^2 +
    2*D0*P*P4*V*V4*D^2 + 2*P*P4*V*V4*D^3*u^6 + 12*P*P4*V*V4*u*D^3 + 12*P*P4*V*V4*D^3*u^5 +
    30*P*P4*V*V4*D^3*u^2 + 30*P*P4*V*V4*D^3*u^4 + 40*P*P4*V*V4*D^3*u^3 + D*P*P40*V*V4*qv*u^5 +
    D*P0*P4*V*V4*qv*u^5 - 8*D*P*V*hA*qv*P4^3*V4^3 - 6*P*P4*V*V4*nRph*u*nR^2 -
    6*P*P4*V*V4*nRph*nR^2*u^2 - 2*D*Dph*P*P4*V*V4*nR - 2*P*P4*V*V4*nR*nZ*nZph -
    2*P*P4*V*V4*nRph*nR^2*u^3 - 2*P4*V4*hA*qv*D^3*P^3*V^3 + 2*D*P*P4*V*V4*nR*nR0 +
    2*D*P*P4*V*V4*nZ*nZ0 + 2*D0*P*P4*V*V4*D^2*u^7 + 5*D*P*P40*V*V4*qv*u + 5*D*P*P40*V*V4*qv*u^4 +
    5*D*P0*P4*V*V4*qv*u + 5*D*P0*P4*V*V4*qv*u^4 + 10*D*P*P40*V*V4*qv*u^2 + 10*D*P*P40*V*V4*qv*u^3 +
    10*D*P0*P4*V*V4*qv*u^2 + 10*D*P0*P4*V*V4*qv*u^3 + 14*D0*P*P4*V*V4*u*D^2 +
    14*D0*P*P4*V*V4*D^2*u^6 + 42*D0*P*P4*V*V4*D^2*u^2 + 42*D0*P*P4*V*V4*D^2*u^5 +
    70*D0*P*P4*V*V4*D^2*u^3 + 70*D0*P*P4*V*V4*D^2*u^4 - 7392*D*P*V*hA*qv*P4^3*V4^3*u^6 -
    6336*D*P*V*hA*qv*P4^3*V4^3*u^5 - 6336*D*P*V*hA*qv*P4^3*V4^3*u^7 -
    3960*D*P*V*hA*qv*P4^3*V4^3*u^4 - 3960*D*P*V*hA*qv*P4^3*V4^3*u^8 -
    1760*D*P*V*hA*qv*P4^3*V4^3*u^3 - 1760*D*P*V*hA*qv*P4^3*V4^3*u^9 - 528*D*P*V*hA*qv*P4^3*V4^3*u^2
    - 528*D*P*V*hA*qv*P4^3*V4^3*u^10 - 96*D*P*V*hA*qv*u*P4^3*V4^3 - 96*D*P*V*hA*qv*P4^3*V4^3*u^11 -
    40*P4*V4*hA*qv*D^3*P^3*V^3*u^3 - 30*P4*V4*hA*qv*D^3*P^3*V^3*u^2 -
    30*P4*V4*hA*qv*D^3*P^3*V^3*u^4 - 20*D*Dph*P*P4*V*V4*nR*u^2 - 20*D*Dph*P*P4*V*V4*nR*u^3 -
    12*P4*V4*hA*qv*u*D^3*P^3*V^3 - 12*P4*V4*hA*qv*D^3*P^3*V^3*u^5 - 10*D*Dph*P*P4*V*V4*nR*u -
    10*D*Dph*P*P4*V*V4*nR*u^4 - 8*D*P*V*hA*qv*P4^3*V4^3*u^12 - 6*P*P4*V*V4*nR*nZ*nZph*u -
    6*P*P4*V*V4*nR*nZ*nZph*u^2 - 2*D*Dph*P*P4*V*V4*nR*u^5 - 2*D*P*P40*V*hA*qv*P4^2*V4^3 -
    2*D*P0*P4*V4*hA*P^2*V^3*qv^2 - 2*D0*P4*V4*hA*qv*D^2*P^3*V^3 - 2*P*P4*V*V4*nR*nZ*nZph*u^3 -
    2*P4*V4*hA*qv*D^3*P^3*V^3*u^6 + 2*D*P*P4*V*V4*nR*nR0*u^5 + 2*D*P*P4*V*V4*nZ*nZ0*u^5 +
    2*P4*V4*hA*nRph*qv*P^3*V^3*nR^2 + 10*D*P*P4*V*V4*nR*nR0*u + 10*D*P*P4*V*V4*nR*nR0*u^4 +
    10*D*P*P4*V*V4*nZ*nZ0*u + 10*D*P*P4*V*V4*nZ*nZ0*u^4 + 20*D*P*P4*V*V4*nR*nR0*u^2 +
    20*D*P*P4*V*V4*nR*nR0*u^3 + 20*D*P*P4*V*V4*nZ*nZ0*u^2 + 20*D*P*P4*V*V4*nZ*nZ0*u^3 -
    3432*D*P*P40*V*hA*qv*P4^2*V4^3*u^6 - 3432*D*P*P40*V*hA*qv*P4^2*V4^3*u^7 -
    2574*D*P*P40*V*hA*qv*P4^2*V4^3*u^5 - 2574*D*P*P40*V*hA*qv*P4^2*V4^3*u^8 -
    1430*D*P*P40*V*hA*qv*P4^2*V4^3*u^4 - 1430*D*P*P40*V*hA*qv*P4^2*V4^3*u^9 -
    572*D*P*P40*V*hA*qv*P4^2*V4^3*u^3 - 572*D*P*P40*V*hA*qv*P4^2*V4^3*u^10 -
    156*D*P*P40*V*hA*qv*P4^2*V4^3*u^2 - 156*D*P*P40*V*hA*qv*P4^2*V4^3*u^11 -
    70*D0*P4*V4*hA*qv*D^2*P^3*V^3*u^3 - 70*D0*P4*V4*hA*qv*D^2*P^3*V^3*u^4 -
    42*D0*P4*V4*hA*qv*D^2*P^3*V^3*u^2 - 42*D0*P4*V4*hA*qv*D^2*P^3*V^3*u^5 -
    26*D*P*P40*V*hA*qv*u*P4^2*V4^3 - 26*D*P*P40*V*hA*qv*P4^2*V4^3*u^12 -
    20*D*P0*P4*V4*hA*P^2*V^3*qv^2*u^2 - 20*D*P0*P4*V4*hA*P^2*V^3*qv^2*u^3 -
    14*D0*P4*V4*hA*qv*u*D^2*P^3*V^3 - 14*D0*P4*V4*hA*qv*D^2*P^3*V^3*u^6 -
    10*D*P0*P4*V4*hA*u*P^2*V^3*qv^2 - 10*D*P0*P4*V4*hA*P^2*V^3*qv^2*u^4 -
    2*D*P*P40*V*hA*qv*P4^2*V4^3*u^13 - 2*D*P0*P4*V4*hA*P^2*V^3*qv^2*u^5 -
    2*D*P4*V4*hA*nR*nR0*qv*P^3*V^3 - 2*D*P4*V4*hA*nZ*nZ0*qv*P^3*V^3 -
    2*D0*P4*V4*hA*qv*D^2*P^3*V^3*u^7 + 2*D*Dph*P4*V4*hA*nR*qv*P^3*V^3 +
    2*P4*V4*hA*nR*nZ*nZph*qv*P^3*V^3 + 2*P4*V4*hA*nRph*qv*P^3*V^3*nR^2*u^3 +
    6*P4*V4*hA*nRph*qv*u*P^3*V^3*nR^2 + 6*P4*V4*hA*nRph*qv*P^3*V^3*nR^2*u^2 -
    20*D*P4*V4*hA*nR*nR0*qv*P^3*V^3*u^2 - 20*D*P4*V4*hA*nR*nR0*qv*P^3*V^3*u^3 -
    20*D*P4*V4*hA*nZ*nZ0*qv*P^3*V^3*u^2 - 20*D*P4*V4*hA*nZ*nZ0*qv*P^3*V^3*u^3 -
    10*D*P4*V4*hA*nR*nR0*qv*u*P^3*V^3 - 10*D*P4*V4*hA*nR*nR0*qv*P^3*V^3*u^4 -
    10*D*P4*V4*hA*nZ*nZ0*qv*u*P^3*V^3 - 10*D*P4*V4*hA*nZ*nZ0*qv*P^3*V^3*u^4 -
    2*D*P4*V4*hA*nR*nR0*qv*P^3*V^3*u^5 - 2*D*P4*V4*hA*nZ*nZ0*qv*P^3*V^3*u^5 +
    2*D*Dph*P4*V4*hA*nR*qv*P^3*V^3*u^5 + 2*P4*V4*hA*nR*nZ*nZph*qv*P^3*V^3*u^3 +
    6*P4*V4*hA*nR*nZ*nZph*qv*u*P^3*V^3 + 6*P4*V4*hA*nR*nZ*nZph*qv*P^3*V^3*u^2 +
    10*D*Dph*P4*V4*hA*nR*qv*u*P^3*V^3 + 10*D*Dph*P4*V4*hA*nR*qv*P^3*V^3*u^4 +
    20*D*Dph*P4*V4*hA*nR*qv*P^3*V^3*u^2 + 20*D*Dph*P4*V4*hA*nR*qv*P^3*V^3*u^3) * hqz +
    (-P*P40*V*V4*nZ*qv - P0*P4*V*V4*nZ*qv - 2*P*P4*V*V4*nZ*D^2 - 2*P*P4*V*V4*nZ0*nZ^2 +
    2*P*P4*V*V4*nR1*nR^2 - P*P40*V*V4*nZ*qv*u^3 - P0*P4*V*V4*nZ*qv*u^3 - 12*P*P4*V*V4*nZ*D^2*u^2 -
    8*P*P4*V*V4*nZ*u*D^2 - 8*P*P4*V*V4*nZ*D^2*u^3 - 6*P*P4*V*V4*nZ0*u*nZ^2 -
    6*P*P4*V*V4*nZ0*nZ^2*u^2 - 3*P*P40*V*V4*nZ*qv*u - 3*P*P40*V*V4*nZ*qv*u^2 - 3*P0*P4*V*V4*nZ*qv*u
    - 3*P0*P4*V*V4*nZ*qv*u^2 - 2*D*D0*P*P4*V*V4*nZ - 2*P*P4*V*V4*nR*nR0*nZ - 2*P*P4*V*V4*nZ*D^2*u^4
    - 2*P*P4*V*V4*nZ0*nZ^2*u^3 + 2*D*D1*P*P4*V*V4*nR + 2*P*P4*V*V4*nR*nZ*nZ1 +
    2*P*P4*V*V4*nR1*nR^2*u^3 + 6*P*P4*V*V4*nR1*u*nR^2 + 6*P*P4*V*V4*nR1*nR^2*u^2 +
    8*P*V*hA*nZ*qv*P4^3*V4^3 - 20*D*D0*P*P4*V*V4*nZ*u^2 - 20*D*D0*P*P4*V*V4*nZ*u^3 -
    10*D*D0*P*P4*V*V4*nZ*u - 10*D*D0*P*P4*V*V4*nZ*u^4 - 6*P*P4*V*V4*nR*nR0*nZ*u -
    6*P*P4*V*V4*nR*nR0*nZ*u^2 - 2*D*D0*P*P4*V*V4*nZ*u^5 - 2*P*P4*V*V4*nR*nR0*nZ*u^3 -
    2*P4*V4*hA*nR1*qv*P^3*V^3*nR^2 + 2*D*D1*P*P4*V*V4*nR*u^5 + 2*P*P4*V*V4*nR*nZ*nZ1*u^3 +
    2*P*P40*V*hA*nZ*qv*P4^2*V4^3 + 2*P0*P4*V4*hA*nZ*P^2*V^3*qv^2 + 2*P4*V4*hA*nZ*qv*D^2*P^3*V^3 +
    2*P4*V4*hA*nZ0*qv*P^3*V^3*nZ^2 + 6*P*P4*V*V4*nR*nZ*nZ1*u + 6*P*P4*V*V4*nR*nZ*nZ1*u^2 +
    8*P*V*hA*nZ*qv*P4^3*V4^3*u^10 + 10*D*D1*P*P4*V*V4*nR*u + 10*D*D1*P*P4*V*V4*nR*u^4 +
    20*D*D1*P*P4*V*V4*nR*u^2 + 20*D*D1*P*P4*V*V4*nR*u^3 + 80*P*V*hA*nZ*qv*u*P4^3*V4^3 +
    80*P*V*hA*nZ*qv*P4^3*V4^3*u^9 + 360*P*V*hA*nZ*qv*P4^3*V4^3*u^2 + 360*P*V*hA*nZ*qv*P4^3*V4^3*u^8
    + 960*P*V*hA*nZ*qv*P4^3*V4^3*u^3 + 960*P*V*hA*nZ*qv*P4^3*V4^3*u^7 +
    1680*P*V*hA*nZ*qv*P4^3*V4^3*u^4 + 1680*P*V*hA*nZ*qv*P4^3*V4^3*u^6 +
    2016*P*V*hA*nZ*qv*P4^3*V4^3*u^5 - 6*P4*V4*hA*nR1*qv*u*P^3*V^3*nR^2 -
    6*P4*V4*hA*nR1*qv*P^3*V^3*nR^2*u^2 - 2*D*D1*P4*V4*hA*nR*qv*P^3*V^3 -
    2*P4*V4*hA*nR*nZ*nZ1*qv*P^3*V^3 - 2*P4*V4*hA*nR1*qv*P^3*V^3*nR^2*u^3 +
    2*D*D0*P4*V4*hA*nZ*qv*P^3*V^3 + 2*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^11 +
    2*P0*P4*V4*hA*nZ*P^2*V^3*qv^2*u^3 + 2*P4*V4*hA*nR*nR0*nZ*qv*P^3*V^3 +
    2*P4*V4*hA*nZ*qv*D^2*P^3*V^3*u^4 + 2*P4*V4*hA*nZ0*qv*P^3*V^3*nZ^2*u^3 +
    6*P0*P4*V4*hA*nZ*u*P^2*V^3*qv^2 + 6*P0*P4*V4*hA*nZ*P^2*V^3*qv^2*u^2 +
    6*P4*V4*hA*nZ0*qv*u*P^3*V^3*nZ^2 + 6*P4*V4*hA*nZ0*qv*P^3*V^3*nZ^2*u^2 +
    8*P4*V4*hA*nZ*qv*u*D^2*P^3*V^3 + 8*P4*V4*hA*nZ*qv*D^2*P^3*V^3*u^3 +
    12*P4*V4*hA*nZ*qv*D^2*P^3*V^3*u^2 + 22*P*P40*V*hA*nZ*qv*u*P4^2*V4^3 +
    22*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^10 + 110*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^2 +
    110*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^9 + 330*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^3 +
    330*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^8 + 660*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^4 +
    660*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^7 + 924*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^5 +
    924*P*P40*V*hA*nZ*qv*P4^2*V4^3*u^6 - 20*D*D1*P4*V4*hA*nR*qv*P^3*V^3*u^2 -
    20*D*D1*P4*V4*hA*nR*qv*P^3*V^3*u^3 - 10*D*D1*P4*V4*hA*nR*qv*u*P^3*V^3 -
    10*D*D1*P4*V4*hA*nR*qv*P^3*V^3*u^4 - 6*P4*V4*hA*nR*nZ*nZ1*qv*u*P^3*V^3 -
    6*P4*V4*hA*nR*nZ*nZ1*qv*P^3*V^3*u^2 - 2*D*D1*P4*V4*hA*nR*qv*P^3*V^3*u^5 -
    2*P4*V4*hA*nR*nZ*nZ1*qv*P^3*V^3*u^3 + 2*D*D0*P4*V4*hA*nZ*qv*P^3*V^3*u^5 +
    2*P4*V4*hA*nR*nR0*nZ*qv*P^3*V^3*u^3 + 6*P4*V4*hA*nR*nR0*nZ*qv*u*P^3*V^3 +
    6*P4*V4*hA*nR*nR0*nZ*qv*P^3*V^3*u^2 + 10*D*D0*P4*V4*hA*nZ*qv*u*P^3*V^3 +
    10*D*D0*P4*V4*hA*nZ*qv*P^3*V^3*u^4 + 20*D*D0*P4*V4*hA*nZ*qv*P^3*V^3*u^2 +
    20*D*D0*P4*V4*hA*nZ*qv*P^3*V^3*u^3) * hqph + (-16*D1*P*P4*V*V4*hA*qv*D^2 -
    4*D1*P0*P4*V*V4*hA*qv*D^2 + 4*P0*P4*V*V4*hA*nZph*qv*nZ^2 + 16*P*P4*V*V4*hA*nZph*qv*nZ^2 -
    320*D1*P*P4*V*V4*hA*qv*D^2*u^3 - 240*D1*P*P4*V*V4*hA*qv*D^2*u^2 -
    240*D1*P*P4*V*V4*hA*qv*D^2*u^4 - 140*D1*P0*P4*V*V4*hA*qv*D^2*u^3 -
    140*D1*P0*P4*V*V4*hA*qv*D^2*u^4 - 96*D1*P*P4*V*V4*hA*qv*u*D^2 - 96*D1*P*P4*V*V4*hA*qv*D^2*u^5 -
    84*D1*P0*P4*V*V4*hA*qv*D^2*u^2 - 84*D1*P0*P4*V*V4*hA*qv*D^2*u^5 - 28*D1*P0*P4*V*V4*hA*qv*u*D^2
    - 28*D1*P0*P4*V*V4*hA*qv*D^2*u^6 - 16*D*P*P4*V*V4*hA*nR*nR1*qv - 16*D*P*P4*V*V4*hA*nZ*nZ1*qv -
    16*D1*P*P4*V*V4*hA*qv*D^2*u^6 - 4*D*P0*P4*V*V4*hA*nR*nR1*qv - 4*D*P0*P4*V*V4*hA*nZ*nZ1*qv -
    4*D1*P0*P4*V*V4*hA*qv*D^2*u^7 + 4*D*Dph*P0*P4*V*V4*hA*nZ*qv + 4*P0*P4*V*V4*hA*nR*nRph*nZ*qv +
    4*P0*P4*V*V4*hA*nZph*qv*nZ^2*u^3 + 12*P0*P4*V*V4*hA*nZph*qv*u*nZ^2 +
    12*P0*P4*V*V4*hA*nZph*qv*nZ^2*u^2 + 16*D*Dph*P*P4*V*V4*hA*nZ*qv + 16*P*P4*V*V4*hA*nR*nRph*nZ*qv
    + 16*P*P4*V*V4*hA*nZph*qv*nZ^2*u^2 + 32*P*P4*V*V4*hA*nZph*qv*u*nZ^2 -
    96*D*P*P4*V*V4*hA*nR*nR1*qv*u^2 - 96*D*P*P4*V*V4*hA*nZ*nZ1*qv*u^2 -
    64*D*P*P4*V*V4*hA*nR*nR1*qv*u - 64*D*P*P4*V*V4*hA*nR*nR1*qv*u^3 - 64*D*P*P4*V*V4*hA*nZ*nZ1*qv*u
    - 64*D*P*P4*V*V4*hA*nZ*nZ1*qv*u^3 - 40*D*P0*P4*V*V4*hA*nR*nR1*qv*u^2 -
    40*D*P0*P4*V*V4*hA*nR*nR1*qv*u^3 - 40*D*P0*P4*V*V4*hA*nZ*nZ1*qv*u^2 -
    40*D*P0*P4*V*V4*hA*nZ*nZ1*qv*u^3 - 20*D*P0*P4*V*V4*hA*nR*nR1*qv*u -
    20*D*P0*P4*V*V4*hA*nR*nR1*qv*u^4 - 20*D*P0*P4*V*V4*hA*nZ*nZ1*qv*u -
    20*D*P0*P4*V*V4*hA*nZ*nZ1*qv*u^4 - 16*D*P*P4*V*V4*hA*nR*nR1*qv*u^4 -
    16*D*P*P4*V*V4*hA*nZ*nZ1*qv*u^4 - 4*D*P0*P4*V*V4*hA*nR*nR1*qv*u^5 -
    4*D*P0*P4*V*V4*hA*nZ*nZ1*qv*u^5 + 4*D*Dph*P0*P4*V*V4*hA*nZ*qv*u^5 +
    4*P0*P4*V*V4*hA*nR*nRph*nZ*qv*u^3 + 12*P0*P4*V*V4*hA*nR*nRph*nZ*qv*u +
    12*P0*P4*V*V4*hA*nR*nRph*nZ*qv*u^2 + 16*D*Dph*P*P4*V*V4*hA*nZ*qv*u^4 +
    16*P*P4*V*V4*hA*nR*nRph*nZ*qv*u^2 + 20*D*Dph*P0*P4*V*V4*hA*nZ*qv*u +
    20*D*Dph*P0*P4*V*V4*hA*nZ*qv*u^4 + 32*P*P4*V*V4*hA*nR*nRph*nZ*qv*u +
    40*D*Dph*P0*P4*V*V4*hA*nZ*qv*u^2 + 40*D*Dph*P0*P4*V*V4*hA*nZ*qv*u^3 +
    64*D*Dph*P*P4*V*V4*hA*nZ*qv*u + 64*D*Dph*P*P4*V*V4*hA*nZ*qv*u^3 +
    96*D*Dph*P*P4*V*V4*hA*nZ*qv*u^2) * hV + (-16*D1*P*P4*V*V4*hA*qv*D^2 - 4*D1*P*P40*V*V4*hA*qv*D^2
    + 4*P*P40*V*V4*hA*nZph*qv*nZ^2 + 16*P*P4*V*V4*hA*nZph*qv*nZ^2 - 320*D1*P*P4*V*V4*hA*qv*D^2*u^3
    - 240*D1*P*P4*V*V4*hA*qv*D^2*u^2 - 240*D1*P*P4*V*V4*hA*qv*D^2*u^4 -
    140*D1*P*P40*V*V4*hA*qv*D^2*u^3 - 140*D1*P*P40*V*V4*hA*qv*D^2*u^4 - 96*D1*P*P4*V*V4*hA*qv*u*D^2
    - 96*D1*P*P4*V*V4*hA*qv*D^2*u^5 - 84*D1*P*P40*V*V4*hA*qv*D^2*u^2 -
    84*D1*P*P40*V*V4*hA*qv*D^2*u^5 - 28*D1*P*P40*V*V4*hA*qv*u*D^2 - 28*D1*P*P40*V*V4*hA*qv*D^2*u^6
    - 16*D*P*P4*V*V4*hA*nR*nR1*qv - 16*D*P*P4*V*V4*hA*nZ*nZ1*qv - 16*D1*P*P4*V*V4*hA*qv*D^2*u^6 -
    4*D*P*P40*V*V4*hA*nR*nR1*qv - 4*D*P*P40*V*V4*hA*nZ*nZ1*qv - 4*D1*P*P40*V*V4*hA*qv*D^2*u^7 +
    4*D*Dph*P*P40*V*V4*hA*nZ*qv + 4*P*P40*V*V4*hA*nR*nRph*nZ*qv + 4*P*P40*V*V4*hA*nZph*qv*nZ^2*u^3
    + 12*P*P40*V*V4*hA*nZph*qv*u*nZ^2 + 12*P*P40*V*V4*hA*nZph*qv*nZ^2*u^2 +
    16*D*Dph*P*P4*V*V4*hA*nZ*qv + 16*P*P4*V*V4*hA*nR*nRph*nZ*qv + 16*P*P4*V*V4*hA*nZph*qv*nZ^2*u^2
    + 32*P*P4*V*V4*hA*nZph*qv*u*nZ^2 - 96*D*P*P4*V*V4*hA*nR*nR1*qv*u^2 -
    96*D*P*P4*V*V4*hA*nZ*nZ1*qv*u^2 - 64*D*P*P4*V*V4*hA*nR*nR1*qv*u -
    64*D*P*P4*V*V4*hA*nR*nR1*qv*u^3 - 64*D*P*P4*V*V4*hA*nZ*nZ1*qv*u -
    64*D*P*P4*V*V4*hA*nZ*nZ1*qv*u^3 - 40*D*P*P40*V*V4*hA*nR*nR1*qv*u^2 -
    40*D*P*P40*V*V4*hA*nR*nR1*qv*u^3 - 40*D*P*P40*V*V4*hA*nZ*nZ1*qv*u^2 -
    40*D*P*P40*V*V4*hA*nZ*nZ1*qv*u^3 - 20*D*P*P40*V*V4*hA*nR*nR1*qv*u -
    20*D*P*P40*V*V4*hA*nR*nR1*qv*u^4 - 20*D*P*P40*V*V4*hA*nZ*nZ1*qv*u -
    20*D*P*P40*V*V4*hA*nZ*nZ1*qv*u^4 - 16*D*P*P4*V*V4*hA*nR*nR1*qv*u^4 -
    16*D*P*P4*V*V4*hA*nZ*nZ1*qv*u^4 - 4*D*P*P40*V*V4*hA*nR*nR1*qv*u^5 -
    4*D*P*P40*V*V4*hA*nZ*nZ1*qv*u^5 + 4*D*Dph*P*P40*V*V4*hA*nZ*qv*u^5 +
    4*P*P40*V*V4*hA*nR*nRph*nZ*qv*u^3 + 12*P*P40*V*V4*hA*nR*nRph*nZ*qv*u +
    12*P*P40*V*V4*hA*nR*nRph*nZ*qv*u^2 + 16*D*Dph*P*P4*V*V4*hA*nZ*qv*u^4 +
    16*P*P4*V*V4*hA*nR*nRph*nZ*qv*u^2 + 20*D*Dph*P*P40*V*V4*hA*nZ*qv*u +
    20*D*Dph*P*P40*V*V4*hA*nZ*qv*u^4 + 32*P*P4*V*V4*hA*nR*nRph*nZ*qv*u +
    40*D*Dph*P*P40*V*V4*hA*nZ*qv*u^2 + 40*D*Dph*P*P40*V*V4*hA*nZ*qv*u^3 +
    64*D*Dph*P*P4*V*V4*hA*nZ*qv*u + 64*D*Dph*P*P4*V*V4*hA*nZ*qv*u^3 +
    96*D*Dph*P*P4*V*V4*hA*nZ*qv*u^2) * hV4 + (-16*D1*P*P4*V*V4*qv*D^2 - 2*D1*P*P40*V*V4*qv*D^2 -
    2*D1*P0*P4*V*V4*qv*D^2 + 2*P*P40*V*V4*nZph*qv*nZ^2 + 2*P0*P4*V*V4*nZph*qv*nZ^2 +
    16*P*P4*V*V4*nZph*qv*nZ^2 - 320*D1*P*P4*V*V4*qv*D^2*u^3 - 240*D1*P*P4*V*V4*qv*D^2*u^2 -
    240*D1*P*P4*V*V4*qv*D^2*u^4 - 96*D1*P*P4*V*V4*qv*u*D^2 - 96*D1*P*P4*V*V4*qv*D^2*u^5 -
    70*D1*P*P40*V*V4*qv*D^2*u^3 - 70*D1*P*P40*V*V4*qv*D^2*u^4 - 70*D1*P0*P4*V*V4*qv*D^2*u^3 -
    70*D1*P0*P4*V*V4*qv*D^2*u^4 - 42*D1*P*P40*V*V4*qv*D^2*u^2 - 42*D1*P*P40*V*V4*qv*D^2*u^5 -
    42*D1*P0*P4*V*V4*qv*D^2*u^2 - 42*D1*P0*P4*V*V4*qv*D^2*u^5 - 16*D*P*P4*V*V4*nR*nR1*qv -
    16*D*P*P4*V*V4*nZ*nZ1*qv - 16*D1*P*P4*V*V4*qv*D^2*u^6 - 14*D1*P*P40*V*V4*qv*u*D^2 -
    14*D1*P*P40*V*V4*qv*D^2*u^6 - 14*D1*P0*P4*V*V4*qv*u*D^2 - 14*D1*P0*P4*V*V4*qv*D^2*u^6 -
    2*D*P*P40*V*V4*nR*nR1*qv - 2*D*P*P40*V*V4*nZ*nZ1*qv - 2*D*P0*P4*V*V4*nR*nR1*qv -
    2*D*P0*P4*V*V4*nZ*nZ1*qv - 2*D1*P*P40*V*V4*qv*D^2*u^7 - 2*D1*P0*P4*V*V4*qv*D^2*u^7 +
    2*D*Dph*P*P40*V*V4*nZ*qv + 2*D*Dph*P0*P4*V*V4*nZ*qv + 2*P*P40*V*V4*nR*nRph*nZ*qv +
    2*P*P40*V*V4*nZph*qv*nZ^2*u^3 + 2*P0*P4*V*V4*nR*nRph*nZ*qv + 2*P0*P4*V*V4*nZph*qv*nZ^2*u^3 +
    6*P*P40*V*V4*nZph*qv*u*nZ^2 + 6*P*P40*V*V4*nZph*qv*nZ^2*u^2 + 6*P0*P4*V*V4*nZph*qv*u*nZ^2 +
    6*P0*P4*V*V4*nZph*qv*nZ^2*u^2 + 16*D*Dph*P*P4*V*V4*nZ*qv + 16*P*P4*V*V4*nR*nRph*nZ*qv +
    16*P*P4*V*V4*nZph*qv*nZ^2*u^2 + 32*P*P4*V*V4*nZph*qv*u*nZ^2 - 96*D*P*P4*V*V4*nR*nR1*qv*u^2 -
    96*D*P*P4*V*V4*nZ*nZ1*qv*u^2 - 64*D*P*P4*V*V4*nR*nR1*qv*u - 64*D*P*P4*V*V4*nR*nR1*qv*u^3 -
    64*D*P*P4*V*V4*nZ*nZ1*qv*u - 64*D*P*P4*V*V4*nZ*nZ1*qv*u^3 - 20*D*P*P40*V*V4*nR*nR1*qv*u^2 -
    20*D*P*P40*V*V4*nR*nR1*qv*u^3 - 20*D*P*P40*V*V4*nZ*nZ1*qv*u^2 - 20*D*P*P40*V*V4*nZ*nZ1*qv*u^3 -
    20*D*P0*P4*V*V4*nR*nR1*qv*u^2 - 20*D*P0*P4*V*V4*nR*nR1*qv*u^3 - 20*D*P0*P4*V*V4*nZ*nZ1*qv*u^2 -
    20*D*P0*P4*V*V4*nZ*nZ1*qv*u^3 - 16*D*P*P4*V*V4*nR*nR1*qv*u^4 - 16*D*P*P4*V*V4*nZ*nZ1*qv*u^4 -
    10*D*P*P40*V*V4*nR*nR1*qv*u - 10*D*P*P40*V*V4*nR*nR1*qv*u^4 - 10*D*P*P40*V*V4*nZ*nZ1*qv*u -
    10*D*P*P40*V*V4*nZ*nZ1*qv*u^4 - 10*D*P0*P4*V*V4*nR*nR1*qv*u - 10*D*P0*P4*V*V4*nR*nR1*qv*u^4 -
    10*D*P0*P4*V*V4*nZ*nZ1*qv*u - 10*D*P0*P4*V*V4*nZ*nZ1*qv*u^4 - 2*D*P*P40*V*V4*nR*nR1*qv*u^5 -
    2*D*P*P40*V*V4*nZ*nZ1*qv*u^5 - 2*D*P0*P4*V*V4*nR*nR1*qv*u^5 - 2*D*P0*P4*V*V4*nZ*nZ1*qv*u^5 +
    2*D*Dph*P*P40*V*V4*nZ*qv*u^5 + 2*D*Dph*P0*P4*V*V4*nZ*qv*u^5 + 2*P*P40*V*V4*nR*nRph*nZ*qv*u^3 +
    2*P0*P4*V*V4*nR*nRph*nZ*qv*u^3 + 6*P*P40*V*V4*nR*nRph*nZ*qv*u + 6*P*P40*V*V4*nR*nRph*nZ*qv*u^2
    + 6*P0*P4*V*V4*nR*nRph*nZ*qv*u + 6*P0*P4*V*V4*nR*nRph*nZ*qv*u^2 + 10*D*Dph*P*P40*V*V4*nZ*qv*u +
    10*D*Dph*P*P40*V*V4*nZ*qv*u^4 + 10*D*Dph*P0*P4*V*V4*nZ*qv*u + 10*D*Dph*P0*P4*V*V4*nZ*qv*u^4 +
    16*D*Dph*P*P4*V*V4*nZ*qv*u^4 + 16*P*P4*V*V4*nR*nRph*nZ*qv*u^2 + 20*D*Dph*P*P40*V*V4*nZ*qv*u^2 +
    20*D*Dph*P*P40*V*V4*nZ*qv*u^3 + 20*D*Dph*P0*P4*V*V4*nZ*qv*u^2 + 20*D*Dph*P0*P4*V*V4*nZ*qv*u^3 +
    32*P*P4*V*V4*nR*nRph*nZ*qv*u + 64*D*Dph*P*P4*V*V4*nZ*qv*u + 64*D*Dph*P*P4*V*V4*nZ*qv*u^3 +
    96*D*Dph*P*P4*V*V4*nZ*qv*u^2) * h_half

set_option linter.unusedSimpArgs false in
/-- `|B| · ½W³κ_D = R ∂_u|B| · R²W n_z − R² ∂_z|B| · R W n_R`
(the `D`-component of `|B| ½W³κ = R³W ∇|B| × (…)`). -/
theorem gcMu_bmY_a (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)
    (hV4 : PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1) :
    PolyExprS.eval (xB u z) eBm * PolyExprS.eval (xB u z) eYD =
      (1 + u) * PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm * PolyExprS.eval (xB u z) eXb -
      (1 + u) ^ 2 * PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm * PolyExprS.eval (xB u z) eXa := by
  simp only [deriv_eBm]
  simp only [deriv_single, deriv_phiDir]
  simp only [eval_eBm, eval_eYD, eval_eYR, eval_eYZ, eval_eXa, eval_eXb, eval_eXc]
  have h_Q := QPP4_val (xB u z)
  have h_Q0 := QPP4_d0 (xB u z)
  have h_Q1 := QPP4_d1 (xB u z)
  have h_E := E_val (xB u z)
  have h_E0 := E_d0 (xB u z)
  have h_E1 := E_d1 (xB u z)
  have h_E4 := E4_val (xB u z)
  have h_E40 := E4_d0 (xB u z)
  have h_E41 := E4_d1 (xB u z)
  have h_P1 := P_d1 (xB u z)
  have h_P41 := P4_d1 (xB u z)
  have hq := gc_eval_eq u z
  have hKD := gc_eval_eKD u z
  have hqR := gc_eval_eqR u z
  have hqz := gc_eval_eqz u z
  have hW3 := gc_eval_eW3 u z
  have h_half := half_rel
  simp only [xB_zero] at *
  rw [← hq] at h_Q h_Q0 h_Q1 h_E h_E0 h_E1
  rw [h_E] at hV
  rw [h_E4] at hV4
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  linear_combination (-P*V4*nZ*V^2 - P*V4*nZ*V^2*u^3 - 3*P*V4*nZ*u*V^2 - 3*P*V4*nZ*V^2*u^2) * h_Q0
    + (P*V4*nR*V^2 + P*V4*nR*V^2*u^3 + 3*P*V4*nR*u*V^2 + 3*P*V4*nR*V^2*u^2) * h_Q1 + (KD*V*V4*W3*hA
    + E0*P*V4*hA*nZ*V^4 + E40*P*hA*nZ*V^2*V4^3 - E1*P*V4*hA*nR*V^4 - E41*P*hA*nR*V^2*V4^3 +
    E0*P*V4*hA*nZ*V^4*u^3 + E40*P*hA*nZ*V^2*V4^3*u^3 - E1*P*V4*hA*nR*V^4*u^3 -
    E41*P*hA*nR*V^2*V4^3*u^3 - 3*E1*P*V4*hA*nR*u*V^4 - 3*E1*P*V4*hA*nR*V^4*u^2 -
    3*E41*P*hA*nR*u*V^2*V4^3 - 3*E41*P*hA*nR*V^2*V4^3*u^2 + 3*E0*P*V4*hA*nZ*u*V^4 +
    3*E0*P*V4*hA*nZ*V^4*u^2 + 3*E40*P*hA*nZ*u*V^2*V4^3 + 3*E40*P*hA*nZ*V^2*V4^3*u^2) * h_Q +
    (P4*V4*hA*nZ*qv*P^2*V^4 + P4*V4*hA*nZ*qv*P^2*V^4*u^3 + 3*P4*V4*hA*nZ*qv*u*P^2*V^4 +
    3*P4*V4*hA*nZ*qv*P^2*V^4*u^2) * h_E0 + (-P4*V4*hA*nR*qv*P^2*V^4 - P4*V4*hA*nR*qv*P^2*V^4*u^3 -
    3*P4*V4*hA*nR*qv*u*P^2*V^4 - 3*P4*V4*hA*nR*qv*P^2*V^4*u^2) * h_E1 + (P4*hA*nZ*qv*P^2*V^2*V4^3 +
    P4*hA*nZ*qv*P^2*V^2*V4^3*u^3 + 3*P4*hA*nZ*qv*u*P^2*V^2*V4^3 + 3*P4*hA*nZ*qv*P^2*V^2*V4^3*u^2) *
    h_E40 + (-P4*hA*nR*qv*P^2*V^2*V4^3 - P4*hA*nR*qv*P^2*V^2*V4^3*u^3 -
    3*P4*hA*nR*qv*u*P^2*V^2*V4^3 - 3*P4*hA*nR*qv*P^2*V^2*V4^3*u^2) * h_E41 + (P*P4*V4*nR*qv*V^2 +
    P*P4*V4*nR*qv*V^2*u^3 - 2*P4*V4*hA*nR*P^3*V^4*qv^2 + 3*P*P4*V4*nR*qv*u*V^2 +
    3*P*P4*V4*nR*qv*V^2*u^2 - 6*P4*V4*hA*nR*u*P^3*V^4*qv^2 - 6*P4*V4*hA*nR*P^3*V^4*qv^2*u^2 -
    2*P4*V4*hA*nR*P^3*V^4*qv^2*u^3) * h_P1 + (V4*nR*qv*P^2*V^2 + V4*nR*qv*P^2*V^2*u^3 +
    3*V4*nR*qv*u*P^2*V^2 + 3*V4*nR*qv*P^2*V^2*u^2) * h_P41 + (KD*P*P4*V*V4*hA*qv) * hW3 +
    (P4*V4*hA*qv*P^4*V^4) * hKD + (P4*V4*hA*nZ*qv*P^4*V^4 + P4*V4*hA*nZ*qv*P^4*V^4*u^3 +
    3*P4*V4*hA*nZ*qv*u*P^4*V^4 + 3*P4*V4*hA*nZ*qv*P^4*V^4*u^2) * hqR + (-P4*V4*hA*nR*qv*P^4*V^4 -
    P4*V4*hA*nR*qv*P^4*V^4*u^3 - 3*P4*V4*hA*nR*qv*u*P^4*V^4 - 3*P4*V4*hA*nR*qv*P^4*V^4*u^2) * hqz +
    (-P40*V4*nZ - P40*V4*nZ*u^3 - 8*P4*V4*hA*nZ - 3*P40*V4*nZ*u - 3*P40*V4*nZ*u^2 +
    8*hA*nZ*P4^3*V4^3 - 16*P4*V4*hA*nZ*u - 8*P4*V4*hA*nZ*u^2 + 2*P40*hA*nZ*P4^2*V4^3 +
    8*hA*nZ*P4^3*V4^3*u^10 + 80*hA*nZ*u*P4^3*V4^3 + 80*hA*nZ*P4^3*V4^3*u^9 +
    360*hA*nZ*P4^3*V4^3*u^2 + 360*hA*nZ*P4^3*V4^3*u^8 + 960*hA*nZ*P4^3*V4^3*u^3 +
    960*hA*nZ*P4^3*V4^3*u^7 + 1680*hA*nZ*P4^3*V4^3*u^4 + 1680*hA*nZ*P4^3*V4^3*u^6 +
    2016*hA*nZ*P4^3*V4^3*u^5 + 2*P40*hA*nZ*P4^2*V4^3*u^11 + 22*P40*hA*nZ*u*P4^2*V4^3 +
    22*P40*hA*nZ*P4^2*V4^3*u^10 + 110*P40*hA*nZ*P4^2*V4^3*u^2 + 110*P40*hA*nZ*P4^2*V4^3*u^9 +
    330*P40*hA*nZ*P4^2*V4^3*u^3 + 330*P40*hA*nZ*P4^2*V4^3*u^8 + 660*P40*hA*nZ*P4^2*V4^3*u^4 +
    660*P40*hA*nZ*P4^2*V4^3*u^7 + 924*P40*hA*nZ*P4^2*V4^3*u^5 + 924*P40*hA*nZ*P4^2*V4^3*u^6 -
    8*P4*V4*hA*nZ*qv*P^2*V^2 - 4*P4*V4*hA*nR1*P^2*V^2*nR^2 + 4*P4*V4*hA*nZ*D^2*P^2*V^2 +
    4*P4*V4*hA*nZ0*P^2*V^2*nZ^2 - 16*P4*V4*hA*nZ*qv*u*P^2*V^2 - 12*P4*V4*hA*nR1*u*P^2*V^2*nR^2 -
    12*P4*V4*hA*nR1*P^2*V^2*nR^2*u^2 - 8*P4*V4*hA*nZ*qv*P^2*V^2*u^2 - 4*D*D1*P4*V4*hA*nR*P^2*V^2 -
    4*P4*V4*hA*nR*nZ*nZ1*P^2*V^2 - 4*P4*V4*hA*nR1*P^2*V^2*nR^2*u^3 + 2*P*P0*P4*V4*hA*nZ*qv*V^2 +
    4*D*D0*P4*V4*hA*nZ*P^2*V^2 + 4*P4*V4*hA*nR*nR0*nZ*P^2*V^2 + 4*P4*V4*hA*nZ*D^2*P^2*V^2*u^4 +
    4*P4*V4*hA*nZ0*P^2*V^2*nZ^2*u^3 + 12*P4*V4*hA*nZ0*u*P^2*V^2*nZ^2 +
    12*P4*V4*hA*nZ0*P^2*V^2*nZ^2*u^2 + 16*P4*V4*hA*nZ*u*D^2*P^2*V^2 +
    16*P4*V4*hA*nZ*D^2*P^2*V^2*u^3 + 24*P4*V4*hA*nZ*D^2*P^2*V^2*u^2 -
    40*D*D1*P4*V4*hA*nR*P^2*V^2*u^2 - 40*D*D1*P4*V4*hA*nR*P^2*V^2*u^3 -
    20*D*D1*P4*V4*hA*nR*u*P^2*V^2 - 20*D*D1*P4*V4*hA*nR*P^2*V^2*u^4 -
    12*P4*V4*hA*nR*nZ*nZ1*u*P^2*V^2 - 12*P4*V4*hA*nR*nZ*nZ1*P^2*V^2*u^2 -
    4*D*D1*P4*V4*hA*nR*P^2*V^2*u^5 - 4*P4*V4*hA*nR*nZ*nZ1*P^2*V^2*u^3 +
    2*P*P0*P4*V4*hA*nZ*qv*V^2*u^3 + 4*D*D0*P4*V4*hA*nZ*P^2*V^2*u^5 +
    4*P4*V4*hA*nR*nR0*nZ*P^2*V^2*u^3 + 6*P*P0*P4*V4*hA*nZ*qv*u*V^2 + 6*P*P0*P4*V4*hA*nZ*qv*V^2*u^2
    + 12*P4*V4*hA*nR*nR0*nZ*u*P^2*V^2 + 12*P4*V4*hA*nR*nR0*nZ*P^2*V^2*u^2 +
    20*D*D0*P4*V4*hA*nZ*u*P^2*V^2 + 20*D*D0*P4*V4*hA*nZ*P^2*V^2*u^4 +
    40*D*D0*P4*V4*hA*nZ*P^2*V^2*u^2 + 40*D*D0*P4*V4*hA*nZ*P^2*V^2*u^3) * hV + (2*P40*V4*hA*nZ +
    8*P4*V4*hA*nZ + 2*P40*V4*hA*nZ*u^3 + 6*P40*V4*hA*nZ*u + 6*P40*V4*hA*nZ*u^2 + 8*P4*V4*hA*nZ*u^2
    + 16*P4*V4*hA*nZ*u) * hV4 + (P40*V4*nZ + P40*V4*nZ*u^3 + 3*P40*V4*nZ*u + 3*P40*V4*nZ*u^2 -
    2*P4*V4*nR1*P^2*V^2*nR^2 + 2*P4*V4*nZ*D^2*P^2*V^2 + 2*P4*V4*nZ0*P^2*V^2*nZ^2 +
    P*P0*P4*V4*nZ*qv*V^2 - 6*P4*V4*nR1*u*P^2*V^2*nR^2 - 6*P4*V4*nR1*P^2*V^2*nR^2*u^2 -
    2*D*D1*P4*V4*nR*P^2*V^2 - 2*P4*V4*nR*nZ*nZ1*P^2*V^2 - 2*P4*V4*nR1*P^2*V^2*nR^2*u^3 +
    2*D*D0*P4*V4*nZ*P^2*V^2 + 2*P4*V4*nR*nR0*nZ*P^2*V^2 + 2*P4*V4*nZ*D^2*P^2*V^2*u^4 +
    2*P4*V4*nZ0*P^2*V^2*nZ^2*u^3 + 6*P4*V4*nZ0*u*P^2*V^2*nZ^2 + 6*P4*V4*nZ0*P^2*V^2*nZ^2*u^2 +
    8*P4*V4*nZ*u*D^2*P^2*V^2 + 8*P4*V4*nZ*D^2*P^2*V^2*u^3 + 12*P4*V4*nZ*D^2*P^2*V^2*u^2 +
    P*P0*P4*V4*nZ*qv*V^2*u^3 - 20*D*D1*P4*V4*nR*P^2*V^2*u^2 - 20*D*D1*P4*V4*nR*P^2*V^2*u^3 -
    10*D*D1*P4*V4*nR*u*P^2*V^2 - 10*D*D1*P4*V4*nR*P^2*V^2*u^4 - 6*P4*V4*nR*nZ*nZ1*u*P^2*V^2 -
    6*P4*V4*nR*nZ*nZ1*P^2*V^2*u^2 - 2*D*D1*P4*V4*nR*P^2*V^2*u^5 - 2*P4*V4*nR*nZ*nZ1*P^2*V^2*u^3 +
    2*D*D0*P4*V4*nZ*P^2*V^2*u^5 + 2*P4*V4*nR*nR0*nZ*P^2*V^2*u^3 + 3*P*P0*P4*V4*nZ*qv*u*V^2 +
    3*P*P0*P4*V4*nZ*qv*V^2*u^2 + 6*P4*V4*nR*nR0*nZ*u*P^2*V^2 + 6*P4*V4*nR*nR0*nZ*P^2*V^2*u^2 +
    10*D*D0*P4*V4*nZ*u*P^2*V^2 + 10*D*D0*P4*V4*nZ*P^2*V^2*u^4 + 20*D*D0*P4*V4*nZ*P^2*V^2*u^2 +
    20*D*D0*P4*V4*nZ*P^2*V^2*u^3) * h_half

set_option linter.unusedSimpArgs false in
/-- `|B| · ½W³κ_z = R² ∂_φ|B| · R W n_R − R³ ∂_u|B| · R² W D`. -/
theorem gcMu_bmY_b (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)
    (hV4 : PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1) :
    PolyExprS.eval (xB u z) eBm * PolyExprS.eval (xB u z) eYZ =
      (1 + u) ^ 2 * PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm * PolyExprS.eval (xB u z) eXa -
      (1 + u) ^ 3 * PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm * PolyExprS.eval (xB u z) eXc := by
  simp only [deriv_eBm]
  simp only [deriv_single, deriv_phiDir]
  simp only [eval_eBm, eval_eYD, eval_eYR, eval_eYZ, eval_eXa, eval_eXb, eval_eXc]
  have h_Q := QPP4_val (xB u z)
  have h_Q0 := QPP4_d0 (xB u z)
  have h_Qph := QPP4_dph (xB u z)
  have h_E := E_val (xB u z)
  have h_E0 := E_d0 (xB u z)
  have h_Eph := E_dph (xB u z)
  have h_E4 := E4_val (xB u z)
  have h_E40 := E4_d0 (xB u z)
  have h_E4ph := E4_dph (xB u z)
  have h_Pph := P_dph (xB u z)
  have h_P4ph := P4_dph (xB u z)
  have hq := gc_eval_eq u z
  have hKZ := gc_eval_eKZ u z
  have hqR := gc_eval_eqR u z
  have hqph := gc_eval_eqph u z
  have hW3 := gc_eval_eW3 u z
  have h_half := half_rel
  simp only [xB_zero] at *
  rw [← hq] at h_Q h_Q0 h_Qph h_E h_E0 h_Eph
  rw [h_E] at hV
  rw [h_E4] at hV4
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  linear_combination (D*P*V4*V^2 + D*P*V4*V^2*u^5 + 5*D*P*V4*u*V^2 + 5*D*P*V4*V^2*u^4 +
    10*D*P*V4*V^2*u^2 + 10*D*P*V4*V^2*u^3) * h_Q0 + (-P*V4*nR*V^2 - P*V4*nR*V^2*u^3 -
    3*P*V4*nR*u*V^2 - 3*P*V4*nR*V^2*u^2) * h_Qph + (KZ*V*V4*W3*hA + E4ph*P*hA*nR*V^2*V4^3 +
    Eph*P*V4*hA*nR*V^4 - D*E0*P*V4*hA*V^4 - D*E40*P*hA*V^2*V4^3 + E4ph*P*hA*nR*V^2*V4^3*u^3 +
    Eph*P*V4*hA*nR*V^4*u^3 - D*E0*P*V4*hA*V^4*u^5 - D*E40*P*hA*V^2*V4^3*u^5 -
    10*D*E0*P*V4*hA*V^4*u^2 - 10*D*E0*P*V4*hA*V^4*u^3 - 10*D*E40*P*hA*V^2*V4^3*u^2 -
    10*D*E40*P*hA*V^2*V4^3*u^3 - 5*D*E0*P*V4*hA*u*V^4 - 5*D*E0*P*V4*hA*V^4*u^4 -
    5*D*E40*P*hA*u*V^2*V4^3 - 5*D*E40*P*hA*V^2*V4^3*u^4 + 3*E4ph*P*hA*nR*u*V^2*V4^3 +
    3*E4ph*P*hA*nR*V^2*V4^3*u^2 + 3*Eph*P*V4*hA*nR*u*V^4 + 3*Eph*P*V4*hA*nR*V^4*u^2) * h_Q +
    (-D*P4*V4*hA*qv*P^2*V^4 - D*P4*V4*hA*qv*P^2*V^4*u^5 - 10*D*P4*V4*hA*qv*P^2*V^4*u^2 -
    10*D*P4*V4*hA*qv*P^2*V^4*u^3 - 5*D*P4*V4*hA*qv*u*P^2*V^4 - 5*D*P4*V4*hA*qv*P^2*V^4*u^4) * h_E0
    + (P4*V4*hA*nR*qv*P^2*V^4 + P4*V4*hA*nR*qv*P^2*V^4*u^3 + 3*P4*V4*hA*nR*qv*u*P^2*V^4 +
    3*P4*V4*hA*nR*qv*P^2*V^4*u^2) * h_Eph + (-D*P4*hA*qv*P^2*V^2*V4^3 - D*P4*hA*qv*P^2*V^2*V4^3*u^5
    - 10*D*P4*hA*qv*P^2*V^2*V4^3*u^2 - 10*D*P4*hA*qv*P^2*V^2*V4^3*u^3 - 5*D*P4*hA*qv*u*P^2*V^2*V4^3
    - 5*D*P4*hA*qv*P^2*V^2*V4^3*u^4) * h_E40 + (P4*hA*nR*qv*P^2*V^2*V4^3 +
    P4*hA*nR*qv*P^2*V^2*V4^3*u^3 + 3*P4*hA*nR*qv*u*P^2*V^2*V4^3 + 3*P4*hA*nR*qv*P^2*V^2*V4^3*u^2) *
    h_E4ph + (-P*P4*V4*nR*qv*V^2 - P*P4*V4*nR*qv*V^2*u^3 - 3*P*P4*V4*nR*qv*u*V^2 -
    3*P*P4*V4*nR*qv*V^2*u^2 + 2*P4*V4*hA*nR*P^3*V^4*qv^2 + 2*P4*V4*hA*nR*P^3*V^4*qv^2*u^3 +
    6*P4*V4*hA*nR*u*P^3*V^4*qv^2 + 6*P4*V4*hA*nR*P^3*V^4*qv^2*u^2) * h_Pph + (-V4*nR*qv*P^2*V^2 -
    V4*nR*qv*P^2*V^2*u^3 - 3*V4*nR*qv*u*P^2*V^2 - 3*V4*nR*qv*P^2*V^2*u^2) * h_P4ph +
    (KZ*P*P4*V*V4*hA*qv) * hW3 + (P4*V4*hA*qv*P^4*V^4) * hKZ + (-D*P4*V4*hA*qv*P^4*V^4 -
    D*P4*V4*hA*qv*P^4*V^4*u^5 - 10*D*P4*V4*hA*qv*P^4*V^4*u^2 - 10*D*P4*V4*hA*qv*P^4*V^4*u^3 -
    5*D*P4*V4*hA*qv*u*P^4*V^4 - 5*D*P4*V4*hA*qv*P^4*V^4*u^4) * hqR + (P4*V4*hA*nR*qv*P^4*V^4 +
    P4*V4*hA*nR*qv*P^4*V^4*u^3 + 3*P4*V4*hA*nR*qv*u*P^4*V^4 + 3*P4*V4*hA*nR*qv*P^4*V^4*u^2) * hqph
    + (D*P40*V4 + D*P40*V4*u^5 - 8*D*hA*P4^3*V4^3 + 5*D*P40*V4*u + 5*D*P40*V4*u^4 + 8*D*P4*V4*hA +
    10*D*P40*V4*u^2 + 10*D*P40*V4*u^3 - 7392*D*hA*P4^3*V4^3*u^6 - 6336*D*hA*P4^3*V4^3*u^5 -
    6336*D*hA*P4^3*V4^3*u^7 - 3960*D*hA*P4^3*V4^3*u^4 - 3960*D*hA*P4^3*V4^3*u^8 -
    1760*D*hA*P4^3*V4^3*u^3 - 1760*D*hA*P4^3*V4^3*u^9 - 528*D*hA*P4^3*V4^3*u^2 -
    528*D*hA*P4^3*V4^3*u^10 - 96*D*hA*u*P4^3*V4^3 - 96*D*hA*P4^3*V4^3*u^11 - 8*D*hA*P4^3*V4^3*u^12
    - 2*D*P40*hA*P4^2*V4^3 + 8*D*P4*V4*hA*u^4 + 32*D*P4*V4*hA*u + 32*D*P4*V4*hA*u^3 +
    48*D*P4*V4*hA*u^2 - 3432*D*P40*hA*P4^2*V4^3*u^6 - 3432*D*P40*hA*P4^2*V4^3*u^7 -
    2574*D*P40*hA*P4^2*V4^3*u^5 - 2574*D*P40*hA*P4^2*V4^3*u^8 - 1430*D*P40*hA*P4^2*V4^3*u^4 -
    1430*D*P40*hA*P4^2*V4^3*u^9 - 572*D*P40*hA*P4^2*V4^3*u^3 - 572*D*P40*hA*P4^2*V4^3*u^10 -
    156*D*P40*hA*P4^2*V4^3*u^2 - 156*D*P40*hA*P4^2*V4^3*u^11 - 26*D*P40*hA*u*P4^2*V4^3 -
    26*D*P40*hA*P4^2*V4^3*u^12 - 4*P4*V4*hA*D^3*P^2*V^2 - 2*D*P40*hA*P4^2*V4^3*u^13 -
    80*P4*V4*hA*D^3*P^2*V^2*u^3 - 60*P4*V4*hA*D^3*P^2*V^2*u^2 - 60*P4*V4*hA*D^3*P^2*V^2*u^4 -
    24*P4*V4*hA*u*D^3*P^2*V^2 - 24*P4*V4*hA*D^3*P^2*V^2*u^5 - 4*D0*P4*V4*hA*D^2*P^2*V^2 -
    4*P4*V4*hA*D^3*P^2*V^2*u^6 + 4*P4*V4*hA*nRph*P^2*V^2*nR^2 + 8*D*P4*V4*hA*qv*P^2*V^2 -
    140*D0*P4*V4*hA*D^2*P^2*V^2*u^3 - 140*D0*P4*V4*hA*D^2*P^2*V^2*u^4 -
    84*D0*P4*V4*hA*D^2*P^2*V^2*u^2 - 84*D0*P4*V4*hA*D^2*P^2*V^2*u^5 - 28*D0*P4*V4*hA*u*D^2*P^2*V^2
    - 28*D0*P4*V4*hA*D^2*P^2*V^2*u^6 - 4*D*P4*V4*hA*nR*nR0*P^2*V^2 - 4*D*P4*V4*hA*nZ*nZ0*P^2*V^2 -
    4*D0*P4*V4*hA*D^2*P^2*V^2*u^7 - 2*D*P*P0*P4*V4*hA*qv*V^2 + 4*D*Dph*P4*V4*hA*nR*P^2*V^2 +
    4*P4*V4*hA*nR*nZ*nZph*P^2*V^2 + 4*P4*V4*hA*nRph*P^2*V^2*nR^2*u^3 + 8*D*P4*V4*hA*qv*P^2*V^2*u^4
    + 12*P4*V4*hA*nRph*u*P^2*V^2*nR^2 + 12*P4*V4*hA*nRph*P^2*V^2*nR^2*u^2 +
    32*D*P4*V4*hA*qv*u*P^2*V^2 + 32*D*P4*V4*hA*qv*P^2*V^2*u^3 + 48*D*P4*V4*hA*qv*P^2*V^2*u^2 -
    40*D*P4*V4*hA*nR*nR0*P^2*V^2*u^2 - 40*D*P4*V4*hA*nR*nR0*P^2*V^2*u^3 -
    40*D*P4*V4*hA*nZ*nZ0*P^2*V^2*u^2 - 40*D*P4*V4*hA*nZ*nZ0*P^2*V^2*u^3 -
    20*D*P*P0*P4*V4*hA*qv*V^2*u^2 - 20*D*P*P0*P4*V4*hA*qv*V^2*u^3 - 20*D*P4*V4*hA*nR*nR0*u*P^2*V^2
    - 20*D*P4*V4*hA*nR*nR0*P^2*V^2*u^4 - 20*D*P4*V4*hA*nZ*nZ0*u*P^2*V^2 -
    20*D*P4*V4*hA*nZ*nZ0*P^2*V^2*u^4 - 10*D*P*P0*P4*V4*hA*qv*u*V^2 - 10*D*P*P0*P4*V4*hA*qv*V^2*u^4
    - 4*D*P4*V4*hA*nR*nR0*P^2*V^2*u^5 - 4*D*P4*V4*hA*nZ*nZ0*P^2*V^2*u^5 -
    2*D*P*P0*P4*V4*hA*qv*V^2*u^5 + 4*D*Dph*P4*V4*hA*nR*P^2*V^2*u^5 +
    4*P4*V4*hA*nR*nZ*nZph*P^2*V^2*u^3 + 12*P4*V4*hA*nR*nZ*nZph*u*P^2*V^2 +
    12*P4*V4*hA*nR*nZ*nZph*P^2*V^2*u^2 + 20*D*Dph*P4*V4*hA*nR*u*P^2*V^2 +
    20*D*Dph*P4*V4*hA*nR*P^2*V^2*u^4 + 40*D*Dph*P4*V4*hA*nR*P^2*V^2*u^2 +
    40*D*Dph*P4*V4*hA*nR*P^2*V^2*u^3) * hV + (-8*D*P4*V4*hA - 2*D*P40*V4*hA - 48*D*P4*V4*hA*u^2 -
    32*D*P4*V4*hA*u - 32*D*P4*V4*hA*u^3 - 20*D*P40*V4*hA*u^2 - 20*D*P40*V4*hA*u^3 -
    10*D*P40*V4*hA*u - 10*D*P40*V4*hA*u^4 - 8*D*P4*V4*hA*u^4 - 2*D*P40*V4*hA*u^5) * hV4 +
    (-D*P40*V4 - D*P40*V4*u^5 - 10*D*P40*V4*u^2 - 10*D*P40*V4*u^3 - 5*D*P40*V4*u - 5*D*P40*V4*u^4 -
    2*P4*V4*D^3*P^2*V^2 - 40*P4*V4*D^3*P^2*V^2*u^3 - 30*P4*V4*D^3*P^2*V^2*u^2 -
    30*P4*V4*D^3*P^2*V^2*u^4 - 12*P4*V4*u*D^3*P^2*V^2 - 12*P4*V4*D^3*P^2*V^2*u^5 -
    2*D0*P4*V4*D^2*P^2*V^2 - 2*P4*V4*D^3*P^2*V^2*u^6 + 2*P4*V4*nRph*P^2*V^2*nR^2 -
    D*P*P0*P4*V4*qv*V^2 - 70*D0*P4*V4*D^2*P^2*V^2*u^3 - 70*D0*P4*V4*D^2*P^2*V^2*u^4 -
    42*D0*P4*V4*D^2*P^2*V^2*u^2 - 42*D0*P4*V4*D^2*P^2*V^2*u^5 - 14*D0*P4*V4*u*D^2*P^2*V^2 -
    14*D0*P4*V4*D^2*P^2*V^2*u^6 - 2*D*P4*V4*nR*nR0*P^2*V^2 - 2*D*P4*V4*nZ*nZ0*P^2*V^2 -
    2*D0*P4*V4*D^2*P^2*V^2*u^7 + 2*D*Dph*P4*V4*nR*P^2*V^2 + 2*P4*V4*nR*nZ*nZph*P^2*V^2 +
    2*P4*V4*nRph*P^2*V^2*nR^2*u^3 + 6*P4*V4*nRph*u*P^2*V^2*nR^2 + 6*P4*V4*nRph*P^2*V^2*nR^2*u^2 -
    D*P*P0*P4*V4*qv*V^2*u^5 - 20*D*P4*V4*nR*nR0*P^2*V^2*u^2 - 20*D*P4*V4*nR*nR0*P^2*V^2*u^3 -
    20*D*P4*V4*nZ*nZ0*P^2*V^2*u^2 - 20*D*P4*V4*nZ*nZ0*P^2*V^2*u^3 - 10*D*P*P0*P4*V4*qv*V^2*u^2 -
    10*D*P*P0*P4*V4*qv*V^2*u^3 - 10*D*P4*V4*nR*nR0*u*P^2*V^2 - 10*D*P4*V4*nR*nR0*P^2*V^2*u^4 -
    10*D*P4*V4*nZ*nZ0*u*P^2*V^2 - 10*D*P4*V4*nZ*nZ0*P^2*V^2*u^4 - 5*D*P*P0*P4*V4*qv*u*V^2 -
    5*D*P*P0*P4*V4*qv*V^2*u^4 - 2*D*P4*V4*nR*nR0*P^2*V^2*u^5 - 2*D*P4*V4*nZ*nZ0*P^2*V^2*u^5 +
    2*D*Dph*P4*V4*nR*P^2*V^2*u^5 + 2*P4*V4*nR*nZ*nZph*P^2*V^2*u^3 + 6*P4*V4*nR*nZ*nZph*u*P^2*V^2 +
    6*P4*V4*nR*nZ*nZph*P^2*V^2*u^2 + 10*D*Dph*P4*V4*nR*u*P^2*V^2 + 10*D*Dph*P4*V4*nR*P^2*V^2*u^4 +
    20*D*Dph*P4*V4*nR*P^2*V^2*u^2 + 20*D*Dph*P4*V4*nR*P^2*V^2*u^3) * h_half

set_option linter.unusedSimpArgs false in
/-- `|B| · ½W³κ_R = −(R ∂_φ|B| · R² W n_z − R³ ∂_z|B| · R² W D)`. -/
theorem gcMu_bmY_c (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1) :
    PolyExprS.eval (xB u z) eBm * PolyExprS.eval (xB u z) eYR =
      -((1 + u) * PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm * PolyExprS.eval (xB u z) eXb -
      (1 + u) ^ 3 * PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm *
        PolyExprS.eval (xB u z) eXc) := by
  simp only [deriv_eBm]
  simp only [deriv_single, deriv_phiDir]
  simp only [eval_eBm, eval_eYD, eval_eYR, eval_eYZ, eval_eXa, eval_eXb, eval_eXc]
  have h_Q := QPP4_val (xB u z)
  have h_Q1 := QPP4_d1 (xB u z)
  have h_Qph := QPP4_dph (xB u z)
  have h_E := E_val (xB u z)
  have h_E1 := E_d1 (xB u z)
  have h_Eph := E_dph (xB u z)
  have h_E41 := E4_d1 (xB u z)
  have h_E4ph := E4_dph (xB u z)
  have h_P1 := P_d1 (xB u z)
  have h_Pph := P_dph (xB u z)
  have h_P41 := P4_d1 (xB u z)
  have h_P4ph := P4_dph (xB u z)
  have hq := gc_eval_eq u z
  have hKR := gc_eval_eKR u z
  have hqz := gc_eval_eqz u z
  have hqph := gc_eval_eqph u z
  have hW3 := gc_eval_eW3 u z
  have h_half := half_rel
  simp only [xB_zero] at *
  rw [← hq] at h_Q h_Q1 h_Qph h_E h_E1 h_Eph
  rw [h_E] at hV
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  linear_combination (-D*P*V4*V^2 - D*P*V4*V^2*u^5 - 10*D*P*V4*V^2*u^2 - 10*D*P*V4*V^2*u^3 -
    5*D*P*V4*u*V^2 - 5*D*P*V4*V^2*u^4) * h_Q1 + (P*V4*nZ*V^2 + P*V4*nZ*V^2*u^3 + 3*P*V4*nZ*u*V^2 +
    3*P*V4*nZ*V^2*u^2) * h_Qph + (KR*V*V4*W3*hA + D*E1*P*V4*hA*V^4 + D*E41*P*hA*V^2*V4^3 -
    E4ph*P*hA*nZ*V^2*V4^3 - Eph*P*V4*hA*nZ*V^4 + D*E1*P*V4*hA*V^4*u^5 + D*E41*P*hA*V^2*V4^3*u^5 -
    E4ph*P*hA*nZ*V^2*V4^3*u^3 - Eph*P*V4*hA*nZ*V^4*u^3 - 3*E4ph*P*hA*nZ*u*V^2*V4^3 -
    3*E4ph*P*hA*nZ*V^2*V4^3*u^2 - 3*Eph*P*V4*hA*nZ*u*V^4 - 3*Eph*P*V4*hA*nZ*V^4*u^2 +
    5*D*E1*P*V4*hA*u*V^4 + 5*D*E1*P*V4*hA*V^4*u^4 + 5*D*E41*P*hA*u*V^2*V4^3 +
    5*D*E41*P*hA*V^2*V4^3*u^4 + 10*D*E1*P*V4*hA*V^4*u^2 + 10*D*E1*P*V4*hA*V^4*u^3 +
    10*D*E41*P*hA*V^2*V4^3*u^2 + 10*D*E41*P*hA*V^2*V4^3*u^3) * h_Q + (D*P4*V4*hA*qv*P^2*V^4 +
    D*P4*V4*hA*qv*P^2*V^4*u^5 + 5*D*P4*V4*hA*qv*u*P^2*V^4 + 5*D*P4*V4*hA*qv*P^2*V^4*u^4 +
    10*D*P4*V4*hA*qv*P^2*V^4*u^2 + 10*D*P4*V4*hA*qv*P^2*V^4*u^3) * h_E1 + (-P4*V4*hA*nZ*qv*P^2*V^4
    - P4*V4*hA*nZ*qv*P^2*V^4*u^3 - 3*P4*V4*hA*nZ*qv*u*P^2*V^4 - 3*P4*V4*hA*nZ*qv*P^2*V^4*u^2) *
    h_Eph + (D*P4*hA*qv*P^2*V^2*V4^3 + D*P4*hA*qv*P^2*V^2*V4^3*u^5 + 5*D*P4*hA*qv*u*P^2*V^2*V4^3 +
    5*D*P4*hA*qv*P^2*V^2*V4^3*u^4 + 10*D*P4*hA*qv*P^2*V^2*V4^3*u^2 +
    10*D*P4*hA*qv*P^2*V^2*V4^3*u^3) * h_E41 + (-P4*hA*nZ*qv*P^2*V^2*V4^3 -
    P4*hA*nZ*qv*P^2*V^2*V4^3*u^3 - 3*P4*hA*nZ*qv*u*P^2*V^2*V4^3 - 3*P4*hA*nZ*qv*P^2*V^2*V4^3*u^2) *
    h_E4ph + (-D*P*P4*V4*qv*V^2 - D*P*P4*V4*qv*V^2*u^5 - 10*D*P*P4*V4*qv*V^2*u^2 -
    10*D*P*P4*V4*qv*V^2*u^3 - 5*D*P*P4*V4*qv*u*V^2 - 5*D*P*P4*V4*qv*V^2*u^4 +
    2*D*P4*V4*hA*P^3*V^4*qv^2 + 2*D*P4*V4*hA*P^3*V^4*qv^2*u^5 + 10*D*P4*V4*hA*u*P^3*V^4*qv^2 +
    10*D*P4*V4*hA*P^3*V^4*qv^2*u^4 + 20*D*P4*V4*hA*P^3*V^4*qv^2*u^2 +
    20*D*P4*V4*hA*P^3*V^4*qv^2*u^3) * h_P1 + (P*P4*V4*nZ*qv*V^2 + P*P4*V4*nZ*qv*V^2*u^3 -
    2*P4*V4*hA*nZ*P^3*V^4*qv^2 + 3*P*P4*V4*nZ*qv*u*V^2 + 3*P*P4*V4*nZ*qv*V^2*u^2 -
    6*P4*V4*hA*nZ*u*P^3*V^4*qv^2 - 6*P4*V4*hA*nZ*P^3*V^4*qv^2*u^2 - 2*P4*V4*hA*nZ*P^3*V^4*qv^2*u^3)
    * h_Pph + (-D*V4*qv*P^2*V^2 - D*V4*qv*P^2*V^2*u^5 - 10*D*V4*qv*P^2*V^2*u^2 -
    10*D*V4*qv*P^2*V^2*u^3 - 5*D*V4*qv*u*P^2*V^2 - 5*D*V4*qv*P^2*V^2*u^4) * h_P41 +
    (V4*nZ*qv*P^2*V^2 + V4*nZ*qv*P^2*V^2*u^3 + 3*V4*nZ*qv*u*P^2*V^2 + 3*V4*nZ*qv*P^2*V^2*u^2) *
    h_P4ph + (KR*P*P4*V*V4*hA*qv) * hW3 + (P4*V4*hA*qv*P^4*V^4) * hKR + (D*P4*V4*hA*qv*P^4*V^4 +
    D*P4*V4*hA*qv*P^4*V^4*u^5 + 5*D*P4*V4*hA*qv*u*P^4*V^4 + 5*D*P4*V4*hA*qv*P^4*V^4*u^4 +
    10*D*P4*V4*hA*qv*P^4*V^4*u^2 + 10*D*P4*V4*hA*qv*P^4*V^4*u^3) * hqz + (-P4*V4*hA*nZ*qv*P^4*V^4 -
    P4*V4*hA*nZ*qv*P^4*V^4*u^3 - 3*P4*V4*hA*nZ*qv*u*P^4*V^4 - 3*P4*V4*hA*nZ*qv*P^4*V^4*u^2) * hqph
    + (-4*P4*V4*hA*nZph*P^2*V^2*nZ^2 + 4*D1*P4*V4*hA*D^2*P^2*V^2 - 12*P4*V4*hA*nZph*u*P^2*V^2*nZ^2
    - 12*P4*V4*hA*nZph*P^2*V^2*nZ^2*u^2 - 4*D*Dph*P4*V4*hA*nZ*P^2*V^2 -
    4*P4*V4*hA*nR*nRph*nZ*P^2*V^2 - 4*P4*V4*hA*nZph*P^2*V^2*nZ^2*u^3 + 4*D*P4*V4*hA*nR*nR1*P^2*V^2
    + 4*D*P4*V4*hA*nZ*nZ1*P^2*V^2 + 4*D1*P4*V4*hA*D^2*P^2*V^2*u^7 + 28*D1*P4*V4*hA*u*D^2*P^2*V^2 +
    28*D1*P4*V4*hA*D^2*P^2*V^2*u^6 + 84*D1*P4*V4*hA*D^2*P^2*V^2*u^2 +
    84*D1*P4*V4*hA*D^2*P^2*V^2*u^5 + 140*D1*P4*V4*hA*D^2*P^2*V^2*u^3 +
    140*D1*P4*V4*hA*D^2*P^2*V^2*u^4 - 40*D*Dph*P4*V4*hA*nZ*P^2*V^2*u^2 -
    40*D*Dph*P4*V4*hA*nZ*P^2*V^2*u^3 - 20*D*Dph*P4*V4*hA*nZ*u*P^2*V^2 -
    20*D*Dph*P4*V4*hA*nZ*P^2*V^2*u^4 - 12*P4*V4*hA*nR*nRph*nZ*u*P^2*V^2 -
    12*P4*V4*hA*nR*nRph*nZ*P^2*V^2*u^2 - 4*D*Dph*P4*V4*hA*nZ*P^2*V^2*u^5 -
    4*P4*V4*hA*nR*nRph*nZ*P^2*V^2*u^3 + 4*D*P4*V4*hA*nR*nR1*P^2*V^2*u^5 +
    4*D*P4*V4*hA*nZ*nZ1*P^2*V^2*u^5 + 20*D*P4*V4*hA*nR*nR1*u*P^2*V^2 +
    20*D*P4*V4*hA*nR*nR1*P^2*V^2*u^4 + 20*D*P4*V4*hA*nZ*nZ1*u*P^2*V^2 +
    20*D*P4*V4*hA*nZ*nZ1*P^2*V^2*u^4 + 40*D*P4*V4*hA*nR*nR1*P^2*V^2*u^2 +
    40*D*P4*V4*hA*nR*nR1*P^2*V^2*u^3 + 40*D*P4*V4*hA*nZ*nZ1*P^2*V^2*u^2 +
    40*D*P4*V4*hA*nZ*nZ1*P^2*V^2*u^3) * hV + (-2*P4*V4*nZph*P^2*V^2*nZ^2 + 2*D1*P4*V4*D^2*P^2*V^2 -
    6*P4*V4*nZph*u*P^2*V^2*nZ^2 - 6*P4*V4*nZph*P^2*V^2*nZ^2*u^2 - 2*D*Dph*P4*V4*nZ*P^2*V^2 -
    2*P4*V4*nR*nRph*nZ*P^2*V^2 - 2*P4*V4*nZph*P^2*V^2*nZ^2*u^3 + 2*D*P4*V4*nR*nR1*P^2*V^2 +
    2*D*P4*V4*nZ*nZ1*P^2*V^2 + 2*D1*P4*V4*D^2*P^2*V^2*u^7 + 14*D1*P4*V4*u*D^2*P^2*V^2 +
    14*D1*P4*V4*D^2*P^2*V^2*u^6 + 42*D1*P4*V4*D^2*P^2*V^2*u^2 + 42*D1*P4*V4*D^2*P^2*V^2*u^5 +
    70*D1*P4*V4*D^2*P^2*V^2*u^3 + 70*D1*P4*V4*D^2*P^2*V^2*u^4 - 20*D*Dph*P4*V4*nZ*P^2*V^2*u^2 -
    20*D*Dph*P4*V4*nZ*P^2*V^2*u^3 - 10*D*Dph*P4*V4*nZ*u*P^2*V^2 - 10*D*Dph*P4*V4*nZ*P^2*V^2*u^4 -
    6*P4*V4*nR*nRph*nZ*u*P^2*V^2 - 6*P4*V4*nR*nRph*nZ*P^2*V^2*u^2 - 2*D*Dph*P4*V4*nZ*P^2*V^2*u^5 -
    2*P4*V4*nR*nRph*nZ*P^2*V^2*u^3 + 2*D*P4*V4*nR*nR1*P^2*V^2*u^5 + 2*D*P4*V4*nZ*nZ1*P^2*V^2*u^5 +
    10*D*P4*V4*nR*nR1*u*P^2*V^2 + 10*D*P4*V4*nR*nR1*P^2*V^2*u^4 + 10*D*P4*V4*nZ*nZ1*u*P^2*V^2 +
    10*D*P4*V4*nZ*nZ1*P^2*V^2*u^4 + 20*D*P4*V4*nR*nR1*P^2*V^2*u^2 + 20*D*P4*V4*nR*nR1*P^2*V^2*u^3 +
    20*D*P4*V4*nZ*nZ1*P^2*V^2*u^2 + 20*D*P4*V4*nZ*nZ1*P^2*V^2*u^3) * h_half

set_option linter.unusedSimpArgs false in
/-- **Divergence-free identity** of the `μ > 0` passing flow form. -/
theorem gcMu_divFree (ρ lm : ℝ) (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)
    (hV4 : PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1) :
    (1 + u) * phiDS (xB u z) (gcDM ρ lm) - 3 * PolyExprS.eval (xB u z) (gcNRM ρ lm) +
      (1 + u) * pdS (xB u z) 0 (gcNRM ρ lm) + (1 + u) * pdS (xB u z) 1 (gcNZM ρ lm) = 0 := by
  have o1 := gc_divFree 1 u z hV
  have o0 := gc_divFree 0 u z hV
  have gB := gcMu_gradBm u z hV hV4
  have hYD := eval_eYD (xB u z)
  have hYR := eval_eYR (xB u z)
  have hYZ := eval_eYZ (xB u z)
  simp only [phiDS_eq_deriv, pdS, gcDM, gcNRM, gcNZM, gcPaM, gcPbM, gcPcM, gcD_eq, gcNR_eq,
    gcNZ_eq, gcPa_eq, gcPb_eq, gcPc_eq, eF, eS, PolyExprS.deriv, PolyExprS.eval,
    PolyExprS.deriv_ofPoly, PolyExprS.eval_ofPoly, deriv_eN, deriv_single, deriv_phiDir, map_neg,
    Complex.ofReal_one, Complex.ofReal_zero, map_one, map_zero,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero, one_mul] at *
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  set lA := algebraMap ℂ FA (lm : ℂ) with hdef_lA
  set l2 := algebraMap ℂ FA ((lm : ℂ) / 2) with hdef_l2
  set N := PolyExprS.eval (xB u z) (eN lm) with hdef_N
  set Bm := PolyExprS.eval (xB u z) eBm with hdef_Bm
  set YD := PolyExprS.eval (xB u z) eYD with hdef_YD
  set YR := PolyExprS.eval (xB u z) eYR with hdef_YR
  set YZ := PolyExprS.eval (xB u z) eYZ with hdef_YZ
  set dYDph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eYD with hdef_dYDph
  set dYR0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eYR with hdef_dYR0
  set dYZ1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eYZ with hdef_dYZ1
  set Xa := PolyExprS.eval (xB u z) eXa with hdef_Xa
  set Xb := PolyExprS.eval (xB u z) eXb with hdef_Xb
  set Xc := PolyExprS.eval (xB u z) eXc with hdef_Xc
  set dXa1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXa with hdef_dXa1
  set dXaph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXa with hdef_dXaph
  set dXb0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXb with hdef_dXb0
  set dXbph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXb with hdef_dXbph
  set dXc0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXc with hdef_dXc0
  set dXc1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXc with hdef_dXc1
  set dB0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm with hdef_dB0
  set dB1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm with hdef_dB1
  set dBph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm with hdef_dBph
  set Pa := PolyExpr.eval (xB u z) KamNewton.Pap with hdef_Pa
  set Pb := PolyExpr.eval (xB u z) KamNewton.Pbp with hdef_Pb
  set Pa1 := pd (xB u z) 1 KamNewton.Pap with hdef_Pa1
  set Paph := phiD (xB u z) KamNewton.Pap with hdef_Paph
  set Pb0 := pd (xB u z) 0 KamNewton.Pbp with hdef_Pb0
  set Pbph := phiD (xB u z) KamNewton.Pbp with hdef_Pbph
  linear_combination (1 - N*rA + Bm*N*l2*rA) * o0 + (N*rA - Bm*N*l2*rA) * o1 + (W3*lA*rA*N^3*hA^2 -
    N*W3*hA*l2*rA + W3*lA*rA*u*N^3*hA^2 - N*W3*hA*l2*rA*u - Bm*W3*l2*lA*rA*N^3*hA^2 -
    Bm*W3*l2*lA*rA*u*N^3*hA^2) * gB + (-N*dBph*l2*rA + dBph*hA*lA*rA*N^3 - N*dBph*l2*rA*u +
    dBph*hA*lA*rA*u*N^3 - Bm*dBph*hA*l2*lA*rA*N^3 - Bm*dBph*hA*l2*lA*rA*u*N^3) * hYD +
    (-N*dB0*l2*rA + dB0*hA*lA*rA*N^3 - N*dB0*l2*rA*u + dB0*hA*lA*rA*u*N^3 - Bm*dB0*hA*l2*lA*rA*N^3
    - Bm*dB0*hA*l2*lA*rA*u*N^3) * hYR + (-N*dB1*l2*rA + dB1*hA*lA*rA*N^3 - N*dB1*l2*rA*u +
    dB1*hA*lA*rA*u*N^3 - Bm*dB1*hA*l2*lA*rA*N^3 - Bm*dB1*hA*l2*lA*rA*u*N^3) * hYZ

set_option linter.unusedSimpArgs false in
/-- **Flux primitive identity** (a) of the `μ > 0` passing flow form. -/
theorem gcMu_flux_a (ρ lm : ℝ) (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)
    (hV4 : PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1)
    (hN : PolyExprS.eval (xB u z) (eN lm) ^ 2 * (1 + -algebraMap ℂ FA (lm : ℂ) *
      PolyExprS.eval (xB u z) eBm) = 1) :
    (1 + u) * pdS (xB u z) 0 (gcPbM ρ lm) - 2 * PolyExprS.eval (xB u z) (gcPbM ρ lm) -
      (1 + u) ^ 2 * pdS (xB u z) 1 (gcPaM ρ lm) = PolyExprS.eval (xB u z) (gcDM ρ lm) := by
  have o1 := gc_flux_a 1 u z hV
  have o0 := gc_flux_a 0 u z hV
  have cA := gcMu_bmY_a u z hV hV4
  have h_half := half_rel
  have hl2 := half_lm lm
  simp only [phiDS_eq_deriv, pdS, gcDM, gcNRM, gcNZM, gcPaM, gcPbM, gcPcM, gcD_eq, gcNR_eq,
    gcNZ_eq, gcPa_eq, gcPb_eq, gcPc_eq, eF, eS, PolyExprS.deriv, PolyExprS.eval,
    PolyExprS.deriv_ofPoly, PolyExprS.eval_ofPoly, deriv_eN, deriv_single, deriv_phiDir, map_neg,
    Complex.ofReal_one, Complex.ofReal_zero, map_one, map_zero,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero, one_mul] at *
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  set lA := algebraMap ℂ FA (lm : ℂ) with hdef_lA
  set l2 := algebraMap ℂ FA ((lm : ℂ) / 2) with hdef_l2
  set N := PolyExprS.eval (xB u z) (eN lm) with hdef_N
  set Bm := PolyExprS.eval (xB u z) eBm with hdef_Bm
  set YD := PolyExprS.eval (xB u z) eYD with hdef_YD
  set YR := PolyExprS.eval (xB u z) eYR with hdef_YR
  set YZ := PolyExprS.eval (xB u z) eYZ with hdef_YZ
  set dYDph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eYD with hdef_dYDph
  set dYR0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eYR with hdef_dYR0
  set dYZ1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eYZ with hdef_dYZ1
  set Xa := PolyExprS.eval (xB u z) eXa with hdef_Xa
  set Xb := PolyExprS.eval (xB u z) eXb with hdef_Xb
  set Xc := PolyExprS.eval (xB u z) eXc with hdef_Xc
  set dXa1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXa with hdef_dXa1
  set dXaph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXa with hdef_dXaph
  set dXb0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXb with hdef_dXb0
  set dXbph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXb with hdef_dXbph
  set dXc0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXc with hdef_dXc0
  set dXc1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXc with hdef_dXc1
  set dB0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm with hdef_dB0
  set dB1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm with hdef_dB1
  set dBph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm with hdef_dBph
  set Pa := PolyExpr.eval (xB u z) KamNewton.Pap with hdef_Pa
  set Pb := PolyExpr.eval (xB u z) KamNewton.Pbp with hdef_Pb
  set Pa1 := pd (xB u z) 1 KamNewton.Pap with hdef_Pa1
  set Paph := phiD (xB u z) KamNewton.Pap with hdef_Paph
  set Pb0 := pd (xB u z) 0 KamNewton.Pbp with hdef_Pb0
  set Pbph := phiD (xB u z) KamNewton.Pbp with hdef_Pbph
  linear_combination (1 - N*rA + Bm*N*lA*rA) * o0 + (N*rA - Bm*N*lA*rA) * o1 + (-N*lA*rA +
    hA*lA*rA*N^3 - Bm*hA*rA*N^3*lA^2) * cA + (-Bm*N*YD*hA*lA*rA) * hN + (Bm*N*YD*hA*rA) * hl2 +
    (-Bm*N*YD*l2*rA) * h_half

set_option linter.unusedSimpArgs false in
/-- **Flux primitive identity** (b) of the `μ > 0` passing flow form. -/
theorem gcMu_flux_b (ρ lm : ℝ) (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)
    (hV4 : PolyExprS.eval (xB u z) eV4 ^ 2 * (1 + PolyExpr.eval (xB u z) E4P) = 1)
    (hN : PolyExprS.eval (xB u z) (eN lm) ^ 2 * (1 + -algebraMap ℂ FA (lm : ℂ) *
      PolyExprS.eval (xB u z) eBm) = 1) :
    (1 + u) ^ 2 * phiDS (xB u z) (gcPaM ρ lm) - (1 + u) ^ 3 * pdS (xB u z) 0 (gcPcM ρ lm) =
      PolyExprS.eval (xB u z) (gcNZM ρ lm) := by
  have o1 := gc_flux_b 1 u z hV
  have o0 := gc_flux_b 0 u z hV
  have cB := gcMu_bmY_b u z hV hV4
  have h_half := half_rel
  have hl2 := half_lm lm
  simp only [phiDS_eq_deriv, pdS, gcDM, gcNRM, gcNZM, gcPaM, gcPbM, gcPcM, gcD_eq, gcNR_eq,
    gcNZ_eq, gcPa_eq, gcPb_eq, gcPc_eq, eF, eS, PolyExprS.deriv, PolyExprS.eval,
    PolyExprS.deriv_ofPoly, PolyExprS.eval_ofPoly, deriv_eN, deriv_single, deriv_phiDir, map_neg,
    Complex.ofReal_one, Complex.ofReal_zero, map_one, map_zero,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, one_mul] at *
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  set lA := algebraMap ℂ FA (lm : ℂ) with hdef_lA
  set l2 := algebraMap ℂ FA ((lm : ℂ) / 2) with hdef_l2
  set N := PolyExprS.eval (xB u z) (eN lm) with hdef_N
  set Bm := PolyExprS.eval (xB u z) eBm with hdef_Bm
  set YD := PolyExprS.eval (xB u z) eYD with hdef_YD
  set YR := PolyExprS.eval (xB u z) eYR with hdef_YR
  set YZ := PolyExprS.eval (xB u z) eYZ with hdef_YZ
  set dYDph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eYD with hdef_dYDph
  set dYR0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eYR with hdef_dYR0
  set dYZ1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eYZ with hdef_dYZ1
  set Xa := PolyExprS.eval (xB u z) eXa with hdef_Xa
  set Xb := PolyExprS.eval (xB u z) eXb with hdef_Xb
  set Xc := PolyExprS.eval (xB u z) eXc with hdef_Xc
  set dXa1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXa with hdef_dXa1
  set dXaph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXa with hdef_dXaph
  set dXb0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXb with hdef_dXb0
  set dXbph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXb with hdef_dXbph
  set dXc0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXc with hdef_dXc0
  set dXc1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXc with hdef_dXc1
  set dB0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm with hdef_dB0
  set dB1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm with hdef_dB1
  set dBph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm with hdef_dBph
  set Pa := PolyExpr.eval (xB u z) KamNewton.Pap with hdef_Pa
  set Pb := PolyExpr.eval (xB u z) KamNewton.Pbp with hdef_Pb
  set Pa1 := pd (xB u z) 1 KamNewton.Pap with hdef_Pa1
  set Paph := phiD (xB u z) KamNewton.Pap with hdef_Paph
  set Pb0 := pd (xB u z) 0 KamNewton.Pbp with hdef_Pb0
  set Pbph := phiD (xB u z) KamNewton.Pbp with hdef_Pbph
  linear_combination (1 - N*rA + Bm*N*lA*rA) * o0 + (N*rA - Bm*N*lA*rA) * o1 + (-N*lA*rA +
    hA*lA*rA*N^3 - Bm*hA*rA*N^3*lA^2) * cB + (-Bm*N*YZ*hA*lA*rA) * hN + (Bm*N*YZ*hA*rA) * hl2 +
    (-Bm*N*YZ*l2*rA) * h_half

set_option linter.unusedSimpArgs false in
/-- **Flux primitive identity** (c) of the `μ > 0` passing flow form. -/
theorem gcMu_flux_c (ρ lm : ℝ) (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1)
    (hN : PolyExprS.eval (xB u z) (eN lm) ^ 2 * (1 + -algebraMap ℂ FA (lm : ℂ) *
      PolyExprS.eval (xB u z) eBm) = 1) :
    (1 + u) * phiDS (xB u z) (gcPbM ρ lm) - (1 + u) ^ 3 * pdS (xB u z) 1 (gcPcM ρ lm) =
      -PolyExprS.eval (xB u z) (gcNRM ρ lm) := by
  have o1 := gc_flux_c 1 u z
  have o0 := gc_flux_c 0 u z
  have cC := gcMu_bmY_c u z hV
  have h_half := half_rel
  have hl2 := half_lm lm
  simp only [phiDS_eq_deriv, pdS, gcDM, gcNRM, gcNZM, gcPaM, gcPbM, gcPcM, gcD_eq, gcNR_eq,
    gcNZ_eq, gcPa_eq, gcPb_eq, gcPc_eq, eF, eS, PolyExprS.deriv, PolyExprS.eval,
    PolyExprS.deriv_ofPoly, PolyExprS.eval_ofPoly, deriv_eN, deriv_single, deriv_phiDir, map_neg,
    Complex.ofReal_one, Complex.ofReal_zero, map_one, map_zero,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub, one_mul] at *
  set D := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_D
  set nR := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nR
  set nZ := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZ
  set D0 := pd (xB u z) 0 KamNewton.Dp with hdef_D0
  set D1 := pd (xB u z) 1 KamNewton.Dp with hdef_D1
  set Dph := phiD (xB u z) KamNewton.Dp with hdef_Dph
  set nR0 := pd (xB u z) 0 KamNewton.nRp with hdef_nR0
  set nR1 := pd (xB u z) 1 KamNewton.nRp with hdef_nR1
  set nRph := phiD (xB u z) KamNewton.nRp with hdef_nRph
  set nZ0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZ0
  set nZ1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZ1
  set nZph := phiD (xB u z) KamNewton.nZp with hdef_nZph
  set P := PolyExpr.eval (xB u z) PuP with hdef_P
  set P0 := pd (xB u z) 0 PuP with hdef_P0
  set P1 := pd (xB u z) 1 PuP with hdef_P1
  set Pph := phiD (xB u z) PuP with hdef_Pph
  set P4 := PolyExpr.eval (xB u z) P4P with hdef_P4
  set P40 := pd (xB u z) 0 P4P with hdef_P40
  set P41 := pd (xB u z) 1 P4P with hdef_P41
  set P4ph := phiD (xB u z) P4P with hdef_P4ph
  set Q := PolyExpr.eval (xB u z) QPP4P with hdef_Q
  set Q0 := pd (xB u z) 0 QPP4P with hdef_Q0
  set Q1 := pd (xB u z) 1 QPP4P with hdef_Q1
  set Qph := phiD (xB u z) QPP4P with hdef_Qph
  set E := PolyExpr.eval (xB u z) EpP with hdef_E
  set E0 := pd (xB u z) 0 EpP with hdef_E0
  set E1 := pd (xB u z) 1 EpP with hdef_E1
  set Eph := phiD (xB u z) EpP with hdef_Eph
  set E4 := PolyExpr.eval (xB u z) E4P with hdef_E4
  set E40 := pd (xB u z) 0 E4P with hdef_E40
  set E41 := pd (xB u z) 1 E4P with hdef_E41
  set E4ph := phiD (xB u z) E4P with hdef_E4ph
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set V4 := PolyExprS.eval (xB u z) eV4 with hdef_V4
  set hA := algebraMap ℂ FA (1 / 2) with hdef_hA
  set KD := PolyExprS.eval (xB u z) eKD with hdef_KD
  set KR := PolyExprS.eval (xB u z) eKR with hdef_KR
  set KZ := PolyExprS.eval (xB u z) eKZ with hdef_KZ
  set qv := PolyExprS.eval (xB u z) eq with hdef_qv
  set qR := PolyExprS.eval (xB u z) eqR with hdef_qR
  set qz := PolyExprS.eval (xB u z) eqz with hdef_qz
  set qph := PolyExprS.eval (xB u z) eqph with hdef_qph
  set W3 := PolyExprS.eval (xB u z) eW3 with hdef_W3
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  set lA := algebraMap ℂ FA (lm : ℂ) with hdef_lA
  set l2 := algebraMap ℂ FA ((lm : ℂ) / 2) with hdef_l2
  set N := PolyExprS.eval (xB u z) (eN lm) with hdef_N
  set Bm := PolyExprS.eval (xB u z) eBm with hdef_Bm
  set YD := PolyExprS.eval (xB u z) eYD with hdef_YD
  set YR := PolyExprS.eval (xB u z) eYR with hdef_YR
  set YZ := PolyExprS.eval (xB u z) eYZ with hdef_YZ
  set dYDph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eYD with hdef_dYDph
  set dYR0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eYR with hdef_dYR0
  set dYZ1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eYZ with hdef_dYZ1
  set Xa := PolyExprS.eval (xB u z) eXa with hdef_Xa
  set Xb := PolyExprS.eval (xB u z) eXb with hdef_Xb
  set Xc := PolyExprS.eval (xB u z) eXc with hdef_Xc
  set dXa1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXa with hdef_dXa1
  set dXaph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXa with hdef_dXaph
  set dXb0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXb with hdef_dXb0
  set dXbph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eXb with hdef_dXbph
  set dXc0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eXc with hdef_dXc0
  set dXc1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eXc with hdef_dXc1
  set dB0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eBm with hdef_dB0
  set dB1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eBm with hdef_dB1
  set dBph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eBm with hdef_dBph
  set Pa := PolyExpr.eval (xB u z) KamNewton.Pap with hdef_Pa
  set Pb := PolyExpr.eval (xB u z) KamNewton.Pbp with hdef_Pb
  set Pa1 := pd (xB u z) 1 KamNewton.Pap with hdef_Pa1
  set Paph := phiD (xB u z) KamNewton.Pap with hdef_Paph
  set Pb0 := pd (xB u z) 0 KamNewton.Pbp with hdef_Pb0
  set Pbph := phiD (xB u z) KamNewton.Pbp with hdef_Pbph
  linear_combination (1 - N*rA + Bm*N*lA*rA) * o0 + (N*rA - Bm*N*lA*rA) * o1 + (N*lA*rA -
    hA*lA*rA*N^3 + Bm*hA*rA*N^3*lA^2) * cC + (Bm*N*YR*hA*lA*rA) * hN + (-Bm*N*YR*hA*rA) * hl2 +
    (Bm*N*YR*l2*rA) * h_half

-- END GENERATED

end PlasmaLean.Design.RationalStellaratorGC
