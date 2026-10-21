/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module


public import PlasmaLean.Design.RationalStellaratorGCPoly

/-!
# The guiding-centre field of the rational stellarator in flow form (`gcFlow`)

The modified field of the passing (`μ = 0`) guiding centres is `B̃ = B + ρ ∇×b`, `b = B/|B|`,
`B = field (1/4)` (`Theory/Kinetic/GuidingCentreLittlejohn`, `notes/theory/after-kam.md` §1). For a
curl-free `B`, `∇×b = ∇(|B|⁻¹) × B = ½ |B|⁻³ B × ∇|B|²`; in the variables of the flow form
(`u = R − 1`, `c = cos 2φ`, `s = sin 2φ`; `D = R³B_φ`, `n = R⁴(B^R, B^z)`) and with
`q = n_R² + R² D² + n_z² = R⁸|B|²`, `W = q^{−1/2}`:

* `D̃ = D + (ρ/2) W³ R² (R n_z ∂_u q − 8 n_z q − R n_R ∂_z q)`,
* `ñ_R = n_R + (ρ/2) W³ (R⁵ D ∂_z q − R³ n_z ∂_φ q)`,
* `ñ_z = n_z + (ρ/2) W³ (R³ n_R ∂_φ q − R⁵ D ∂_u q + 8 R⁴ D q)`,

and the primitive of the flux form is `α̃ = α − ρ b♭`: `P̃_a = P_a − ρ R W n_R`,
`P̃_b = P_b − ρ R² W n_z`, `P̃_c = −ρ R² W D` (derived and checked with sympy,
`scripts/gc_kam/gc_symbolic.py`).

**The node.** `W` is not polynomial. It is written `W = P(u) (1 + E)^{−1/2}` with the Taylor
polynomial `P(u)` of `R^{−3}` and the expanded deviation `E = q P² − 1`, so that `W² q = 1`
holds exactly while the majorant of `E` is small near the torus (`E` vanishes on the axis): the
node `eV = isqrt 1 E` is valid for strip norms `‖u‖, ‖z‖ ≲ 0.27` (numerically: majorant `0.55` at
`0.23`).

**Results.**
* `gc_divFree`, `gc_flux_a`, `gc_flux_b`, `gc_flux_c`: the identities of the interface
  `FlowFieldS` hold at every torus point where the node identity `W²(1 + E) = 1` holds; each is a
  `linear_combination` (generated certificate) of the polynomial identities of
  `Design/RationalStellaratorGCPoly`, the identities of `field (1/4)` (`KamNewton.divFree`,
  `KamNewton.flux_*`) and the node identity.
* `gcFlow ρ : FlowFieldS`: the guiding-centre field as an instance of the KAM interface, so
  `FlowFieldS.KamH.kam_flow_torus` applies to it.

**Sanity.** `gcD_zero`: for `ρ = 0` the flow form is that of `field (1/4)`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton Complex WEll1Z2

/-! ## Auxiliary lemmas -/

/-- The direction of the `φ`-derivative: `∂_φ = −2s ∂_c + 2c ∂_s`. -/
def phiDir (x : Fin 6 → FA) : Fin 6 → FA := ![0, 0, -2 * x 3, 2 * x 2, 0, 0]

/-- `phiDS` is the directional derivative along `phiDir`. -/
theorem phiDS_eq_deriv (x : Fin 6 → FA) (e : PolyExprS ℂ (Fin 6)) :
    phiDS x e = PolyExprS.deriv x (phiDir x) e := by
  rw [deriv_eq_sum_pdS, Fin.sum_univ_six, phiDS]
  simp [phiDir]
  ring

/-- `phiD` is the directional derivative along `phiDir`. -/
theorem deriv_phiDir (x : Fin 6 → FA) (e : PolyExpr ℂ (Fin 6)) :
    PolyExpr.deriv x (phiDir x) e = phiD x e := by
  rw [deriv_eq_sum, Fin.sum_univ_six, phiD]
  simp [phiDir]
  ring

/-- Derivatives along unit vectors are partial derivatives. -/
theorem deriv_single (x : Fin 6 → FA) (i : Fin 6) (e : PolyExpr ℂ (Fin 6)) :
    PolyExpr.deriv x (Pi.single i 1) e = pd x i e := rfl

/-- The first variable of a torus point. -/
theorem xB_zero (u z : FA) : xB u z 0 = u := rfl

/-- `e₀ · e₀ = 1`. -/
theorem single_00 : (Pi.single (0 : Fin 6) (1 : FA) : Fin 6 → FA) 0 = 1 := by simp

/-- `e₁ · e₀ = 0`. -/
theorem single_10 : (Pi.single (1 : Fin 6) (1 : FA) : Fin 6 → FA) 0 = 0 := by simp

/-- `phiDir` has no `u`-component. -/
theorem phiDir_0 (x : Fin 6 → FA) : phiDir x 0 = 0 := rfl

/-- `2 · ½ = 1` in `𝔸`. -/
theorem half_rel : 2 * algebraMap ℂ FA (1 / 2) = 1 := by
  rw [← map_ofNat (algebraMap ℂ FA) 2, ← map_mul]; norm_num

/-- The scalar `−½` of the node derivative. -/
theorem smul_half (X : FA) : (-(1 / 2 : ℂ)) • X = -(algebraMap ℂ FA (1 / 2) * X) := by
  rw [Algebra.smul_def, map_neg, neg_mul]

/-- Cancel a nonzero natural factor in `𝔸`. -/
theorem eq_of_natCast_mul_sub {X Y : FA} {n : ℕ} (hn : n ≠ 0) (h : (n : FA) * (X - Y) = 0) :
    X = Y := by
  have h1 : algebraMap ℂ FA ((n : ℂ)⁻¹) * (n : FA) = 1 := by
    rw [← map_natCast (algebraMap ℂ FA) n, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hn),
      map_one]
  have h2 : X - Y = 0 := by
    calc X - Y = algebraMap ℂ FA ((n : ℂ)⁻¹) * ((n : FA) * (X - Y)) := by
          rw [← mul_assoc, h1, one_mul]
      _ = 0 := by rw [h, mul_zero]
  exact sub_eq_zero.1 h2

/-! ## The expressions -/

/-- The node `(1 + E)^{−1/2}`, so that `W = P (1 + E)^{−1/2} = q^{−1/2}`. -/
def eV : PolyExprS ℂ (Fin 6) := .isqrt 1 (PolyExprS.ofPoly EpP)

/-- Derivative of the node: `−½ ((1 + E)^{−1/2})³ DE`. -/
theorem deriv_eV (x h : Fin 6 → FA) : PolyExprS.deriv x h eV =
    -(algebraMap ℂ FA (1 / 2) * PolyExprS.eval x eV ^ 3) * PolyExpr.deriv x h EpP := by
  simp only [eV, PolyExprS.deriv, PolyExprS.deriv_ofPoly, smul_half]

/-- `W = P · (1 + E)^{−1/2} = q^{−1/2}`. -/
def eW : PolyExprS ℂ (Fin 6) :=
  .mul (PolyExprS.ofPoly PuP) (eV)

/-- `W³`. -/
def eW3 : PolyExprS ℂ (Fin 6) :=
  .mul (eW) (.mul (eW) (eW))

/-- `R = 1 + u`. -/
def eR : PolyExprS ℂ (Fin 6) :=
  .add (.const (1 : ℂ)) (.var 0)

/-- `∂_u q`. -/
def eqR : PolyExprS ℂ (Fin 6) :=
  .add (.mul (.const (2 : ℂ)) (.mul (PolyExprS.ofPoly KamNewton.nRp) (PolyExprS.ofPoly nRuP)))
    (.add (.mul (.const (2 : ℂ)) (.mul (eR) (.mul (PolyExprS.ofPoly KamNewton.Dp)
    (PolyExprS.ofPoly KamNewton.Dp)))) (.add (.mul (.const (2 : ℂ)) (.mul (eR) (.mul (eR) (.mul
    (PolyExprS.ofPoly KamNewton.Dp) (PolyExprS.ofPoly DuP))))) (.mul (.const (2 : ℂ)) (.mul
    (PolyExprS.ofPoly KamNewton.nZp) (PolyExprS.ofPoly nZuP)))))

/-- `q = n_R² + R² D² + n_z²`. -/
def eq : PolyExprS ℂ (Fin 6) :=
  .add (.mul (PolyExprS.ofPoly KamNewton.nRp) (PolyExprS.ofPoly KamNewton.nRp)) (.add (.mul (eR)
    (.mul (eR) (.mul (PolyExprS.ofPoly KamNewton.Dp) (PolyExprS.ofPoly KamNewton.Dp)))) (.mul
    (PolyExprS.ofPoly KamNewton.nZp) (PolyExprS.ofPoly KamNewton.nZp)))

/-- `∂_z q`. -/
def eqz : PolyExprS ℂ (Fin 6) :=
  .add (.mul (.const (2 : ℂ)) (.mul (PolyExprS.ofPoly KamNewton.nRp) (PolyExprS.ofPoly nRzP)))
    (.add (.mul (.const (2 : ℂ)) (.mul (eR) (.mul (eR) (.mul (PolyExprS.ofPoly KamNewton.Dp)
    (PolyExprS.ofPoly DzP))))) (.mul (.const (2 : ℂ)) (.mul (PolyExprS.ofPoly KamNewton.nZp)
    (PolyExprS.ofPoly nZzP))))

/-- The bracket `κ_D = R² (R n_z ∂_u q − 8 n_z q − R n_R ∂_z q)` of `D̃`. -/
def eKD : PolyExprS ℂ (Fin 6) :=
  .mul (eR) (.mul (eR) (.sub (.sub (.mul (eR) (.mul (PolyExprS.ofPoly KamNewton.nZp) (eqR)))
    (.mul (.const (8 : ℂ)) (.mul (PolyExprS.ofPoly KamNewton.nZp) (eq)))) (.mul (eR) (.mul
    (PolyExprS.ofPoly KamNewton.nRp) (eqz)))))

/-- `∂_φ q`. -/
def eqph : PolyExprS ℂ (Fin 6) :=
  .add (.mul (.const (2 : ℂ)) (.mul (PolyExprS.ofPoly KamNewton.nRp) (PolyExprS.ofPoly nRphP)))
    (.add (.mul (.const (2 : ℂ)) (.mul (eR) (.mul (eR) (.mul (PolyExprS.ofPoly KamNewton.Dp)
    (PolyExprS.ofPoly DphP))))) (.mul (.const (2 : ℂ)) (.mul (PolyExprS.ofPoly KamNewton.nZp)
    (PolyExprS.ofPoly nZphP))))

/-- The bracket `κ_R = R⁵ D ∂_z q − R³ n_z ∂_φ q` of `ñ_R`. -/
def eKR : PolyExprS ℂ (Fin 6) :=
  .sub (.mul (eR) (.mul (eR) (.mul (eR) (.mul (eR) (.mul (eR) (.mul (PolyExprS.ofPoly
    KamNewton.Dp) (eqz))))))) (.mul (eR) (.mul (eR) (.mul (eR) (.mul (PolyExprS.ofPoly
    KamNewton.nZp) (eqph)))))

/-- The bracket `κ_z = R³ n_R ∂_φ q − R⁵ D ∂_u q + 8 R⁴ D q` of `ñ_z`. -/
def eKZ : PolyExprS ℂ (Fin 6) :=
  .add (.sub (.mul (eR) (.mul (eR) (.mul (eR) (.mul (PolyExprS.ofPoly KamNewton.nRp) (eqph)))))
    (.mul (eR) (.mul (eR) (.mul (eR) (.mul (eR) (.mul (eR) (.mul (PolyExprS.ofPoly KamNewton.Dp)
    (eqR)))))))) (.mul (.const (8 : ℂ)) (.mul (eR) (.mul (eR) (.mul (eR) (.mul (eR) (.mul
    (PolyExprS.ofPoly KamNewton.Dp) (eq)))))))

/-- `D̃ = R³ B̃_φ`. -/
def gcD (ρ : ℝ) : PolyExprS ℂ (Fin 6) :=
  .add (PolyExprS.ofPoly KamNewton.Dp) (.mul (.const (ρ : ℂ)) (.mul (.const (1 / 2 : ℂ)) (.mul
    (eW3) (eKD))))

/-- `ñ_R = R⁴ B̃^R`. -/
def gcNR (ρ : ℝ) : PolyExprS ℂ (Fin 6) :=
  .add (PolyExprS.ofPoly KamNewton.nRp) (.mul (.const (ρ : ℂ)) (.mul (.const (1 / 2 : ℂ)) (.mul
    (eW3) (eKR))))

/-- `ñ_z = R⁴ B̃^z`. -/
def gcNZ (ρ : ℝ) : PolyExprS ℂ (Fin 6) :=
  .add (PolyExprS.ofPoly KamNewton.nZp) (.mul (.const (ρ : ℂ)) (.mul (.const (1 / 2 : ℂ)) (.mul
    (eW3) (eKZ))))

/-- `P̃_a = P_a − ρ R W n_R`. -/
def gcPa (ρ : ℝ) : PolyExprS ℂ (Fin 6) :=
  .sub (PolyExprS.ofPoly KamNewton.Pap) (.mul (.const (ρ : ℂ)) (.mul (eR) (.mul (eW)
    (PolyExprS.ofPoly KamNewton.nRp))))

/-- `P̃_b = P_b − ρ R² W n_z`. -/
def gcPb (ρ : ℝ) : PolyExprS ℂ (Fin 6) :=
  .sub (PolyExprS.ofPoly KamNewton.Pbp) (.mul (.const (ρ : ℂ)) (.mul (eR) (.mul (eR) (.mul (eW)
    (PolyExprS.ofPoly KamNewton.nZp)))))

/-- `P̃_c = −ρ R² W D`. -/
def gcPc (ρ : ℝ) : PolyExprS ℂ (Fin 6) :=
  .sub (.const (0 : ℂ)) (.mul (.const (ρ : ℂ)) (.mul (eR) (.mul (eR) (.mul (eW)
    (PolyExprS.ofPoly KamNewton.Dp)))))

/-! ## The identities -/

/-- The divergence of the bracket `κ` of the correction: `R ∂_φκ_D − 3κ_R + R ∂_uκ_R + R ∂_zκ_z =
12R³(R²D ∂_zq − n_z ∂_φq)` (uses `∇×B = 0`). -/
theorem gc_divK (u z : FA) :
    (1 + u) * PolyExprS.deriv (xB u z) (phiDir (xB u z)) eKD - 3 * PolyExprS.eval (xB u z) eKR +
    (1 + u) * PolyExprS.deriv (xB u z) (Pi.single 0 1) eKR + (1 + u) * PolyExprS.deriv (xB u z)
    (Pi.single 1 1) eKZ = 12 * (1 + u) ^ 3 * ((1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp *
    PolyExprS.eval (xB u z) eqz - PolyExpr.eval (xB u z) KamNewton.nZp * PolyExprS.eval (xB u z)
    eqph) := by
  have h_D_d0 := pd0_D (xB u z)
  have h_D_d1 := pd1_D (xB u z)
  have h_D_ph := phiD_D (xB u z)
  have h_D_uz := sym_uz_D (xB u z)
  have h_D_uph := sym_uph_D (xB u z)
  have h_D_zph := sym_zph_D (xB u z)
  have h_nR_d0 := pd0_nR (xB u z)
  have h_nR_d1 := pd1_nR (xB u z)
  have h_nR_ph := phiD_nR (xB u z)
  have h_nR_uz := sym_uz_nR (xB u z)
  have h_nR_uph := sym_uph_nR (xB u z)
  have h_nR_zph := sym_zph_nR (xB u z)
  have h_nZ_d0 := pd0_nZ (xB u z)
  have h_nZ_d1 := pd1_nZ (xB u z)
  have h_nZ_ph := phiD_nZ (xB u z)
  have h_nZ_uz := sym_uz_nZ (xB u z)
  have h_nZ_uph := sym_uph_nZ (xB u z)
  have h_nZ_zph := sym_zph_nZ (xB u z)
  have h_curl2 := curl2 (xB u z)
  have h_curl3 := curl3 (xB u z)
  have h_curl1 := curl1 (xB u z)
  simp only [eKD, eKR, eKZ, eR, eq, eqR, eqz, eqph, PolyExprS.eval, PolyExprS.deriv,
    PolyExprS.eval_ofPoly, PolyExprS.deriv_ofPoly, deriv_single, deriv_phiDir, xB_zero, single_00,
    single_10, phiDir_0, map_one, map_ofNat] at *
  set Dp_d0 := pd (xB u z) 0 KamNewton.Dp with hdef_Dp_d0
  set Dp_d1 := pd (xB u z) 1 KamNewton.Dp with hdef_Dp_d1
  set Dp_dph := phiD (xB u z) KamNewton.Dp with hdef_Dp_dph
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DphP_d0 := pd (xB u z) 0 DphP with hdef_DphP_d0
  set DphP_d1 := pd (xB u z) 1 DphP with hdef_DphP_d1
  set DphP_v := PolyExpr.eval (xB u z) DphP with hdef_DphP_v
  set DuP_d1 := pd (xB u z) 1 DuP with hdef_DuP_d1
  set DuP_dph := phiD (xB u z) DuP with hdef_DuP_dph
  set DuP_v := PolyExpr.eval (xB u z) DuP with hdef_DuP_v
  set DzP_d0 := pd (xB u z) 0 DzP with hdef_DzP_d0
  set DzP_dph := phiD (xB u z) DzP with hdef_DzP_dph
  set DzP_v := PolyExpr.eval (xB u z) DzP with hdef_DzP_v
  set nRp_d0 := pd (xB u z) 0 KamNewton.nRp with hdef_nRp_d0
  set nRp_d1 := pd (xB u z) 1 KamNewton.nRp with hdef_nRp_d1
  set nRp_dph := phiD (xB u z) KamNewton.nRp with hdef_nRp_dph
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRphP_d0 := pd (xB u z) 0 nRphP with hdef_nRphP_d0
  set nRphP_d1 := pd (xB u z) 1 nRphP with hdef_nRphP_d1
  set nRphP_v := PolyExpr.eval (xB u z) nRphP with hdef_nRphP_v
  set nRuP_d1 := pd (xB u z) 1 nRuP with hdef_nRuP_d1
  set nRuP_dph := phiD (xB u z) nRuP with hdef_nRuP_dph
  set nRuP_v := PolyExpr.eval (xB u z) nRuP with hdef_nRuP_v
  set nRzP_d0 := pd (xB u z) 0 nRzP with hdef_nRzP_d0
  set nRzP_dph := phiD (xB u z) nRzP with hdef_nRzP_dph
  set nRzP_v := PolyExpr.eval (xB u z) nRzP with hdef_nRzP_v
  set nZp_d0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZp_d0
  set nZp_d1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZp_d1
  set nZp_dph := phiD (xB u z) KamNewton.nZp with hdef_nZp_dph
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZphP_d0 := pd (xB u z) 0 nZphP with hdef_nZphP_d0
  set nZphP_d1 := pd (xB u z) 1 nZphP with hdef_nZphP_d1
  set nZphP_v := PolyExpr.eval (xB u z) nZphP with hdef_nZphP_v
  set nZuP_d1 := pd (xB u z) 1 nZuP with hdef_nZuP_d1
  set nZuP_dph := phiD (xB u z) nZuP with hdef_nZuP_dph
  set nZuP_v := PolyExpr.eval (xB u z) nZuP with hdef_nZuP_v
  set nZzP_d0 := pd (xB u z) 0 nZzP with hdef_nZzP_d0
  set nZzP_dph := phiD (xB u z) nZzP with hdef_nZzP_dph
  set nZzP_v := PolyExpr.eval (xB u z) nZzP with hdef_nZzP_v
  have e_D_d0 : Dp_d0 = DuP_v := by linear_combination (1) * h_D_d0
  have e_D_d1 : Dp_d1 = DzP_v := by linear_combination (1) * h_D_d1
  have e_D_ph : Dp_dph = DphP_v := by linear_combination (1) * h_D_ph
  have e_D_uz : DzP_d0 = DuP_d1 := by linear_combination (-1) * h_D_uz
  have e_D_uph : DphP_d0 = DuP_dph := by linear_combination (-1) * h_D_uph
  have e_D_zph : DphP_d1 = DzP_dph := by linear_combination (-1) * h_D_zph
  have e_nR_d0 : nRp_d0 = nRuP_v := by linear_combination (1) * h_nR_d0
  have e_nR_d1 : nRp_d1 = nRzP_v := by linear_combination (1) * h_nR_d1
  have e_nR_ph : nRp_dph = nRphP_v := by linear_combination (1) * h_nR_ph
  have e_nR_uz : nRzP_d0 = nRuP_d1 := by linear_combination (-1) * h_nR_uz
  have e_nR_uph : nRphP_d0 = nRuP_dph := by linear_combination (-1) * h_nR_uph
  have e_nR_zph : nRphP_d1 = nRzP_dph := by linear_combination (-1) * h_nR_zph
  have e_nZ_d0 : nZp_d0 = nZuP_v := by linear_combination (1) * h_nZ_d0
  have e_nZ_d1 : nZp_d1 = nZzP_v := by linear_combination (1) * h_nZ_d1
  have e_nZ_ph : nZp_dph = nZphP_v := by linear_combination (1) * h_nZ_ph
  have e_nZ_uz : nZzP_d0 = nZuP_d1 := by linear_combination (-1) * h_nZ_uz
  have e_nZ_uph : nZphP_d0 = nZuP_dph := by linear_combination (-1) * h_nZ_uph
  have e_nZ_zph : nZphP_d1 = nZzP_dph := by linear_combination (-1) * h_nZ_zph
  have e_curl2 : nZphP_v = DzP_v + DzP_v*u^2 + 2*DzP_v*u := by linear_combination (1) * h_curl2
  have e_curl3 : nRphP_v = DuP_v - 2*Dp_v + DuP_v*u^2 - 2*Dp_v*u + 2*DuP_v*u
      := by linear_combination (-1) * h_curl3
  simp only [e_D_d0, e_D_d1, e_D_ph, e_D_uz, e_D_uph, e_D_zph, e_nR_d0, e_nR_d1, e_nR_ph,
    e_nR_uz, e_nR_uph, e_nR_zph, e_nZ_d0, e_nZ_d1, e_nZ_ph, e_nZ_uz, e_nZ_uph, e_nZ_zph, e_curl2,
    e_curl3] at h_curl1 ⊢
  have q_curl1 : nRzP_v - nZuP_v + 4*nZp_v + u*nRzP_v - u*nZuP_v = 0
      := by linear_combination h_curl1
  linear_combination (-4*Dp_v*nRp_v + 2*Dp_v*DphP_v + 2*DuP_v*nRp_v + 2*DzP_v*nZp_v -
    24*Dp_v*nRp_v*u^2 - 16*Dp_v*u*nRp_v - 16*Dp_v*nRp_v*u^3 - 4*Dp_v*nRp_v*u^4 + 2*Dp_v*DphP_v*u^5
    + 2*DuP_v*nRp_v*u^5 + 2*DzP_v*nZp_v*u^5 + 10*Dp_v*DphP_v*u + 10*Dp_v*DphP_v*u^4 +
    10*DuP_v*u*nRp_v + 10*DuP_v*nRp_v*u^4 + 10*DzP_v*u*nZp_v + 10*DzP_v*nZp_v*u^4 +
    20*Dp_v*DphP_v*u^2 + 20*Dp_v*DphP_v*u^3 + 20*DuP_v*nRp_v*u^2 + 20*DuP_v*nRp_v*u^3 +
    20*DzP_v*nZp_v*u^2 + 20*DzP_v*nZp_v*u^3) * q_curl1

/-- The bracket `κ` against `∇q`: `κ_D ∂_φq + κ_R ∂_uq + κ_z ∂_zq = 8R² q (R²D ∂_zq − n_z ∂_φq)`. -/
theorem gc_gradK (u z : FA) :
    PolyExprS.eval (xB u z) eKD * (2 * PolyExpr.eval (xB u z) KamNewton.nRp * phiD (xB u z)
    KamNewton.nRp + 2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp * phiD (xB u z)
    KamNewton.Dp + 2 * PolyExpr.eval (xB u z) KamNewton.nZp * phiD (xB u z) KamNewton.nZp) +
    PolyExprS.eval (xB u z) eKR * (2 * PolyExpr.eval (xB u z) KamNewton.nRp * pd (xB u z) 0
    KamNewton.nRp + 2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp * pd (xB u z) 0
    KamNewton.Dp + 2 * PolyExpr.eval (xB u z) KamNewton.nZp * pd (xB u z) 0 KamNewton.nZp + 2 * (1
    + u) * PolyExpr.eval (xB u z) KamNewton.Dp ^ 2) + PolyExprS.eval (xB u z) eKZ * (2 *
    PolyExpr.eval (xB u z) KamNewton.nRp * pd (xB u z) 1 KamNewton.nRp + 2 * (1 + u) ^ 2 *
    PolyExpr.eval (xB u z) KamNewton.Dp * pd (xB u z) 1 KamNewton.Dp + 2 * PolyExpr.eval (xB u z)
    KamNewton.nZp * pd (xB u z) 1 KamNewton.nZp) = 8 * (1 + u) ^ 2 * PolyExprS.eval (xB u z) eq *
    ((1 + u) ^ 2 * PolyExpr.eval (xB u z) KamNewton.Dp * PolyExprS.eval (xB u z) eqz -
    PolyExpr.eval (xB u z) KamNewton.nZp * PolyExprS.eval (xB u z) eqph) := by
  have h_D_d0 := pd0_D (xB u z)
  have h_D_d1 := pd1_D (xB u z)
  have h_D_ph := phiD_D (xB u z)
  have h_nR_d0 := pd0_nR (xB u z)
  have h_nR_d1 := pd1_nR (xB u z)
  have h_nR_ph := phiD_nR (xB u z)
  have h_nZ_d0 := pd0_nZ (xB u z)
  have h_nZ_d1 := pd1_nZ (xB u z)
  have h_nZ_ph := phiD_nZ (xB u z)
  have h_curl2 := curl2 (xB u z)
  have h_curl3 := curl3 (xB u z)
  simp only [eKD, eKR, eKZ, eR, eq, eqR, eqz, eqph, PolyExprS.eval, PolyExprS.eval_ofPoly,
    xB_zero, map_one, map_ofNat] at *
  set Dp_d0 := pd (xB u z) 0 KamNewton.Dp with hdef_Dp_d0
  set Dp_d1 := pd (xB u z) 1 KamNewton.Dp with hdef_Dp_d1
  set Dp_dph := phiD (xB u z) KamNewton.Dp with hdef_Dp_dph
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DphP_v := PolyExpr.eval (xB u z) DphP with hdef_DphP_v
  set DuP_v := PolyExpr.eval (xB u z) DuP with hdef_DuP_v
  set DzP_v := PolyExpr.eval (xB u z) DzP with hdef_DzP_v
  set nRp_d0 := pd (xB u z) 0 KamNewton.nRp with hdef_nRp_d0
  set nRp_d1 := pd (xB u z) 1 KamNewton.nRp with hdef_nRp_d1
  set nRp_dph := phiD (xB u z) KamNewton.nRp with hdef_nRp_dph
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRphP_v := PolyExpr.eval (xB u z) nRphP with hdef_nRphP_v
  set nRuP_v := PolyExpr.eval (xB u z) nRuP with hdef_nRuP_v
  set nRzP_v := PolyExpr.eval (xB u z) nRzP with hdef_nRzP_v
  set nZp_d0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZp_d0
  set nZp_d1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZp_d1
  set nZp_dph := phiD (xB u z) KamNewton.nZp with hdef_nZp_dph
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZphP_v := PolyExpr.eval (xB u z) nZphP with hdef_nZphP_v
  set nZuP_v := PolyExpr.eval (xB u z) nZuP with hdef_nZuP_v
  set nZzP_v := PolyExpr.eval (xB u z) nZzP with hdef_nZzP_v
  have e_D_d0 : Dp_d0 = DuP_v := by linear_combination (1) * h_D_d0
  have e_D_d1 : Dp_d1 = DzP_v := by linear_combination (1) * h_D_d1
  have e_D_ph : Dp_dph = DphP_v := by linear_combination (1) * h_D_ph
  have e_nR_d0 : nRp_d0 = nRuP_v := by linear_combination (1) * h_nR_d0
  have e_nR_d1 : nRp_d1 = nRzP_v := by linear_combination (1) * h_nR_d1
  have e_nR_ph : nRp_dph = nRphP_v := by linear_combination (1) * h_nR_ph
  have e_nZ_d0 : nZp_d0 = nZuP_v := by linear_combination (1) * h_nZ_d0
  have e_nZ_d1 : nZp_d1 = nZzP_v := by linear_combination (1) * h_nZ_d1
  have e_nZ_ph : nZp_dph = nZphP_v := by linear_combination (1) * h_nZ_ph
  have e_curl2 : nZphP_v = DzP_v + DzP_v*u^2 + 2*DzP_v*u := by linear_combination (1) * h_curl2
  have e_curl3 : nRphP_v = DuP_v - 2*Dp_v + DuP_v*u^2 - 2*Dp_v*u + 2*DuP_v*u
      := by linear_combination (-1) * h_curl3
  simp only [e_D_d0, e_D_d1, e_D_ph, e_nR_d0, e_nR_d1, e_nR_ph, e_nZ_d0, e_nZ_d1, e_nZ_ph,
    e_curl2, e_curl3]
  ring

/-- Derivative of `W³`: `D(W³) = −(3/2) W³ W² Dq` (`W = q^{−1/2}`). -/
theorem gc_W3_d0 (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1) :
    PolyExprS.deriv (xB u z) (Pi.single 0 1) eW3 = -(3 * algebraMap ℂ FA (1 / 2 : ℂ) *
    PolyExprS.eval (xB u z) eW3 * PolyExprS.eval (xB u z) eW ^ 2 * (2 * PolyExpr.eval (xB u z)
    KamNewton.nRp * pd (xB u z) 0 KamNewton.nRp + 2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z)
    KamNewton.Dp * pd (xB u z) 0 KamNewton.Dp + 2 * PolyExpr.eval (xB u z) KamNewton.nZp * pd (xB
    u z) 0 KamNewton.nZp + 2 * (1 + u) * PolyExpr.eval (xB u z) KamNewton.Dp ^ 2)) := by
  have h_D_d0 := pd0_D (xB u z)
  have h_nR_d0 := pd0_nR (xB u z)
  have h_nZ_d0 := pd0_nZ (xB u z)
  have h_E_d0 := E_d0 (xB u z)
  have h_E := E_val (xB u z)
  have h_half := half_rel
  simp only [eW3, eW, PolyExprS.eval, PolyExprS.deriv, PolyExprS.eval_ofPoly,
    PolyExprS.deriv_ofPoly, deriv_eV, deriv_single, xB_zero] at *
  set Dp_d0 := pd (xB u z) 0 KamNewton.Dp with hdef_Dp_d0
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DuP_v := PolyExpr.eval (xB u z) DuP with hdef_DuP_v
  set EpP_d0 := pd (xB u z) 0 EpP with hdef_EpP_d0
  set EpP_v := PolyExpr.eval (xB u z) EpP with hdef_EpP_v
  set PuP_d0 := pd (xB u z) 0 PuP with hdef_PuP_d0
  set PuP_v := PolyExpr.eval (xB u z) PuP with hdef_PuP_v
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set hA := algebraMap ℂ FA (1 / 2 : ℂ) with hdef_hA
  set nRp_d0 := pd (xB u z) 0 KamNewton.nRp with hdef_nRp_d0
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRuP_v := PolyExpr.eval (xB u z) nRuP with hdef_nRuP_v
  set nZp_d0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZp_d0
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZuP_v := PolyExpr.eval (xB u z) nZuP with hdef_nZuP_v
  have e_D_d0 : Dp_d0 = DuP_v := by linear_combination (1) * h_D_d0
  have e_nR_d0 : nRp_d0 = nRuP_v := by linear_combination (1) * h_nR_d0
  have e_nZ_d0 : nZp_d0 = nZuP_v := by linear_combination (1) * h_nZ_d0
  have e_E_d0 : EpP_d0 = 2*Dp_v^2*PuP_v^2 + 2*Dp_d0*Dp_v*PuP_v^2 + 2*PuP_d0*PuP_v*Dp_v^2 +
      2*PuP_d0*PuP_v*nRp_v^2 + 2*PuP_d0*PuP_v*nZp_v^2 + 2*u*Dp_v^2*PuP_v^2 +
      2*nRp_d0*nRp_v*PuP_v^2 + 2*nZp_d0*nZp_v*PuP_v^2 + 2*Dp_d0*Dp_v*PuP_v^2*u^2 +
      2*PuP_d0*PuP_v*Dp_v^2*u^2 + 4*Dp_d0*Dp_v*u*PuP_v^2 + 4*PuP_d0*PuP_v*u*Dp_v^2
      := by linear_combination (1) * h_E_d0
  have e_E : EpP_v = -1 + Dp_v^2*PuP_v^2 + PuP_v^2*nRp_v^2 + PuP_v^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2 + 2*u*Dp_v^2*PuP_v^2 := by linear_combination (1) * h_E
  simp only [e_D_d0, e_nR_d0, e_nZ_d0, e_E_d0, e_E] at h_half hV ⊢
  have q_half : -1 + 2*hA = 0 := by linear_combination h_half
  have q_V : -1 + Dp_v^2*PuP_v^2*V^2 + PuP_v^2*V^2*nRp_v^2 + PuP_v^2*V^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2*V^2 + 2*u*Dp_v^2*PuP_v^2*V^2 = 0 := by linear_combination hV
  linear_combination (-3*PuP_d0*Dp_v^2*PuP_v^4*V^5 - 3*PuP_d0*PuP_v^4*V^5*nRp_v^2 -
    3*PuP_d0*PuP_v^4*V^5*nZp_v^2 - 6*PuP_d0*u*Dp_v^2*PuP_v^4*V^5 -
    3*PuP_d0*Dp_v^2*PuP_v^4*u^2*V^5) * q_half + (-3*PuP_d0*PuP_v^2*V^3) * q_V

/-- Derivative of `W³`: `D(W³) = −(3/2) W³ W² Dq` (`W = q^{−1/2}`). -/
theorem gc_W3_d1 (u z : FA) :
    PolyExprS.deriv (xB u z) (Pi.single 1 1) eW3 = -(3 * algebraMap ℂ FA (1 / 2 : ℂ) *
    PolyExprS.eval (xB u z) eW3 * PolyExprS.eval (xB u z) eW ^ 2 * (2 * PolyExpr.eval (xB u z)
    KamNewton.nRp * pd (xB u z) 1 KamNewton.nRp + 2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z)
    KamNewton.Dp * pd (xB u z) 1 KamNewton.Dp + 2 * PolyExpr.eval (xB u z) KamNewton.nZp * pd (xB
    u z) 1 KamNewton.nZp)) := by
  have h_D_d1 := pd1_D (xB u z)
  have h_nR_d1 := pd1_nR (xB u z)
  have h_nZ_d1 := pd1_nZ (xB u z)
  have h_P_d1 := P_d1 (xB u z)
  have h_E_d1 := E_d1 (xB u z)
  simp only [eW3, eW, PolyExprS.eval, PolyExprS.deriv, PolyExprS.eval_ofPoly,
    PolyExprS.deriv_ofPoly, deriv_eV, deriv_single, xB_zero] at *
  set Dp_d1 := pd (xB u z) 1 KamNewton.Dp with hdef_Dp_d1
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DzP_v := PolyExpr.eval (xB u z) DzP with hdef_DzP_v
  set EpP_d1 := pd (xB u z) 1 EpP with hdef_EpP_d1
  set PuP_d1 := pd (xB u z) 1 PuP with hdef_PuP_d1
  set PuP_v := PolyExpr.eval (xB u z) PuP with hdef_PuP_v
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set hA := algebraMap ℂ FA (1 / 2 : ℂ) with hdef_hA
  set nRp_d1 := pd (xB u z) 1 KamNewton.nRp with hdef_nRp_d1
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRzP_v := PolyExpr.eval (xB u z) nRzP with hdef_nRzP_v
  set nZp_d1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZp_d1
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZzP_v := PolyExpr.eval (xB u z) nZzP with hdef_nZzP_v
  have e_D_d1 : Dp_d1 = DzP_v := by linear_combination (1) * h_D_d1
  have e_nR_d1 : nRp_d1 = nRzP_v := by linear_combination (1) * h_nR_d1
  have e_nZ_d1 : nZp_d1 = nZzP_v := by linear_combination (1) * h_nZ_d1
  have e_P_d1 : PuP_d1 = 0 := by linear_combination (1) * h_P_d1
  have e_E_d1 : EpP_d1 = 2*Dp_d1*Dp_v*PuP_v^2 + 2*PuP_d1*PuP_v*Dp_v^2 + 2*PuP_d1*PuP_v*nRp_v^2 +
      2*PuP_d1*PuP_v*nZp_v^2 + 2*nRp_d1*nRp_v*PuP_v^2 + 2*nZp_d1*nZp_v*PuP_v^2 +
      2*Dp_d1*Dp_v*PuP_v^2*u^2 + 2*PuP_d1*PuP_v*Dp_v^2*u^2 + 4*Dp_d1*Dp_v*u*PuP_v^2 +
      4*PuP_d1*PuP_v*u*Dp_v^2 := by linear_combination (1) * h_E_d1
  simp only [e_D_d1, e_nR_d1, e_nZ_d1, e_P_d1, e_E_d1]
  ring

/-- Derivative of `W³`: `D(W³) = −(3/2) W³ W² Dq` (`W = q^{−1/2}`). -/
theorem gc_W3_dph (u z : FA) :
    PolyExprS.deriv (xB u z) (phiDir (xB u z)) eW3 = -(3 * algebraMap ℂ FA (1 / 2 : ℂ) *
    PolyExprS.eval (xB u z) eW3 * PolyExprS.eval (xB u z) eW ^ 2 * (2 * PolyExpr.eval (xB u z)
    KamNewton.nRp * phiD (xB u z) KamNewton.nRp + 2 * (1 + u) ^ 2 * PolyExpr.eval (xB u z)
    KamNewton.Dp * phiD (xB u z) KamNewton.Dp + 2 * PolyExpr.eval (xB u z) KamNewton.nZp * phiD
    (xB u z) KamNewton.nZp)) := by
  have h_D_ph := phiD_D (xB u z)
  have h_nR_ph := phiD_nR (xB u z)
  have h_nZ_ph := phiD_nZ (xB u z)
  have h_P_dph := P_dph (xB u z)
  have h_E_dph := E_dph (xB u z)
  have h_curl2 := curl2 (xB u z)
  have h_curl3 := curl3 (xB u z)
  simp only [eW3, eW, PolyExprS.eval, PolyExprS.deriv, PolyExprS.eval_ofPoly,
    PolyExprS.deriv_ofPoly, deriv_eV, deriv_phiDir, xB_zero] at *
  set Dp_dph := phiD (xB u z) KamNewton.Dp with hdef_Dp_dph
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DphP_v := PolyExpr.eval (xB u z) DphP with hdef_DphP_v
  set DuP_v := PolyExpr.eval (xB u z) DuP with hdef_DuP_v
  set DzP_v := PolyExpr.eval (xB u z) DzP with hdef_DzP_v
  set EpP_dph := phiD (xB u z) EpP with hdef_EpP_dph
  set PuP_dph := phiD (xB u z) PuP with hdef_PuP_dph
  set PuP_v := PolyExpr.eval (xB u z) PuP with hdef_PuP_v
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set hA := algebraMap ℂ FA (1 / 2 : ℂ) with hdef_hA
  set nRp_dph := phiD (xB u z) KamNewton.nRp with hdef_nRp_dph
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRphP_v := PolyExpr.eval (xB u z) nRphP with hdef_nRphP_v
  set nZp_dph := phiD (xB u z) KamNewton.nZp with hdef_nZp_dph
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZphP_v := PolyExpr.eval (xB u z) nZphP with hdef_nZphP_v
  have e_D_ph : Dp_dph = DphP_v := by linear_combination (1) * h_D_ph
  have e_nR_ph : nRp_dph = nRphP_v := by linear_combination (1) * h_nR_ph
  have e_nZ_ph : nZp_dph = nZphP_v := by linear_combination (1) * h_nZ_ph
  have e_P_dph : PuP_dph = 0 := by linear_combination (1) * h_P_dph
  have e_E_dph : EpP_dph = 2*Dp_dph*Dp_v*PuP_v^2 + 2*PuP_dph*PuP_v*Dp_v^2 +
      2*PuP_dph*PuP_v*nRp_v^2 + 2*PuP_dph*PuP_v*nZp_v^2 + 2*nRp_dph*nRp_v*PuP_v^2 +
      2*nZp_dph*nZp_v*PuP_v^2 + 2*Dp_dph*Dp_v*PuP_v^2*u^2 + 2*PuP_dph*PuP_v*Dp_v^2*u^2 +
      4*Dp_dph*Dp_v*u*PuP_v^2 + 4*PuP_dph*PuP_v*u*Dp_v^2 := by linear_combination (1) * h_E_dph
  have e_curl2 : nZphP_v = DzP_v + DzP_v*u^2 + 2*DzP_v*u := by linear_combination (1) * h_curl2
  have e_curl3 : nRphP_v = DuP_v - 2*Dp_v + DuP_v*u^2 - 2*Dp_v*u + 2*DuP_v*u
      := by linear_combination (-1) * h_curl3
  simp only [e_D_ph, e_nR_ph, e_nZ_ph, e_P_dph, e_E_dph, e_curl2, e_curl3]
  ring

/-- `W² q = 1`. -/
theorem gc_Wq (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1) :
    PolyExprS.eval (xB u z) eW ^ 2 * PolyExprS.eval (xB u z) eq = 1 := by
  have h_E := E_val (xB u z)
  simp only [eW, eq, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, xB_zero, map_one] at *
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set EpP_v := PolyExpr.eval (xB u z) EpP with hdef_EpP_v
  set PuP_v := PolyExpr.eval (xB u z) PuP with hdef_PuP_v
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  have e_E : EpP_v = -1 + Dp_v^2*PuP_v^2 + PuP_v^2*nRp_v^2 + PuP_v^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2 + 2*u*Dp_v^2*PuP_v^2 := by linear_combination (1) * h_E
  simp only [e_E] at hV ⊢
  have q_V : -1 + Dp_v^2*PuP_v^2*V^2 + PuP_v^2*V^2*nRp_v^2 + PuP_v^2*V^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2*V^2 + 2*u*Dp_v^2*PuP_v^2*V^2 = 0 := by linear_combination hV
  linear_combination (1) * q_V

/-- **Divergence-free identity** of the guiding-centre flow form.
Proof: the divergence of the correction `ρ/2 · W³ κ` splits into `W³ div κ`
(`gc_divK`) and `κ · ∇(W³)` (`gc_W3_d*`, `gc_gradK`, `gc_Wq`). -/
theorem gc_divFree (ρ : ℝ) (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1) :
    (1 + u) * phiDS (xB u z) (gcD ρ) - 3 * PolyExprS.eval (xB u z) (gcNR ρ) + (1 + u) * pdS (xB u
    z) 0 (gcNR ρ) + (1 + u) * pdS (xB u z) 1 (gcNZ ρ) = 0 := by
  have h1 := gc_divK u z
  have h2 := gc_gradK u z
  have h3 := gc_W3_d0 u z hV
  have h4 := gc_W3_d1 u z
  have h5 := gc_W3_dph u z
  have h6 := gc_Wq u z hV
  have h7 := KamNewton.divFree (xB u z)
  have h8 := half_rel
  simp only [phiDS_eq_deriv, pdS, gcD, gcNR, gcNZ, PolyExprS.eval, PolyExprS.deriv,
    PolyExprS.eval_ofPoly, PolyExprS.deriv_ofPoly, deriv_single, deriv_phiDir, xB_zero] at *
  set W3_v := PolyExprS.eval (xB u z) eW3 with hdef_W3_v
  set W3_d0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eW3 with hdef_W3_d0
  set W3_d1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eW3 with hdef_W3_d1
  set W3_dph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eW3 with hdef_W3_dph
  set W_v := PolyExprS.eval (xB u z) eW with hdef_W_v
  set KD_v := PolyExprS.eval (xB u z) eKD with hdef_KD_v
  set KD_dph := PolyExprS.deriv (xB u z) (phiDir (xB u z)) eKD with hdef_KD_dph
  set KR_v := PolyExprS.eval (xB u z) eKR with hdef_KR_v
  set KR_d0 := PolyExprS.deriv (xB u z) (Pi.single 0 1) eKR with hdef_KR_d0
  set KZ_v := PolyExprS.eval (xB u z) eKZ with hdef_KZ_v
  set KZ_d1 := PolyExprS.deriv (xB u z) (Pi.single 1 1) eKZ with hdef_KZ_d1
  set q_v := PolyExprS.eval (xB u z) eq with hdef_q_v
  set qz_v := PolyExprS.eval (xB u z) eqz with hdef_qz_v
  set qph_v := PolyExprS.eval (xB u z) eqph with hdef_qph_v
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  set hA := algebraMap ℂ FA (1 / 2 : ℂ) with hdef_hA
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set Dp_d0 := pd (xB u z) 0 KamNewton.Dp with hdef_Dp_d0
  set Dp_d1 := pd (xB u z) 1 KamNewton.Dp with hdef_Dp_d1
  set Dp_dph := phiD (xB u z) KamNewton.Dp with hdef_Dp_dph
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRp_d0 := pd (xB u z) 0 KamNewton.nRp with hdef_nRp_d0
  set nRp_d1 := pd (xB u z) 1 KamNewton.nRp with hdef_nRp_d1
  set nRp_dph := phiD (xB u z) KamNewton.nRp with hdef_nRp_dph
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZp_d0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZp_d0
  set nZp_d1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZp_d1
  set nZp_dph := phiD (xB u z) KamNewton.nZp with hdef_nZp_dph
  linear_combination h7 + (W3_v*hA*rA) * h1 + (KR_v*hA*rA + KR_v*u*hA*rA) * h3 + (KZ_v*hA*rA +
    KZ_v*u*hA*rA) * h4 + (KD_v*hA*rA + KD_v*u*hA*rA) * h5 + (-3*W3_v*rA*W_v^2*hA^2 -
    3*u*W3_v*rA*W_v^2*hA^2) * h2 + (-24*Dp_v*W3_v*qz_v*rA*hA^2 + 24*W3_v*nZp_v*qph_v*rA*hA^2 -
    240*Dp_v*W3_v*qz_v*rA*u^2*hA^2 - 240*Dp_v*W3_v*qz_v*rA*u^3*hA^2 - 120*Dp_v*u*W3_v*qz_v*rA*hA^2
    - 120*Dp_v*W3_v*qz_v*rA*u^4*hA^2 - 24*Dp_v*W3_v*qz_v*rA*u^5*hA^2 +
    24*W3_v*nZp_v*qph_v*rA*u^3*hA^2 + 72*u*W3_v*nZp_v*qph_v*rA*hA^2 +
    72*W3_v*nZp_v*qph_v*rA*u^2*hA^2) * h6 + (-12*Dp_v*W3_v*hA*qz_v*rA + 12*W3_v*hA*nZp_v*qph_v*rA
    - 120*Dp_v*W3_v*hA*qz_v*rA*u^2 - 120*Dp_v*W3_v*hA*qz_v*rA*u^3 - 60*Dp_v*u*W3_v*hA*qz_v*rA -
    60*Dp_v*W3_v*hA*qz_v*rA*u^4 - 12*Dp_v*W3_v*hA*qz_v*rA*u^5 + 12*W3_v*hA*nZp_v*qph_v*rA*u^3 +
    36*u*W3_v*hA*nZp_v*qph_v*rA + 36*W3_v*hA*nZp_v*qph_v*rA*u^2) * h8

/-- **Flux primitive identity** (a) of the guiding-centre flow form. Certificate: rewriting with the
relations of `Design/RationalStellaratorGCPoly`, then `linear_combination` (generated). -/
theorem gc_flux_a (ρ : ℝ) (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1) :
    (1 + u) * pdS (xB u z) 0 (gcPb ρ) - 2 * PolyExprS.eval (xB u z) (gcPb ρ) - (1 + u) ^ 2 * pdS
    (xB u z) 1 (gcPa ρ) = PolyExprS.eval (xB u z) (gcD ρ) := by
  simp only [pdS]
  have h_D_d0 := pd0_D (xB u z)
  have h_D_d1 := pd1_D (xB u z)
  have h_nR_d0 := pd0_nR (xB u z)
  have h_nR_d1 := pd1_nR (xB u z)
  have h_nZ_d0 := pd0_nZ (xB u z)
  have h_nZ_d1 := pd1_nZ (xB u z)
  have h_P_d1 := P_d1 (xB u z)
  have h_E_d0 := E_d0 (xB u z)
  have h_E_d1 := E_d1 (xB u z)
  have h_E := E_val (xB u z)
  have h_fa := KamNewton.flux_a (xB u z)
  have h_half := half_rel
  have h_curl1 := curl1 (xB u z)
  simp only [gcPb, gcPa, gcD, eR, eW, eW3, eqR, eq, eqz, eKD, PolyExprS.eval, PolyExprS.deriv,
    PolyExprS.eval_ofPoly, PolyExprS.deriv_ofPoly, deriv_eV, deriv_single, xB_zero, single_00,
    single_10, map_one, map_ofNat] at *
  set Dp_d0 := pd (xB u z) 0 KamNewton.Dp with hdef_Dp_d0
  set Dp_d1 := pd (xB u z) 1 KamNewton.Dp with hdef_Dp_d1
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DuP_v := PolyExpr.eval (xB u z) DuP with hdef_DuP_v
  set DzP_v := PolyExpr.eval (xB u z) DzP with hdef_DzP_v
  set EpP_d0 := pd (xB u z) 0 EpP with hdef_EpP_d0
  set EpP_d1 := pd (xB u z) 1 EpP with hdef_EpP_d1
  set EpP_v := PolyExpr.eval (xB u z) EpP with hdef_EpP_v
  set Pap_d1 := pd (xB u z) 1 KamNewton.Pap with hdef_Pap_d1
  set Pbp_d0 := pd (xB u z) 0 KamNewton.Pbp with hdef_Pbp_d0
  set Pbp_v := PolyExpr.eval (xB u z) KamNewton.Pbp with hdef_Pbp_v
  set PuP_d0 := pd (xB u z) 0 PuP with hdef_PuP_d0
  set PuP_d1 := pd (xB u z) 1 PuP with hdef_PuP_d1
  set PuP_v := PolyExpr.eval (xB u z) PuP with hdef_PuP_v
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set hA := algebraMap ℂ FA (1 / 2 : ℂ) with hdef_hA
  set nRp_d0 := pd (xB u z) 0 KamNewton.nRp with hdef_nRp_d0
  set nRp_d1 := pd (xB u z) 1 KamNewton.nRp with hdef_nRp_d1
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRuP_v := PolyExpr.eval (xB u z) nRuP with hdef_nRuP_v
  set nRzP_v := PolyExpr.eval (xB u z) nRzP with hdef_nRzP_v
  set nZp_d0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZp_d0
  set nZp_d1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZp_d1
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZuP_v := PolyExpr.eval (xB u z) nZuP with hdef_nZuP_v
  set nZzP_v := PolyExpr.eval (xB u z) nZzP with hdef_nZzP_v
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  have e_D_d0 : Dp_d0 = DuP_v := by linear_combination (1) * h_D_d0
  have e_D_d1 : Dp_d1 = DzP_v := by linear_combination (1) * h_D_d1
  have e_nR_d0 : nRp_d0 = nRuP_v := by linear_combination (1) * h_nR_d0
  have e_nR_d1 : nRp_d1 = nRzP_v := by linear_combination (1) * h_nR_d1
  have e_nZ_d0 : nZp_d0 = nZuP_v := by linear_combination (1) * h_nZ_d0
  have e_nZ_d1 : nZp_d1 = nZzP_v := by linear_combination (1) * h_nZ_d1
  have e_P_d1 : PuP_d1 = 0 := by linear_combination (1) * h_P_d1
  have e_E_d0 : EpP_d0 = 2*Dp_v^2*PuP_v^2 + 2*Dp_d0*Dp_v*PuP_v^2 + 2*PuP_d0*PuP_v*Dp_v^2 +
      2*PuP_d0*PuP_v*nRp_v^2 + 2*PuP_d0*PuP_v*nZp_v^2 + 2*u*Dp_v^2*PuP_v^2 +
      2*nRp_d0*nRp_v*PuP_v^2 + 2*nZp_d0*nZp_v*PuP_v^2 + 2*Dp_d0*Dp_v*PuP_v^2*u^2 +
      2*PuP_d0*PuP_v*Dp_v^2*u^2 + 4*Dp_d0*Dp_v*u*PuP_v^2 + 4*PuP_d0*PuP_v*u*Dp_v^2
      := by linear_combination (1) * h_E_d0
  have e_E_d1 : EpP_d1 = 2*Dp_d1*Dp_v*PuP_v^2 + 2*PuP_d1*PuP_v*Dp_v^2 + 2*PuP_d1*PuP_v*nRp_v^2 +
      2*PuP_d1*PuP_v*nZp_v^2 + 2*nRp_d1*nRp_v*PuP_v^2 + 2*nZp_d1*nZp_v*PuP_v^2 +
      2*Dp_d1*Dp_v*PuP_v^2*u^2 + 2*PuP_d1*PuP_v*Dp_v^2*u^2 + 4*Dp_d1*Dp_v*u*PuP_v^2 +
      4*PuP_d1*PuP_v*u*Dp_v^2 := by linear_combination (1) * h_E_d1
  have e_E : EpP_v = -1 + Dp_v^2*PuP_v^2 + PuP_v^2*nRp_v^2 + PuP_v^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2 + 2*u*Dp_v^2*PuP_v^2 := by linear_combination (1) * h_E
  simp only [e_D_d0, e_D_d1, e_nR_d0, e_nR_d1, e_nZ_d0, e_nZ_d1, e_P_d1, e_E_d0, e_E_d1, e_E]
    at h_fa h_half h_curl1 hV ⊢
  have q_fa : Pbp_d0 - Dp_v - Pap_d1 - 2*Pbp_v + Pbp_d0*u - Pap_d1*u^2 - 2*Pap_d1*u = 0
      := by linear_combination h_fa
  have q_half : -1 + 2*hA = 0 := by linear_combination h_half
  have q_curl1 : nRzP_v - nZuP_v + 4*nZp_v + u*nRzP_v - u*nZuP_v = 0
      := by linear_combination h_curl1
  have q_V : -1 + Dp_v^2*PuP_v^2*V^2 + PuP_v^2*V^2*nRp_v^2 + PuP_v^2*V^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2*V^2 + 2*u*Dp_v^2*PuP_v^2*V^2 = 0 := by linear_combination hV
  apply eq_of_natCast_mul_sub (n := 4) (by norm_num)
  linear_combination (4) * q_fa + (16*rA*PuP_v^3*V^3*nZp_v^3 + 4*PuP_d0*rA*PuP_v^2*V^3*nZp_v^3 +
    16*nZp_v*rA*Dp_v^2*PuP_v^3*V^3 + 16*nZp_v*rA*PuP_v^3*V^3*nRp_v^2 +
    16*rA*PuP_v^3*u^2*V^3*nZp_v^3 + 32*u*rA*PuP_v^3*V^3*nZp_v^3 +
    4*PuP_d0*nZp_v*rA*Dp_v^2*PuP_v^2*V^3 + 4*PuP_d0*nZp_v*rA*PuP_v^2*V^3*nRp_v^2 +
    4*PuP_d0*rA*PuP_v^2*u^3*V^3*nZp_v^3 + 12*PuP_d0*u*rA*PuP_v^2*V^3*nZp_v^3 +
    12*PuP_d0*rA*PuP_v^2*u^2*V^3*nZp_v^3 + 16*nZp_v*rA*Dp_v^2*PuP_v^3*u^4*V^3 +
    16*nZp_v*rA*PuP_v^3*u^2*V^3*nRp_v^2 + 32*u*nZp_v*rA*PuP_v^3*V^3*nRp_v^2 +
    64*u*nZp_v*rA*Dp_v^2*PuP_v^3*V^3 + 64*nZp_v*rA*Dp_v^2*PuP_v^3*u^3*V^3 +
    96*nZp_v*rA*Dp_v^2*PuP_v^3*u^2*V^3 + 4*PuP_d0*nZp_v*rA*Dp_v^2*PuP_v^2*u^5*V^3 +
    4*PuP_d0*nZp_v*rA*PuP_v^2*u^3*V^3*nRp_v^2 + 12*PuP_d0*u*nZp_v*rA*PuP_v^2*V^3*nRp_v^2 +
    12*PuP_d0*nZp_v*rA*PuP_v^2*u^2*V^3*nRp_v^2 + 20*PuP_d0*u*nZp_v*rA*Dp_v^2*PuP_v^2*V^3 +
    20*PuP_d0*nZp_v*rA*Dp_v^2*PuP_v^2*u^4*V^3 + 40*PuP_d0*nZp_v*rA*Dp_v^2*PuP_v^2*u^2*V^3 +
    40*PuP_d0*nZp_v*rA*Dp_v^2*PuP_v^2*u^3*V^3) * q_half + (-PuP_d0*V*rA - PuP_d0*V*rA*u^3 -
    3*PuP_d0*u*V*rA - 3*PuP_d0*V*rA*u^2 + 4*rA*Dp_v^2*PuP_v^3*V^3 + 4*rA*PuP_v^3*V^3*nRp_v^2 +
    4*rA*PuP_v^3*V^3*nZp_v^2 + PuP_d0*rA*Dp_v^2*PuP_v^2*V^3 + PuP_d0*rA*PuP_v^2*V^3*nRp_v^2 +
    PuP_d0*rA*PuP_v^2*V^3*nZp_v^2 + 4*rA*Dp_v^2*PuP_v^3*u^4*V^3 + 4*rA*PuP_v^3*u^2*V^3*nRp_v^2 +
    4*rA*PuP_v^3*u^2*V^3*nZp_v^2 + 8*u*rA*PuP_v^3*V^3*nRp_v^2 + 8*u*rA*PuP_v^3*V^3*nZp_v^2 +
    16*u*rA*Dp_v^2*PuP_v^3*V^3 + 16*rA*Dp_v^2*PuP_v^3*u^3*V^3 + 24*rA*Dp_v^2*PuP_v^3*u^2*V^3 +
    PuP_d0*rA*Dp_v^2*PuP_v^2*u^5*V^3 + PuP_d0*rA*PuP_v^2*u^3*V^3*nRp_v^2 +
    PuP_d0*rA*PuP_v^2*u^3*V^3*nZp_v^2 + 3*PuP_d0*u*rA*PuP_v^2*V^3*nRp_v^2 +
    3*PuP_d0*u*rA*PuP_v^2*V^3*nZp_v^2 + 3*PuP_d0*rA*PuP_v^2*u^2*V^3*nRp_v^2 +
    3*PuP_d0*rA*PuP_v^2*u^2*V^3*nZp_v^2 + 5*PuP_d0*u*rA*Dp_v^2*PuP_v^2*V^3 +
    5*PuP_d0*rA*Dp_v^2*PuP_v^2*u^4*V^3 + 10*PuP_d0*rA*Dp_v^2*PuP_v^2*u^2*V^3 +
    10*PuP_d0*rA*Dp_v^2*PuP_v^2*u^3*V^3) * q_curl1 + (PuP_d0*V*nZuP_v*rA - PuP_d0*V*nRzP_v*rA -
    4*PuP_v*V*nRzP_v*rA + 4*PuP_v*V*nZuP_v*rA + PuP_d0*V*nZuP_v*rA*u^4 - PuP_d0*V*nRzP_v*rA*u^4 -
    12*PuP_v*u*V*nRzP_v*rA - 12*PuP_v*V*nRzP_v*rA*u^2 - 6*PuP_d0*V*nRzP_v*rA*u^2 -
    4*PuP_d0*u*V*nRzP_v*rA - 4*PuP_d0*V*nRzP_v*rA*u^3 - 4*PuP_v*V*nRzP_v*rA*u^3 +
    4*PuP_d0*u*V*nZuP_v*rA + 4*PuP_d0*V*nZuP_v*rA*u^3 + 4*PuP_v*V*nZuP_v*rA*u^3 +
    6*PuP_d0*V*nZuP_v*rA*u^2 + 12*PuP_v*u*V*nZuP_v*rA + 12*PuP_v*V*nZuP_v*rA*u^2) * q_V

/-- **Flux primitive identity** (b) (with the `dφ`-component `P_c`). Certificate: rewriting with the
relations of `Design/RationalStellaratorGCPoly`, then `linear_combination` (generated). -/
theorem gc_flux_b (ρ : ℝ) (u z : FA)
    (hV : PolyExprS.eval (xB u z) eV ^ 2 * (1 + PolyExpr.eval (xB u z) EpP) = 1) :
    (1 + u) ^ 2 * phiDS (xB u z) (gcPa ρ) - (1 + u) ^ 3 * pdS (xB u z) 0 (gcPc ρ) = PolyExprS.eval
    (xB u z) (gcNZ ρ) := by
  simp only [phiDS_eq_deriv, pdS]
  have h_D_d0 := pd0_D (xB u z)
  have h_D_ph := phiD_D (xB u z)
  have h_nR_d0 := pd0_nR (xB u z)
  have h_nR_ph := phiD_nR (xB u z)
  have h_nZ_d0 := pd0_nZ (xB u z)
  have h_nZ_ph := phiD_nZ (xB u z)
  have h_P_dph := P_dph (xB u z)
  have h_E_d0 := E_d0 (xB u z)
  have h_E_dph := E_dph (xB u z)
  have h_E := E_val (xB u z)
  have h_curl2 := curl2 (xB u z)
  have h_curl3 := curl3 (xB u z)
  have h_fb := KamNewton.flux_b (xB u z)
  have h_half := half_rel
  simp only [gcPa, gcPc, gcNZ, eR, eW, eW3, eqph, eqR, eq, eKZ, PolyExprS.eval, PolyExprS.deriv,
    PolyExprS.eval_ofPoly, PolyExprS.deriv_ofPoly, deriv_eV, deriv_single, deriv_phiDir, xB_zero,
    single_00, phiDir_0, map_one, map_ofNat] at *
  set Dp_d0 := pd (xB u z) 0 KamNewton.Dp with hdef_Dp_d0
  set Dp_dph := phiD (xB u z) KamNewton.Dp with hdef_Dp_dph
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DphP_v := PolyExpr.eval (xB u z) DphP with hdef_DphP_v
  set DuP_v := PolyExpr.eval (xB u z) DuP with hdef_DuP_v
  set DzP_v := PolyExpr.eval (xB u z) DzP with hdef_DzP_v
  set EpP_d0 := pd (xB u z) 0 EpP with hdef_EpP_d0
  set EpP_dph := phiD (xB u z) EpP with hdef_EpP_dph
  set EpP_v := PolyExpr.eval (xB u z) EpP with hdef_EpP_v
  set Pap_dph := phiD (xB u z) KamNewton.Pap with hdef_Pap_dph
  set PuP_d0 := pd (xB u z) 0 PuP with hdef_PuP_d0
  set PuP_dph := phiD (xB u z) PuP with hdef_PuP_dph
  set PuP_v := PolyExpr.eval (xB u z) PuP with hdef_PuP_v
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set hA := algebraMap ℂ FA (1 / 2 : ℂ) with hdef_hA
  set nRp_d0 := pd (xB u z) 0 KamNewton.nRp with hdef_nRp_d0
  set nRp_dph := phiD (xB u z) KamNewton.nRp with hdef_nRp_dph
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRphP_v := PolyExpr.eval (xB u z) nRphP with hdef_nRphP_v
  set nRuP_v := PolyExpr.eval (xB u z) nRuP with hdef_nRuP_v
  set nZp_d0 := pd (xB u z) 0 KamNewton.nZp with hdef_nZp_d0
  set nZp_dph := phiD (xB u z) KamNewton.nZp with hdef_nZp_dph
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZphP_v := PolyExpr.eval (xB u z) nZphP with hdef_nZphP_v
  set nZuP_v := PolyExpr.eval (xB u z) nZuP with hdef_nZuP_v
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  have e_D_d0 : Dp_d0 = DuP_v := by linear_combination (1) * h_D_d0
  have e_D_ph : Dp_dph = DphP_v := by linear_combination (1) * h_D_ph
  have e_nR_d0 : nRp_d0 = nRuP_v := by linear_combination (1) * h_nR_d0
  have e_nR_ph : nRp_dph = nRphP_v := by linear_combination (1) * h_nR_ph
  have e_nZ_d0 : nZp_d0 = nZuP_v := by linear_combination (1) * h_nZ_d0
  have e_nZ_ph : nZp_dph = nZphP_v := by linear_combination (1) * h_nZ_ph
  have e_P_dph : PuP_dph = 0 := by linear_combination (1) * h_P_dph
  have e_E_d0 : EpP_d0 = 2*Dp_v^2*PuP_v^2 + 2*Dp_d0*Dp_v*PuP_v^2 + 2*PuP_d0*PuP_v*Dp_v^2 +
      2*PuP_d0*PuP_v*nRp_v^2 + 2*PuP_d0*PuP_v*nZp_v^2 + 2*u*Dp_v^2*PuP_v^2 +
      2*nRp_d0*nRp_v*PuP_v^2 + 2*nZp_d0*nZp_v*PuP_v^2 + 2*Dp_d0*Dp_v*PuP_v^2*u^2 +
      2*PuP_d0*PuP_v*Dp_v^2*u^2 + 4*Dp_d0*Dp_v*u*PuP_v^2 + 4*PuP_d0*PuP_v*u*Dp_v^2
      := by linear_combination (1) * h_E_d0
  have e_E_dph : EpP_dph = 2*Dp_dph*Dp_v*PuP_v^2 + 2*PuP_dph*PuP_v*Dp_v^2 +
      2*PuP_dph*PuP_v*nRp_v^2 + 2*PuP_dph*PuP_v*nZp_v^2 + 2*nRp_dph*nRp_v*PuP_v^2 +
      2*nZp_dph*nZp_v*PuP_v^2 + 2*Dp_dph*Dp_v*PuP_v^2*u^2 + 2*PuP_dph*PuP_v*Dp_v^2*u^2 +
      4*Dp_dph*Dp_v*u*PuP_v^2 + 4*PuP_dph*PuP_v*u*Dp_v^2 := by linear_combination (1) * h_E_dph
  have e_E : EpP_v = -1 + Dp_v^2*PuP_v^2 + PuP_v^2*nRp_v^2 + PuP_v^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2 + 2*u*Dp_v^2*PuP_v^2 := by linear_combination (1) * h_E
  have e_curl2 : nZphP_v = DzP_v + DzP_v*u^2 + 2*DzP_v*u := by linear_combination (1) * h_curl2
  have e_curl3 : nRphP_v = DuP_v - 2*Dp_v + DuP_v*u^2 - 2*Dp_v*u + 2*DuP_v*u
      := by linear_combination (-1) * h_curl3
  simp only [e_D_d0, e_D_ph, e_nR_d0, e_nR_ph, e_nZ_d0, e_nZ_ph, e_P_dph, e_E_d0, e_E_dph, e_E,
    e_curl2, e_curl3] at h_fb h_half hV ⊢
  have q_fb : Pap_dph - nZp_v + Pap_dph*u^2 + 2*Pap_dph*u = 0 := by linear_combination h_fb
  have q_half : -1 + 2*hA = 0 := by linear_combination h_half
  have q_V : -1 + Dp_v^2*PuP_v^2*V^2 + PuP_v^2*V^2*nRp_v^2 + PuP_v^2*V^2*nZp_v^2 +
      Dp_v^2*PuP_v^2*u^2*V^2 + 2*u*Dp_v^2*PuP_v^2*V^2 = 0 := by linear_combination hV
  linear_combination (1) * q_fb + (-4*rA*Dp_v^3*PuP_v^3*V^3 - PuP_d0*rA*Dp_v^3*PuP_v^2*V^3 -
    80*rA*Dp_v^3*PuP_v^3*u^3*V^3 - 60*rA*Dp_v^3*PuP_v^3*u^2*V^3 - 60*rA*Dp_v^3*PuP_v^3*u^4*V^3 -
    24*u*rA*Dp_v^3*PuP_v^3*V^3 - 24*rA*Dp_v^3*PuP_v^3*u^5*V^3 - 4*Dp_v*rA*PuP_v^3*V^3*nRp_v^2 -
    4*Dp_v*rA*PuP_v^3*V^3*nZp_v^2 - 4*rA*Dp_v^3*PuP_v^3*u^6*V^3 -
    Dp_v*PuP_d0*rA*PuP_v^2*V^3*nRp_v^2 - Dp_v*PuP_d0*rA*PuP_v^2*V^3*nZp_v^2 -
    PuP_d0*rA*Dp_v^3*PuP_v^2*u^7*V^3 - 35*PuP_d0*rA*Dp_v^3*PuP_v^2*u^3*V^3 -
    35*PuP_d0*rA*Dp_v^3*PuP_v^2*u^4*V^3 - 24*Dp_v*rA*PuP_v^3*u^2*V^3*nRp_v^2 -
    24*Dp_v*rA*PuP_v^3*u^2*V^3*nZp_v^2 - 21*PuP_d0*rA*Dp_v^3*PuP_v^2*u^2*V^3 -
    21*PuP_d0*rA*Dp_v^3*PuP_v^2*u^5*V^3 - 16*Dp_v*u*rA*PuP_v^3*V^3*nRp_v^2 -
    16*Dp_v*u*rA*PuP_v^3*V^3*nZp_v^2 - 16*Dp_v*rA*PuP_v^3*u^3*V^3*nRp_v^2 -
    16*Dp_v*rA*PuP_v^3*u^3*V^3*nZp_v^2 - 7*PuP_d0*u*rA*Dp_v^3*PuP_v^2*V^3 -
    7*PuP_d0*rA*Dp_v^3*PuP_v^2*u^6*V^3 - 4*Dp_v*rA*PuP_v^3*u^4*V^3*nRp_v^2 -
    4*Dp_v*rA*PuP_v^3*u^4*V^3*nZp_v^2 - Dp_v*PuP_d0*rA*PuP_v^2*u^5*V^3*nRp_v^2 -
    Dp_v*PuP_d0*rA*PuP_v^2*u^5*V^3*nZp_v^2 - 10*Dp_v*PuP_d0*rA*PuP_v^2*u^2*V^3*nRp_v^2 -
    10*Dp_v*PuP_d0*rA*PuP_v^2*u^2*V^3*nZp_v^2 - 10*Dp_v*PuP_d0*rA*PuP_v^2*u^3*V^3*nRp_v^2 -
    10*Dp_v*PuP_d0*rA*PuP_v^2*u^3*V^3*nZp_v^2 - 5*Dp_v*PuP_d0*u*rA*PuP_v^2*V^3*nRp_v^2 -
    5*Dp_v*PuP_d0*u*rA*PuP_v^2*V^3*nZp_v^2 - 5*Dp_v*PuP_d0*rA*PuP_v^2*u^4*V^3*nRp_v^2 -
    5*Dp_v*PuP_d0*rA*PuP_v^2*u^4*V^3*nZp_v^2) * q_half + (-Dp_v*PuP_d0*V*rA - 4*Dp_v*PuP_v*V*rA -
    Dp_v*PuP_d0*V*rA*u^5 - 24*Dp_v*PuP_v*V*rA*u^2 - 16*Dp_v*PuP_v*u*V*rA - 16*Dp_v*PuP_v*V*rA*u^3
    - 10*Dp_v*PuP_d0*V*rA*u^2 - 10*Dp_v*PuP_d0*V*rA*u^3 - 5*Dp_v*PuP_d0*u*V*rA -
    5*Dp_v*PuP_d0*V*rA*u^4 - 4*Dp_v*PuP_v*V*rA*u^4) * q_V

/-- **Flux primitive identity** (c) (with the `dφ`-component `P_c`). Certificate: rewriting with the
relations of `Design/RationalStellaratorGCPoly`, then `linear_combination` (generated). -/
theorem gc_flux_c (ρ : ℝ) (u z : FA) :
    (1 + u) * phiDS (xB u z) (gcPb ρ) - (1 + u) ^ 3 * pdS (xB u z) 1 (gcPc ρ) = -PolyExprS.eval
    (xB u z) (gcNR ρ) := by
  simp only [phiDS_eq_deriv, pdS]
  have h_D_d1 := pd1_D (xB u z)
  have h_D_ph := phiD_D (xB u z)
  have h_nR_d1 := pd1_nR (xB u z)
  have h_nR_ph := phiD_nR (xB u z)
  have h_nZ_d1 := pd1_nZ (xB u z)
  have h_nZ_ph := phiD_nZ (xB u z)
  have h_P_d1 := P_d1 (xB u z)
  have h_P_dph := P_dph (xB u z)
  have h_E_d1 := E_d1 (xB u z)
  have h_E_dph := E_dph (xB u z)
  have h_curl2 := curl2 (xB u z)
  have h_curl3 := curl3 (xB u z)
  have h_fc := KamNewton.flux_c (xB u z)
  simp only [gcPb, gcPc, gcNR, eR, eW, eW3, eqz, eqph, eKR, PolyExprS.eval, PolyExprS.deriv,
    PolyExprS.eval_ofPoly, PolyExprS.deriv_ofPoly, deriv_eV, deriv_single, deriv_phiDir, xB_zero,
    single_10, phiDir_0, map_one, map_ofNat] at *
  set Dp_d1 := pd (xB u z) 1 KamNewton.Dp with hdef_Dp_d1
  set Dp_dph := phiD (xB u z) KamNewton.Dp with hdef_Dp_dph
  set Dp_v := PolyExpr.eval (xB u z) KamNewton.Dp with hdef_Dp_v
  set DphP_v := PolyExpr.eval (xB u z) DphP with hdef_DphP_v
  set DuP_v := PolyExpr.eval (xB u z) DuP with hdef_DuP_v
  set DzP_v := PolyExpr.eval (xB u z) DzP with hdef_DzP_v
  set EpP_d1 := pd (xB u z) 1 EpP with hdef_EpP_d1
  set EpP_dph := phiD (xB u z) EpP with hdef_EpP_dph
  set Pbp_dph := phiD (xB u z) KamNewton.Pbp with hdef_Pbp_dph
  set PuP_d1 := pd (xB u z) 1 PuP with hdef_PuP_d1
  set PuP_dph := phiD (xB u z) PuP with hdef_PuP_dph
  set PuP_v := PolyExpr.eval (xB u z) PuP with hdef_PuP_v
  set V := PolyExprS.eval (xB u z) eV with hdef_V
  set hA := algebraMap ℂ FA (1 / 2 : ℂ) with hdef_hA
  set nRp_d1 := pd (xB u z) 1 KamNewton.nRp with hdef_nRp_d1
  set nRp_dph := phiD (xB u z) KamNewton.nRp with hdef_nRp_dph
  set nRp_v := PolyExpr.eval (xB u z) KamNewton.nRp with hdef_nRp_v
  set nRphP_v := PolyExpr.eval (xB u z) nRphP with hdef_nRphP_v
  set nRzP_v := PolyExpr.eval (xB u z) nRzP with hdef_nRzP_v
  set nZp_d1 := pd (xB u z) 1 KamNewton.nZp with hdef_nZp_d1
  set nZp_dph := phiD (xB u z) KamNewton.nZp with hdef_nZp_dph
  set nZp_v := PolyExpr.eval (xB u z) KamNewton.nZp with hdef_nZp_v
  set nZphP_v := PolyExpr.eval (xB u z) nZphP with hdef_nZphP_v
  set nZzP_v := PolyExpr.eval (xB u z) nZzP with hdef_nZzP_v
  set rA := algebraMap ℂ FA (ρ : ℂ) with hdef_rA
  have e_D_d1 : Dp_d1 = DzP_v := by linear_combination (1) * h_D_d1
  have e_D_ph : Dp_dph = DphP_v := by linear_combination (1) * h_D_ph
  have e_nR_d1 : nRp_d1 = nRzP_v := by linear_combination (1) * h_nR_d1
  have e_nR_ph : nRp_dph = nRphP_v := by linear_combination (1) * h_nR_ph
  have e_nZ_d1 : nZp_d1 = nZzP_v := by linear_combination (1) * h_nZ_d1
  have e_nZ_ph : nZp_dph = nZphP_v := by linear_combination (1) * h_nZ_ph
  have e_P_d1 : PuP_d1 = 0 := by linear_combination (1) * h_P_d1
  have e_P_dph : PuP_dph = 0 := by linear_combination (1) * h_P_dph
  have e_E_d1 : EpP_d1 = 2*Dp_d1*Dp_v*PuP_v^2 + 2*PuP_d1*PuP_v*Dp_v^2 + 2*PuP_d1*PuP_v*nRp_v^2 +
      2*PuP_d1*PuP_v*nZp_v^2 + 2*nRp_d1*nRp_v*PuP_v^2 + 2*nZp_d1*nZp_v*PuP_v^2 +
      2*Dp_d1*Dp_v*PuP_v^2*u^2 + 2*PuP_d1*PuP_v*Dp_v^2*u^2 + 4*Dp_d1*Dp_v*u*PuP_v^2 +
      4*PuP_d1*PuP_v*u*Dp_v^2 := by linear_combination (1) * h_E_d1
  have e_E_dph : EpP_dph = 2*Dp_dph*Dp_v*PuP_v^2 + 2*PuP_dph*PuP_v*Dp_v^2 +
      2*PuP_dph*PuP_v*nRp_v^2 + 2*PuP_dph*PuP_v*nZp_v^2 + 2*nRp_dph*nRp_v*PuP_v^2 +
      2*nZp_dph*nZp_v*PuP_v^2 + 2*Dp_dph*Dp_v*PuP_v^2*u^2 + 2*PuP_dph*PuP_v*Dp_v^2*u^2 +
      4*Dp_dph*Dp_v*u*PuP_v^2 + 4*PuP_dph*PuP_v*u*Dp_v^2 := by linear_combination (1) * h_E_dph
  have e_curl2 : nZphP_v = DzP_v + DzP_v*u^2 + 2*DzP_v*u := by linear_combination (1) * h_curl2
  have e_curl3 : nRphP_v = DuP_v - 2*Dp_v + DuP_v*u^2 - 2*Dp_v*u + 2*DuP_v*u
      := by linear_combination (-1) * h_curl3
  simp only [e_D_d1, e_D_ph, e_nR_d1, e_nR_ph, e_nZ_d1, e_nZ_ph, e_P_d1, e_P_dph, e_E_d1,
    e_E_dph, e_curl2, e_curl3] at h_fc ⊢
  have q_fc : Pbp_dph + nRp_v + Pbp_dph*u = 0 := by linear_combination h_fc
  linear_combination (1) * q_fc

end PlasmaLean.Design.RationalStellaratorGC
