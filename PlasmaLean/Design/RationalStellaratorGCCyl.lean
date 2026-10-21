/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGC
public import PlasmaLean.Design.RationalStellaratorGCInstance
public import PlasmaLean.Design.RationalStellaratorForeverCoords
public import PlasmaLean.Design.KamTorusAStrip

/-!
# The guiding-centre field in cylindrical coordinates

For the guiding-centre field `gcField ρ = B + ρ ∇×b` of the rational stellarator `B = field (1/4)`
(`Design/RationalStellaratorGC`), this file computes the cylindrical components at the point
`cylPt R φ z` and identifies them with the flow-form expressions `D̃, ñ_R, ñ_z` of
`Design/RationalStellaratorGCFlow` (the expressions of the KAM theorem `gc_exact_torus`).

**Real flow-form functions.** In the variables `(R, z, C, S)` (`C = cos 2φ`, `S = sin 2φ`):
`D = Dfun`, `n_R = 2εR Ps`, `n_z = εR² Pz` (`nRr`, `nZr`), `q = n_R² + R²D² + n_z² = R⁸|B|²`
(`qr`), the explicit partial derivatives `∂_R, ∂_z, ∂_φ` (`DR, Dz, Dph, …, qR, qz, qph`; the
`φ`-derivative is `−2S ∂_C + 2C ∂_S`), proved to be derivatives (`hasDerivAt_D_R`, …) and identified
with the generated polynomials `DuP, …, nZphP` of `Design/RationalStellaratorGCPoly`
(`eval_DuP_ptC`, …). With `W = q^{−1/2}` (`Wr`):

* `D̃ = D + (ρ/2) W³ R² (R n_z q_R − 8 n_z q − R n_R q_z)` (`gcDr`),
* `ñ_R = n_R + (ρ/2) W³ (R⁵ D q_z − R³ n_z q_φ)` (`gcNRr`),
* `ñ_z = n_z + (ρ/2) W³ (R³ n_R q_φ − R⁵ D q_R + 8R⁴ D q)` (`gcNZr`).

**Main results.**

* `Qf_cylPt`: `|B|² = q / R⁸` at `cylPt R φ z`;
* `gradient_Qf_cylPt`: `∇|B|² = (q_R/R⁸ − 8q/R⁹) e_R + (q_φ/R⁹) e_φ + (q_z/R⁸) e_z`;
* **`gcField_cylPt_real`**: for `R > 0` and `q > 0`,
  `gcField ρ (cylPt R φ z) = (ñ_R/R⁴) e_R + (D̃/R³) e_φ + (ñ_z/R⁴) e_z`;
* `eval_gcD_ptC`, `eval_gcNR_ptC`, `eval_gcNZ_ptC`: at a real point where the node of the
  flow-form expressions is valid (and `|R − 1| ≤ 1/4`), the `PolyExprS` expressions
  `gcD ρ, gcNR ρ, gcNZ ρ` evaluate to `D̃, ñ_R, ñ_z`;
* **`gcField_cylPt`**: hence `gcField ρ (cylPt R φ z)` has cylindrical components
  `(Re ñ_R/R⁴, Re D̃/R³, Re ñ_z/R⁴)` with `D̃, ñ` the evaluations of the flow-form expressions
  of the KAM theorem.

**Sanity.** `gcDr_zero`: for `ρ = 0` the expressions reduce to those of `field (1/4)`;
`Pu_pos`: the Taylor polynomial `P(u)` of `R^{−3}` is positive for `|u| ≤ 1/4`.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCLittlejohn PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WithLp

/-- Builds a `HasDerivAt` proof of a polynomial expression with a metavariable derivative. -/
macro "hd_build" : tactic => `(tactic| repeat (first
  | apply HasDerivAt.pow | apply HasDerivAt.add | apply HasDerivAt.sub | apply HasDerivAt.mul
  | apply HasDerivAt.neg | apply HasDerivAt.div_const
  | apply hasDerivAt_id' | apply hasDerivAt_const))

/-! ## Real flow-form functions and their partial derivatives -/

/-- `n_R = 2εR Ps = R⁴ B^R`. -/
def nRr (R z C S : ℝ) : ℝ := 2 * eps * R * Psfun R z C S

/-- `n_z = εR² Pz = R⁴ B^z`. -/
def nZr (R z C S : ℝ) : ℝ := eps * R ^ 2 * Pzfun R z C S

/-- `∂_R D`. -/
def DR (R z C S : ℝ) : ℝ :=
  2 * R + eps * (-2 * (R * (R ^ 2 - 1)) * S + 2 * (-z * R * (R ^ 2 - 3)) * C)

/-- `∂_z D`. -/
def Dz (R z C S : ℝ) : ℝ := eps * (-2 * (-2 * z) * S + 2 * sgz R z * C)

/-- `∂_φ D = −2S ∂_C D + 2C ∂_S D`. -/
def Dph (R z C S : ℝ) : ℝ := eps * (-2 * sfun R z * (2 * C) + 2 * sgfun R z * (-2 * S))

/-- `∂_R Ps`. -/
def PsR (R z C S : ℝ) : ℝ := R ^ 3 * C + (-z * R ^ 3) * S

/-- `∂_z Ps`. -/
def Psz (R z C S : ℝ) : ℝ := 2 * z * C + (-(R ^ 4 - 5 + 12 * z ^ 2) / 4) * S

/-- `∂_φ Ps`. -/
def Psph (R z C S : ℝ) : ℝ := s2fs R z * (-2 * S) + s2gs R z * (2 * C)

/-- `∂_R Pz`. -/
def PzR (R _z _C S : ℝ) : ℝ := (-R * (R ^ 2 - 3)) * S

/-- `∂_z Pz`. -/
def Pzz (_R z C S : ℝ) : ℝ := -2 * C + 6 * z * S

/-- `∂_φ Pz`. -/
def Pzph (R z C S : ℝ) : ℝ := -2 * z * (-2 * S) + sgz R z * (2 * C)

/-- `∂_R n_R`. -/
def nRR (R z C S : ℝ) : ℝ := 2 * eps * (Psfun R z C S + R * PsR R z C S)

/-- `∂_z n_R`. -/
def nRz (R z C S : ℝ) : ℝ := 2 * eps * R * Psz R z C S

/-- `∂_φ n_R`. -/
def nRph (R z C S : ℝ) : ℝ := 2 * eps * R * Psph R z C S

/-- `∂_R n_z`. -/
def nZR (R z C S : ℝ) : ℝ := eps * (2 * R * Pzfun R z C S + R ^ 2 * PzR R z C S)

/-- `∂_z n_z`. -/
def nZz (R z C S : ℝ) : ℝ := eps * R ^ 2 * Pzz R z C S

/-- `∂_φ n_z`. -/
def nZph (R z C S : ℝ) : ℝ := eps * R ^ 2 * Pzph R z C S

/-- `q = n_R² + R² D² + n_z² = R⁸ |B|²`. -/
def qr (R z C S : ℝ) : ℝ := nRr R z C S ^ 2 + R ^ 2 * Dfun R z C S ^ 2 + nZr R z C S ^ 2

/-- `∂_R q`. -/
def qR (R z C S : ℝ) : ℝ :=
  2 * nRr R z C S * nRR R z C S + 2 * R * Dfun R z C S ^ 2 +
    2 * R ^ 2 * Dfun R z C S * DR R z C S + 2 * nZr R z C S * nZR R z C S

/-- `∂_z q`. -/
def qz (R z C S : ℝ) : ℝ :=
  2 * nRr R z C S * nRz R z C S + 2 * R ^ 2 * Dfun R z C S * Dz R z C S +
    2 * nZr R z C S * nZz R z C S

/-- `∂_φ q`. -/
def qph (R z C S : ℝ) : ℝ :=
  2 * nRr R z C S * nRph R z C S + 2 * R ^ 2 * Dfun R z C S * Dph R z C S +
    2 * nZr R z C S * nZph R z C S

/-! ### The partial derivatives are derivatives -/

/-- Finishes a derivative identity produced by `hd_build`. -/
macro "hd_close" : tactic => `(tactic| (try simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one,
  pow_zero, mul_one, one_mul, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub]) <;> ring)

theorem hasDerivAt_D_R (R z C S : ℝ) :
    HasDerivAt (fun R => Dfun R z C S) (DR R z C S) R := by
  apply HasDerivAt.congr_deriv
  · unfold Dfun sfun sgfun; hd_build
  · unfold DR; hd_close

theorem hasDerivAt_D_z (R z C S : ℝ) :
    HasDerivAt (fun z => Dfun R z C S) (Dz R z C S) z := by
  apply HasDerivAt.congr_deriv
  · unfold Dfun sfun sgfun; hd_build
  · unfold Dz sgz; hd_close

theorem hasDerivAt_Ps_R (R z C S : ℝ) :
    HasDerivAt (fun R => Psfun R z C S) (PsR R z C S) R := by
  apply HasDerivAt.congr_deriv
  · unfold Psfun s2fs s2gs; hd_build
  · unfold PsR; hd_close

theorem hasDerivAt_Ps_z (R z C S : ℝ) :
    HasDerivAt (fun z => Psfun R z C S) (Psz R z C S) z := by
  apply HasDerivAt.congr_deriv
  · unfold Psfun s2fs s2gs; hd_build
  · unfold Psz; hd_close

theorem hasDerivAt_Pz_R (R z C S : ℝ) :
    HasDerivAt (fun R => Pzfun R z C S) (PzR R z C S) R := by
  apply HasDerivAt.congr_deriv
  · unfold Pzfun sgz; hd_build
  · unfold PzR; hd_close

theorem hasDerivAt_Pz_z (R z C S : ℝ) :
    HasDerivAt (fun z => Pzfun R z C S) (Pzz R z C S) z := by
  apply HasDerivAt.congr_deriv
  · unfold Pzfun sgz; hd_build
  · unfold Pzz; hd_close

/-- `d/dφ cos 2φ = −2 sin 2φ`. -/
theorem hasDerivAt_cos2 (φ : ℝ) :
    HasDerivAt (fun φ => cos (2 * φ)) (-2 * sin (2 * φ)) φ :=
  ((hasDerivAt_id' φ).const_mul 2).cos.congr_deriv (by ring)

/-- `d/dφ sin 2φ = 2 cos 2φ`. -/
theorem hasDerivAt_sin2 (φ : ℝ) :
    HasDerivAt (fun φ => sin (2 * φ)) (2 * cos (2 * φ)) φ :=
  ((hasDerivAt_id' φ).const_mul 2).sin.congr_deriv (by ring)

theorem hasDerivAt_D_φ (R z φ : ℝ) :
    HasDerivAt (fun φ => Dfun R z (cos (2 * φ)) (sin (2 * φ)))
      (Dph R z (cos (2 * φ)) (sin (2 * φ))) φ :=
  ((((hasDerivAt_sin2 φ).const_mul (-2 * sfun R z)).add
    ((hasDerivAt_cos2 φ).const_mul (2 * sgfun R z))).const_mul eps).const_add (R ^ 2)
    |>.congr_deriv (by simp only [Dph])

theorem hasDerivAt_Ps_φ (R z φ : ℝ) :
    HasDerivAt (fun φ => Psfun R z (cos (2 * φ)) (sin (2 * φ)))
      (Psph R z (cos (2 * φ)) (sin (2 * φ))) φ :=
  (((hasDerivAt_cos2 φ).const_mul (s2fs R z)).add
    ((hasDerivAt_sin2 φ).const_mul (s2gs R z))).congr_deriv (by simp only [Psph])

theorem hasDerivAt_Pz_φ (R z φ : ℝ) :
    HasDerivAt (fun φ => Pzfun R z (cos (2 * φ)) (sin (2 * φ)))
      (Pzph R z (cos (2 * φ)) (sin (2 * φ))) φ :=
  (((hasDerivAt_cos2 φ).const_mul (-2 * z)).add
    ((hasDerivAt_sin2 φ).const_mul (sgz R z))).congr_deriv (by simp only [Pzph])

theorem hasDerivAt_nR_R (R z C S : ℝ) :
    HasDerivAt (fun R => nRr R z C S) (nRR R z C S) R :=
  (((hasDerivAt_id' R).const_mul (2 * eps)).mul (hasDerivAt_Ps_R R z C S)).congr_deriv
    (by simp only [nRR]; ring)

theorem hasDerivAt_nR_z (R z C S : ℝ) :
    HasDerivAt (fun z => nRr R z C S) (nRz R z C S) z :=
  (hasDerivAt_Ps_z R z C S).const_mul (2 * eps * R)

theorem hasDerivAt_nR_φ (R z φ : ℝ) :
    HasDerivAt (fun φ => nRr R z (cos (2 * φ)) (sin (2 * φ)))
      (nRph R z (cos (2 * φ)) (sin (2 * φ))) φ :=
  (hasDerivAt_Ps_φ R z φ).const_mul (2 * eps * R)

theorem hasDerivAt_nZ_R (R z C S : ℝ) :
    HasDerivAt (fun R => nZr R z C S) (nZR R z C S) R :=
  ((((hasDerivAt_id' R).pow 2).const_mul eps).mul (hasDerivAt_Pz_R R z C S)).congr_deriv
    (by simp only [nZR, Pi.pow_apply] ; push_cast; ring)

theorem hasDerivAt_nZ_z (R z C S : ℝ) :
    HasDerivAt (fun z => nZr R z C S) (nZz R z C S) z :=
  (hasDerivAt_Pz_z R z C S).const_mul (eps * R ^ 2)

theorem hasDerivAt_nZ_φ (R z φ : ℝ) :
    HasDerivAt (fun φ => nZr R z (cos (2 * φ)) (sin (2 * φ)))
      (nZph R z (cos (2 * φ)) (sin (2 * φ))) φ :=
  (hasDerivAt_Pz_φ R z φ).const_mul (eps * R ^ 2)

theorem hasDerivAt_q_R (R z C S : ℝ) :
    HasDerivAt (fun R => qr R z C S) (qR R z C S) R :=
  ((((hasDerivAt_nR_R R z C S).pow 2).add
    (((hasDerivAt_id' R).pow 2).mul ((hasDerivAt_D_R R z C S).pow 2))).add
    ((hasDerivAt_nZ_R R z C S).pow 2)).congr_deriv
    (by simp only [qR, Pi.pow_apply]; push_cast; ring)

theorem hasDerivAt_q_z (R z C S : ℝ) :
    HasDerivAt (fun z => qr R z C S) (qz R z C S) z :=
  ((((hasDerivAt_nR_z R z C S).pow 2).add
    (((hasDerivAt_D_z R z C S).pow 2).const_mul (R ^ 2))).add
    ((hasDerivAt_nZ_z R z C S).pow 2)).congr_deriv (by simp only [qz] ; push_cast; ring)

theorem hasDerivAt_q_φ (R z φ : ℝ) :
    HasDerivAt (fun φ => qr R z (cos (2 * φ)) (sin (2 * φ)))
      (qph R z (cos (2 * φ)) (sin (2 * φ))) φ :=
  ((((hasDerivAt_nR_φ R z φ).pow 2).add
    (((hasDerivAt_D_φ R z φ).pow 2).const_mul (R ^ 2))).add
    ((hasDerivAt_nZ_φ R z φ).pow 2)).congr_deriv (by simp only [qph] ; push_cast; ring)

/-! ### The generated partial-derivative polynomials at real points -/

/-- `DuP` at a real point. -/
theorem eval_DuP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) DuP = (DR (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, DuP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, DR, eps]
  push_cast; ring

/-- `DzP` at a real point. -/
theorem eval_DzP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) DzP = (Dz (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, DzP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Dz, eps, sgz]
  push_cast; ring

/-- `DphP` at a real point. -/
theorem eval_DphP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) DphP = (Dph (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, DphP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Dph, eps, sfun, sgfun]
  push_cast; ring

/-- `nRuP` at a real point. -/
theorem eval_nRuP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nRuP = (nRR (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nRuP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, nRR, eps, Psfun, PsR, s2fs, s2gs]
  push_cast; ring

/-- `nRzP` at a real point. -/
theorem eval_nRzP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nRzP = (nRz (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nRzP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, nRz, eps, Psz]
  push_cast; ring

/-- `nRphP` at a real point. -/
theorem eval_nRphP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nRphP = (nRph (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nRphP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, nRph, eps, Psph, s2fs, s2gs]
  push_cast; ring

/-- `nZuP` at a real point. -/
theorem eval_nZuP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nZuP = (nZR (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nZuP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, nZR, eps, Pzfun, PzR, sgz]
  push_cast; ring

/-- `nZzP` at a real point. -/
theorem eval_nZzP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nZzP = (nZz (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nZzP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, nZz, eps, Pzz]
  push_cast; ring

/-- `nZphP` at a real point. -/
theorem eval_nZphP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nZphP = (nZph (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nZphP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, nZph, eps, Pzph, sgz]
  push_cast; ring

/-- The Taylor polynomial `P(u) = ∑_{n ≤ 6} (−1)ⁿ C(n+2, 2) uⁿ` of `(1 + u)^{−3}`. -/
def Pu (u : ℝ) : ℝ := 1 - 3 * u + 6 * u ^ 2 - 10 * u ^ 3 + 15 * u ^ 4 - 21 * u ^ 5 + 28 * u ^ 6

/-- `PuP` at a real point. -/
theorem eval_PuP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) PuP = (Pu u : ℂ) := by
  simp only [PolyExpr.eval, PuP, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Pu]
  push_cast; ring

/-- **Sanity**: `P(u) > 0` for `|u| ≤ 1/4`. -/
theorem Pu_pos {u : ℝ} (hu : |u| ≤ 1 / 4) : 0 < Pu u := by
  obtain ⟨h1, h2⟩ := abs_le.mp hu
  unfold Pu
  nlinarith [sq_nonneg u, sq_nonneg (u ^ 2), sq_nonneg (u ^ 3), mul_nonneg (sq_nonneg u)
    (sq_nonneg (u - 1 / 4)), pow_two_nonneg (u ^ 2 - u)]

/-- Polynomial expressions commute with algebra homomorphisms. -/
theorem polyExpr_eval_algHom {A B : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [NormedCommRing B]
    [NormedAlgebra ℂ B] (f : A →ₐ[ℂ] B) (x : Fin 6 → A) (e : PolyExpr ℂ (Fin 6)) :
    f (PolyExpr.eval x e) = PolyExpr.eval (fun i => f (x i)) e := by
  induction e with
  | const c => simp [PolyExpr.eval]
  | var i => rfl
  | add p q hp hq => simp [PolyExpr.eval, hp, hq]
  | sub p q hp hq => simp [PolyExpr.eval, hp, hq]
  | mul p q hp hq => simp [PolyExpr.eval, hp, hq]

/-- **`E = q P² − 1`** at a complex point (from `E_val` in `𝔸`). -/
theorem E_val_C (x : Fin 6 → ℂ) :
    PolyExpr.eval x EpP = (PolyExpr.eval x KamNewton.nRp ^ 2 + (1 + x 0) ^ 2 * PolyExpr.eval x
      KamNewton.Dp ^ 2 + PolyExpr.eval x KamNewton.nZp ^ 2) * PolyExpr.eval x PuP ^ 2 - 1 := by
  have h := congrArg (PolyExprS.evalAlg 0 0) (E_val (fun i => algebraMap ℂ FA (x i)))
  have hx : (fun i => PolyExprS.evalAlg 0 0 (algebraMap ℂ FA (x i))) = x := by
    funext i; simp
  simp only [polyExpr_eval_algHom, map_sub, map_mul, map_add, map_pow, map_one, hx] at h
  simpa [PlasmaLean.Theory.KAM.eval_algebraMap] using h

/-- `E` at a real point: `E = q P² − 1`. -/
theorem eval_EpP_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) EpP = ((qr (1 + u) z c s * Pu u ^ 2 - 1 : ℝ) : ℂ) := by
  rw [E_val_C, eval_nRp_ptC, eval_Dp_ptC, eval_nZp_ptC, eval_PuP_ptC]
  simp only [ptC, Matrix.cons_val_zero, qr, nRr, nZr]
  push_cast; ring

/-! ## `|B|²` and its gradient in cylindrical coordinates -/

/-- The squared norm of a vector given by coordinates. -/
theorem norm_sq_toLp3 (a b c : ℝ) : ‖(toLp 2 ![a, b, c] : Space)‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp

/-- Rotation invariance of the squared norm in the horizontal plane. -/
theorem rot_sq (a b c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (a * c - b * s) ^ 2 + (a * s + b * c) ^ 2 = a ^ 2 + b ^ 2 := by
  linear_combination (a ^ 2 + b ^ 2) * h

/-- **`|B|² = q / R⁸`** at `cylPt R φ z`. -/
theorem Qf_cylPt {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    Qf (cylPt R φ z) = qr R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 8 := by
  rw [Qf, field_cylPt hR, norm_sq_toLp3, rot_sq _ _ _ _ (cos_sq_add_sin_sq φ)]
  simp only [cylBR, cylBT, cylBZ, qr, nRr, nZr]
  field_simp

/-- The unit vector `e_R = (cos φ, sin φ, 0)`. -/
def eRv (φ : ℝ) : Space := toLp 2 ![cos φ, sin φ, 0]

/-- The unit vector `e_φ = (−sin φ, cos φ, 0)`. -/
def ePv (φ : ℝ) : Space := toLp 2 ![-sin φ, cos φ, 0]

/-- The unit vector `e_z = (0, 0, 1)`. -/
def eZv : Space := toLp 2 ![0, 0, 1]

/-- `∂_R cylPt = e_R`. -/
theorem hasDerivAt_cylPt_R (R φ z : ℝ) : HasDerivAt (fun R => cylPt R φ z) (eRv φ) R := by
  have h := hasDerivAt_toLp3 ((hasDerivAt_id' R).mul_const (cos φ))
    ((hasDerivAt_id' R).mul_const (sin φ)) (hasDerivAt_const R z)
  simpa [cylPt, eRv] using h

/-- `∂_φ cylPt = R e_φ`. -/
theorem hasDerivAt_cylPt_φ (R φ z : ℝ) : HasDerivAt (fun φ => cylPt R φ z) (R • ePv φ) φ := by
  have h := hasDerivAt_toLp3 ((hasDerivAt_cos φ).const_mul R) ((hasDerivAt_sin φ).const_mul R)
    (hasDerivAt_const φ z)
  refine h.congr_deriv ?_
  ext i; fin_cases i <;> simp [ePv]

/-- `∂_z cylPt = e_z`. -/
theorem hasDerivAt_cylPt_z (R φ z : ℝ) : HasDerivAt (fun z => cylPt R φ z) eZv z := by
  have h := hasDerivAt_toLp3 (hasDerivAt_const z (R * cos φ)) (hasDerivAt_const z (R * sin φ))
    (hasDerivAt_id' z)
  simpa [cylPt, eZv] using h

/-- The cylindrical point lies in the domain for `R > 0`. -/
theorem cylPt_mem_domain {R : ℝ} (hR : 0 < R) (φ z : ℝ) : cylPt R φ z ∈ domain := by
  change 0 < r2 (cylPt R φ z)
  rw [r2_cylPt]; positivity

/-- `DQ(e_R) = ∂_R (q/R⁸)`. -/
theorem fderiv_Qf_eR {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    fderiv ℝ Qf (cylPt R φ z) (eRv φ) =
      qR R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 8 -
        8 * qr R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 9 := by
  have hd := (hasFDerivAt_Qf (cylPt_mem_domain hR φ z)).differentiableAt
  have h1 := hd.hasFDerivAt.comp_hasDerivAt R (hasDerivAt_cylPt_R R φ z)
  have h2 := (hasDerivAt_q_R R z (cos (2 * φ)) (sin (2 * φ))).div (hasDerivAt_pow 8 R)
    (pow_ne_zero 8 hR.ne')
  refine h1.unique (h2.congr_of_eventuallyEq ?_ |>.congr_deriv ?_)
  · filter_upwards [lt_mem_nhds hR] with R' hR'
    exact Qf_cylPt hR' φ z
  · simp only [Nat.cast_ofNat, Nat.reduceSub]
    field_simp

/-- `DQ(R e_φ) = ∂_φ (q/R⁸)`. -/
theorem fderiv_Qf_ePh {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    fderiv ℝ Qf (cylPt R φ z) (R • ePv φ) = qph R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 8 := by
  have hd := (hasFDerivAt_Qf (cylPt_mem_domain hR φ z)).differentiableAt
  have h1 := hd.hasFDerivAt.comp_hasDerivAt φ (hasDerivAt_cylPt_φ R φ z)
  have h2 := (hasDerivAt_q_φ R z φ).div_const (R ^ 8)
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  exact Filter.Eventually.of_forall fun φ' => Qf_cylPt hR φ' z

/-- `DQ(e_z) = ∂_z (q/R⁸)`. -/
theorem fderiv_Qf_eZ {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    fderiv ℝ Qf (cylPt R φ z) eZv = qz R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 8 := by
  have hd := (hasFDerivAt_Qf (cylPt_mem_domain hR φ z)).differentiableAt
  have h1 := hd.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_cylPt_z R φ z)
  have h2 := (hasDerivAt_q_z R z (cos (2 * φ)) (sin (2 * φ))).div_const (R ^ 8)
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  exact Filter.Eventually.of_forall fun z' => Qf_cylPt hR φ z'

/-- Inner product with a vector given by coordinates. -/
theorem inner_toLp3 (g : Space) (a b c : ℝ) :
    ⟪g, (toLp 2 ![a, b, c] : Space)⟫ = g 0 * a + g 1 * b + g 2 * c := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- `⟪∇Q, v⟫ = DQ(v)`. -/
theorem inner_gradient_Qf (x v : Space) : ⟪gradient Qf x, v⟫ = fderiv ℝ Qf x v := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- `∂_R (q/R⁸)`: the `e_R`-component of `∇|B|²`. -/
def GRc (R z C S : ℝ) : ℝ := qR R z C S / R ^ 8 - 8 * qr R z C S / R ^ 9

/-- The `e_φ`-component of `∇|B|²`: `∂_φ (q/R⁸) / R`. -/
def GPc (R z C S : ℝ) : ℝ := qph R z C S / R ^ 9

/-- The `e_z`-component of `∇|B|²`: `∂_z (q/R⁸)`. -/
def GZc (R z C S : ℝ) : ℝ := qz R z C S / R ^ 8

/-- **The gradient of `|B|²` in cylindrical coordinates**:
`∇Q = G_R e_R + G_φ e_φ + G_z e_z` at `cylPt R φ z`. -/
theorem gradient_Qf_cylPt {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    gradient Qf (cylPt R φ z) = toLp 2
      ![GRc R z (cos (2 * φ)) (sin (2 * φ)) * cos φ - GPc R z (cos (2 * φ)) (sin (2 * φ)) * sin φ,
        GRc R z (cos (2 * φ)) (sin (2 * φ)) * sin φ + GPc R z (cos (2 * φ)) (sin (2 * φ)) * cos φ,
        GZc R z (cos (2 * φ)) (sin (2 * φ))] := by
  have h1 := fderiv_Qf_eR hR φ z
  have h2 := fderiv_Qf_ePh hR φ z
  have h3 := fderiv_Qf_eZ hR φ z
  rw [← inner_gradient_Qf] at h1 h2 h3
  have e2 : R • ePv φ = toLp 2 ![-(R * sin φ), R * cos φ, 0] := by
    ext i; fin_cases i <;> simp [ePv]
  rw [eRv, inner_toLp3] at h1
  rw [e2, inner_toLp3] at h2
  rw [eZv, inner_toLp3] at h3
  set g := gradient Qf (cylPt R φ z)
  have hcs := cos_sq_add_sin_sq φ
  have hR0 : R ≠ 0 := hR.ne'
  have h2' : -sin φ * g 0 + cos φ * g 1 = qph R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 9 := by
    rw [pow_succ, ← div_div, ← h2]; field_simp; ring
  simp only [GRc, GPc, GZc]
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linear_combination cos φ * h1 - sin φ * h2' + (-(g 0)) * hcs
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    linear_combination sin φ * h1 + cos φ * h2' + (-(g 1)) * hcs
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    linear_combination h3

/-! ## The guiding-centre field in cylindrical coordinates -/

/-- `W = q^{−1/2}`. -/
def Wr (R z C S : ℝ) : ℝ := (√(qr R z C S))⁻¹

/-- `κ_D = R² (R n_z q_R − 8 n_z q − R n_R q_z)`. -/
def KDr (R z C S : ℝ) : ℝ :=
  R ^ 2 * (R * nZr R z C S * qR R z C S - 8 * nZr R z C S * qr R z C S -
    R * nRr R z C S * qz R z C S)

/-- `κ_R = R⁵ D q_z − R³ n_z q_φ`. -/
def KRr (R z C S : ℝ) : ℝ :=
  R ^ 5 * Dfun R z C S * qz R z C S - R ^ 3 * nZr R z C S * qph R z C S

/-- `κ_z = R³ n_R q_φ − R⁵ D q_R + 8 R⁴ D q`. -/
def KZr (R z C S : ℝ) : ℝ :=
  R ^ 3 * nRr R z C S * qph R z C S - R ^ 5 * Dfun R z C S * qR R z C S +
    8 * R ^ 4 * Dfun R z C S * qr R z C S

/-- **`D̃ = D + (ρ/2) W³ κ_D = R³ B̃_φ`** (real form). -/
def gcDr (ρ R z C S : ℝ) : ℝ := Dfun R z C S + ρ / 2 * Wr R z C S ^ 3 * KDr R z C S

/-- **`ñ_R = n_R + (ρ/2) W³ κ_R = R⁴ B̃^R`** (real form). -/
def gcNRr (ρ R z C S : ℝ) : ℝ := nRr R z C S + ρ / 2 * Wr R z C S ^ 3 * KRr R z C S

/-- **`ñ_z = n_z + (ρ/2) W³ κ_z = R⁴ B̃^z`** (real form). -/
def gcNZr (ρ R z C S : ℝ) : ℝ := nZr R z C S + ρ / 2 * Wr R z C S ^ 3 * KZr R z C S

/-- **Sanity**: for `ρ = 0` the guiding-centre flow form is that of `field (1/4)`. -/
theorem gcDr_zero (R z C S : ℝ) : gcDr 0 R z C S = Dfun R z C S ∧
    gcNRr 0 R z C S = nRr R z C S ∧ gcNZr 0 R z C S = nZr R z C S := by
  simp [gcDr, gcNRr, gcNZr]

/-- `a^{−3/2} = (a √a)⁻¹` for `a > 0`. -/
theorem rpow_neg_three_halves {a : ℝ} (ha : 0 < a) : a ^ (-(3 : ℝ) / 2) = (a * √a)⁻¹ := by
  rw [show -(3 : ℝ) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg ha.le,
    Real.rpow_add ha, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- `(q/R⁸)^{−3/2} = R¹² W³`. -/
theorem Qf_rpow_cyl {R q : ℝ} (hR : 0 < R) (hq : 0 < q) :
    (q / R ^ 8) ^ (-(3 : ℝ) / 2) = R ^ 12 * ((√q)⁻¹) ^ 3 := by
  have hR8 : 0 < R ^ 8 := by positivity
  rw [rpow_neg_three_halves (div_pos hq hR8), Real.sqrt_div' _ hR8.le,
    show R ^ 8 = (R ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hs : 0 < √q := Real.sqrt_pos.2 hq
  have hsq : q * √q = √q ^ 3 := by rw [pow_succ, Real.sq_sqrt hq.le]
  rw [show q / (R ^ 4) ^ 2 * (√q / R ^ 4) = √q ^ 3 / R ^ 12 by rw [← hsq]; field_simp]
  field_simp

/-- The cross product of vectors given by coordinates. -/
theorem cross_toLp3 (a b c d e f : ℝ) :
    cross (toLp 2 ![a, b, c]) (toLp 2 ![d, e, f]) =
      (toLp 2 ![b * f - c * e, c * d - a * f, a * e - b * d] : Space) := by
  simp only [cross, cross_apply]
  ext i; fin_cases i <;> simp

/-- **The guiding-centre field in cylindrical coordinates** (real form): for `R > 0` and `q > 0`,
`gcField ρ (cylPt R φ z) = (ñ_R/R⁴) e_R + (D̃/R³) e_φ + (ñ_z/R⁴) e_z`. -/
theorem gcField_cylPt_real (ρ : ℝ) {R : ℝ} (hR : 0 < R) (φ z : ℝ)
    (hq : 0 < qr R z (cos (2 * φ)) (sin (2 * φ))) :
    gcField ρ (cylPt R φ z) = toLp 2
      ![gcNRr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 * cos φ -
          R * (gcDr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4) * sin φ,
        gcNRr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 * sin φ +
          R * (gcDr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4) * cos φ,
        gcNZr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4] := by
  have hx := cylPt_mem_domain hR φ z
  have hQ : 0 < Qf (cylPt R φ z) := by rw [Qf_cylPt hR]; positivity
  have hB : field (1 / 4) (cylPt R φ z) ≠ 0 := by
    intro h; rw [Qf, h, norm_zero] at hQ; norm_num at hQ
  rw [gcField_eq ρ hx hB, gradient_Qf_cylPt hR, Qf_cylPt hR, Qf_rpow_cyl hR hq, field_cylPt hR,
    cross_toLp3]
  have hR0 : R ≠ 0 := hR.ne'
  simp only [gcNRr, gcDr, gcNZr, Wr, KRr, KDr, KZr, GRc, GPc, GZc, cylBR, cylBT, cylBZ, nRr, nZr]
  have hcs := cos_sq_add_sin_sq φ
  generalize (√(qr R z (cos (2 * φ)) (sin (2 * φ))))⁻¹ = W
  generalize Psfun R z (cos (2 * φ)) (sin (2 * φ)) = Ps
  generalize Pzfun R z (cos (2 * φ)) (sin (2 * φ)) = Pz
  generalize Dfun R z (cos (2 * φ)) (sin (2 * φ)) = D
  generalize qr R z (cos (2 * φ)) (sin (2 * φ)) = q
  generalize qR R z (cos (2 * φ)) (sin (2 * φ)) = qR'
  generalize qz R z (cos (2 * φ)) (sin (2 * φ)) = qz'
  generalize qph R z (cos (2 * φ)) (sin (2 * φ)) = qph'
  generalize cos φ = c at hcs ⊢
  generalize sin φ = s at hcs ⊢
  ext i; fin_cases i
  · simp
    field_simp
    ring
  · simp
    field_simp
    ring
  · simp
    field_simp
    linear_combination (2 * eps * R ^ 2 * ρ * W ^ 3 * Ps * qph' + 8 * R ^ 2 * ρ * W ^ 3 * D * q -
      R ^ 3 * ρ * W ^ 3 * D * qR') * hcs

/-! ## The flow-form expressions at real points -/

/-- `q ≥ 0`. -/
theorem qr_nonneg (R z C S : ℝ) : 0 ≤ qr R z C S := by unfold qr; positivity

/-- **The node at a real point**: where the node is valid and `|u| ≤ 1/4`, `q > 0` and
`W = P (1 + E)^{−1/2}` evaluates to `q^{−1/2}`. -/
theorem eval_eV_ptC {a : Fin 6 → ℝ} {u z c s : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hu : |u| ≤ 1 / 4) :
    0 < qr (1 + u) z c s ∧
      PolyExprS.eval (ptC u z c s 0 0) eV = ((Wr (1 + u) z c s / Pu u : ℝ) : ℂ) := by
  have hV : PolyExprS.Valid a eV := ⟨PolyExprS.valid_ofPoly _ _, by
    rw [PolyExprS.maj_ofPoly]; exact hE⟩
  have hr : (AlgHom.id ℂ ℂ) (PolyExprS.eval (ptC u z c s 0 0) (PolyExprS.ofPoly EpP)) =
      ((qr (1 + u) z c s * Pu u ^ 2 - 1 : ℝ) : ℂ) := by
    rw [AlgHom.id_apply, PolyExprS.eval_ofPoly, eval_EpP_ptC]
  obtain ⟨hpos, hval⟩ := PolyExprS.eval_isqrt_point (AlgHom.id ℂ ℂ) hx hV hr
  rw [AlgHom.id_apply] at hval
  have e : ∀ a b : ℝ, Sub.sub a b = a - b := fun _ _ => rfl
  simp only [e, add_sub_cancel] at hpos hval
  have hP := Pu_pos hu
  have hq0 := qr_nonneg (1 + u) z c s
  have hq : 0 < qr (1 + u) z c s := by
    rcases hq0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; norm_num at hpos
  refine ⟨hq, ?_⟩
  rw [show eV = PolyExprS.isqrt 1 (PolyExprS.ofPoly EpP) from rfl, hval,
    Real.sqrt_mul hq0, Real.sqrt_sq hP.le, Wr]
  push_cast
  field_simp
  rfl

/-- Unfolds the flow-form expressions at a real point. -/
theorem eval_parts_ptC (u z c s : ℝ) :
    PolyExprS.eval (ptC u z c s 0 0) eR = ((1 + u : ℝ) : ℂ) ∧
    PolyExprS.eval (ptC u z c s 0 0) eq = (qr (1 + u) z c s : ℂ) ∧
    PolyExprS.eval (ptC u z c s 0 0) eqR = (qR (1 + u) z c s : ℂ) ∧
    PolyExprS.eval (ptC u z c s 0 0) eqz = (qz (1 + u) z c s : ℂ) ∧
    PolyExprS.eval (ptC u z c s 0 0) eqph = (qph (1 + u) z c s : ℂ) := by
  have h0 : PolyExprS.eval (ptC u z c s 0 0) eR = ((1 + u : ℝ) : ℂ) := by
    simp [eR, PolyExprS.eval, ptC]
  refine ⟨h0, ?_, ?_, ?_, ?_⟩
  · simp only [eq, PolyExprS.eval, PolyExprS.eval_ofPoly, h0, eval_nRp_ptC, eval_Dp_ptC,
      eval_nZp_ptC, qr, nRr, nZr]
    push_cast; ring
  · simp only [eqR, PolyExprS.eval, PolyExprS.eval_ofPoly, h0, eval_nRp_ptC, eval_Dp_ptC,
      eval_nZp_ptC, eval_nRuP_ptC, eval_DuP_ptC, eval_nZuP_ptC, qR, nRr, nZr,
      Algebra.algebraMap_self, RingHom.id_apply]
    push_cast; ring
  · simp only [eqz, PolyExprS.eval, PolyExprS.eval_ofPoly, h0, eval_nRp_ptC, eval_Dp_ptC,
      eval_nZp_ptC, eval_nRzP_ptC, eval_DzP_ptC, eval_nZzP_ptC, qz, nRr, nZr,
      Algebra.algebraMap_self, RingHom.id_apply]
    push_cast; ring
  · simp only [eqph, PolyExprS.eval, PolyExprS.eval_ofPoly, h0, eval_nRp_ptC, eval_Dp_ptC,
      eval_nZp_ptC, eval_nRphP_ptC, eval_DphP_ptC, eval_nZphP_ptC, qph, nRr, nZr,
      Algebra.algebraMap_self, RingHom.id_apply]
    push_cast; ring

/-- `W = P (1 + E)^{−1/2}` evaluates to `q^{−1/2}` at a valid real point. -/
theorem eval_eW_ptC {a : Fin 6 → ℝ} {u z c s : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) eW = (Wr (1 + u) z c s : ℂ) := by
  obtain ⟨-, hV⟩ := eval_eV_ptC hx hE hu
  have hP : (Pu u : ℂ) ≠ 0 := by exact_mod_cast (Pu_pos hu).ne'
  simp only [eW, PolyExprS.eval, PolyExprS.eval_ofPoly, eval_PuP_ptC, hV]
  push_cast
  field_simp

/-- **`D̃` at a valid real point**: the flow-form expression `gcD ρ` evaluates to `D̃`
(`gcDr`). -/
theorem eval_gcD_ptC (ρ : ℝ) {a : Fin 6 → ℝ} {u z c s : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) (gcD ρ) = (gcDr ρ (1 + u) z c s : ℂ) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := eval_parts_ptC u z c s
  simp only [gcD, eW3, eKD, PolyExprS.eval, PolyExprS.eval_ofPoly, eval_eW_ptC hx hE hu, h0, h1,
    h2, h3, eval_Dp_ptC, eval_nRp_ptC, eval_nZp_ptC, Algebra.algebraMap_self, RingHom.id_apply,
    gcDr, KDr, nRr, nZr]
  push_cast; ring

/-- **`ñ_R` at a valid real point.** -/
theorem eval_gcNR_ptC (ρ : ℝ) {a : Fin 6 → ℝ} {u z c s : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) (gcNR ρ) = (gcNRr ρ (1 + u) z c s : ℂ) := by
  obtain ⟨h0, -, -, h3, h4⟩ := eval_parts_ptC u z c s
  simp only [gcNR, eW3, eKR, PolyExprS.eval, PolyExprS.eval_ofPoly, eval_eW_ptC hx hE hu, h0,
    h3, h4, eval_Dp_ptC, eval_nRp_ptC, eval_nZp_ptC, Algebra.algebraMap_self, RingHom.id_apply,
    gcNRr, KRr, nRr, nZr]
  push_cast; ring

/-- **`ñ_z` at a valid real point.** -/
theorem eval_gcNZ_ptC (ρ : ℝ) {a : Fin 6 → ℝ} {u z c s : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) (gcNZ ρ) = (gcNZr ρ (1 + u) z c s : ℂ) := by
  obtain ⟨h0, h1, h2, -, h4⟩ := eval_parts_ptC u z c s
  simp only [gcNZ, eW3, eKZ, PolyExprS.eval, PolyExprS.eval_ofPoly, eval_eW_ptC hx hE hu, h0,
    h1, h2, h4, eval_Dp_ptC, eval_nRp_ptC, eval_nZp_ptC, Algebra.algebraMap_self,
    RingHom.id_apply, gcNZr, KZr, nRr, nZr]
  push_cast; ring

/-- **The guiding-centre field in cylindrical coordinates, in terms of the flow-form expressions
of the KAM theorem** (`gcField_cylPt`): at a point `cylPt R φ z` with `|R − 1| ≤ 1/4` whose
flow-form variables `(R − 1, z, cos 2φ, sin 2φ)` make the node `(1 + E)^{−1/2}` valid,

`gcField ρ = (Re ñ_R/R⁴) e_R + (Re D̃/R³) e_φ + (Re ñ_z/R⁴) e_z`,

where `D̃, ñ_R, ñ_z` are the values of `gcD ρ, gcNR ρ, gcNZ ρ` (the expressions of
`gcFlow ρ`). -/
theorem gcField_cylPt (ρ : ℝ) {R φ z : ℝ} {a : Fin 6 → ℝ}
    (hx : ∀ i, ‖ptC (R - 1) z (cos (2 * φ)) (sin (2 * φ)) 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hR : |R - 1| ≤ 1 / 4) :
    gcField ρ (cylPt R φ z) = toLp 2
      ![(PolyExprS.eval (ptC (R - 1) z (cos (2 * φ)) (sin (2 * φ)) 0 0) (gcNR ρ)).re / R ^ 4 *
            cos φ - R * ((PolyExprS.eval (ptC (R - 1) z (cos (2 * φ)) (sin (2 * φ)) 0 0)
            (gcD ρ)).re / R ^ 4) * sin φ,
        (PolyExprS.eval (ptC (R - 1) z (cos (2 * φ)) (sin (2 * φ)) 0 0) (gcNR ρ)).re / R ^ 4 *
            sin φ + R * ((PolyExprS.eval (ptC (R - 1) z (cos (2 * φ)) (sin (2 * φ)) 0 0)
            (gcD ρ)).re / R ^ 4) * cos φ,
        (PolyExprS.eval (ptC (R - 1) z (cos (2 * φ)) (sin (2 * φ)) 0 0) (gcNZ ρ)).re / R ^ 4] := by
  have hR0 : 0 < R := by linarith [(abs_le.mp hR).1]
  have e1 : 1 + (R - 1) = R := by ring
  obtain ⟨hq, -⟩ := eval_eV_ptC hx hE hR
  rw [e1] at hq
  rw [eval_gcD_ptC ρ hx hE hR, eval_gcNR_ptC ρ hx hE hR, eval_gcNZ_ptC ρ hx hE hR, e1,
    Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  exact gcField_cylPt_real ρ hR0 φ z hq

end PlasmaLean.Design.RationalStellaratorGC
