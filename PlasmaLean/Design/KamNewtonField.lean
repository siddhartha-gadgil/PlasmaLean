/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowField

/-!
# The field of the rational stellarator in the strip algebra (KAM route, K3d)

The flow form of the field-line equations of `field (1/4)` (`Design/KamTorusA`) for a torus
`K = (R, z) = (1 + u, z)` is `D(K, φ)·𝓛K = n(K, φ)` with `𝓛 = ∂_φ + ι∂_θ` and polynomials
`D, n_R, n_z` in `u, z, c = cos 2φ, s = sin 2φ`. This file sets these objects up in the strip
algebra `𝔸` (`Theory/KAM/StripAlgebra`) and packages them as the instance `field14 : FlowField`
of the abstract interface of the KAM step (`Design/KamFlowField`):

* the polynomials in **monomial form in `u = R − 1`** (so that the majorants see the
  cancellations near the magnetic axis): `Dp` (`D = R²(1 + ε∂_φh)`), `nRp = 2εR·Ps`,
  `nZp = εR²·Pz`, the residuals `resRp = D w_R − n_R`, `resZp = D w_z − n_z`, the flux primitive
  numerators `Pap`, `Pbp`, and the torsion numerator `Pp`;
* the **polynomial identities** on which the Newton step rests, proved pointwise in `ℂ` and
  transported to `𝔸` by uniqueness of Fourier coefficients (`ext_eval`):
  - `divFree`: `R ∂_φD − 3 n_R + R ∂_u n_R + R ∂_z n_z = 0` (the flux form `(D/R³) dR∧dz` is
    invariant: `div B = 0`);
  - `flux_a`, `flux_b`, `flux_c`: the 1-form `α = a dR + b dz`, `a = P_a/R`, `b = P_b/R²`, is a
    primitive of the flux 2-form `β = w (dR − X_R dφ) ∧ (dz − X_z dφ)`, `w = D/R³`;
  - `torsion_poly`: `P = (n_R D − D ∇n_R·V₀ + n_R ∇D·V₀) z − (n_z D − D ∇n_z·V₀ + n_z ∇D·V₀) u`;
* the evaluations `Dof`, `Pof`, `resR`, `resZ` at a torus, which agree definitionally with the
  generic ones of `field14` (`field14_Dof`, `field14_Pof`, `field14_resR`, `field14_resZ`).

The field-independent operators (`dTh`, `dPh`, `Lt`, `cS`, `sS`, `pd`, `phiD`, `xK`, `xB`, `W0of`)
are in `Design/KamFlowField`.

**Sanity.** `realConsts_all` (rational coefficients), `field14_resR` (the generic residual of the
instance is the residual of `field (1/4)`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PolyExpr Complex WEll1Z2

/-! ## The polynomials (monomial form in `u = R − 1, z, c, s`; variables `w_R, w_z` are `4, 5`) -/

/-- `D = R²(1 + ε∂_φh)` in monomial form in `u = R − 1, z, c = cos 2φ, s = sin 2φ`. -/
def Dp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/8) [(0, 4), (1, 1), (2, 1)],
    monoE (-1/8) [(0, 4), (3, 1)],
    monoE (-1/2) [(0, 3), (1, 1), (2, 1)],
    monoE (-1/2) [(0, 3), (3, 1)],
    monoE (-1/2) [(0, 2), (3, 1)],
    monoE (1) [(0, 2)],
    monoE (1) [(0, 1), (1, 1), (2, 1)],
    monoE (2) [(0, 1)],
    monoE (1/2) [(1, 3), (2, 1)],
    monoE (1/2) [(1, 2), (3, 1)],
    monoE (1) []]

/-- The numerator `2εR Ps` of `X_R`, monomial form in `u, z, c, s`. -/
def nRp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/8) [(0, 5), (1, 1), (3, 1)],
    monoE (1/8) [(0, 5), (2, 1)],
    monoE (-5/8) [(0, 4), (1, 1), (3, 1)],
    monoE (5/8) [(0, 4), (2, 1)],
    monoE (-5/4) [(0, 3), (1, 1), (3, 1)],
    monoE (5/4) [(0, 3), (2, 1)],
    monoE (-5/4) [(0, 2), (1, 1), (3, 1)],
    monoE (5/4) [(0, 2), (2, 1)],
    monoE (-1/2) [(0, 1), (1, 3), (3, 1)],
    monoE (1/2) [(0, 1), (1, 2), (2, 1)],
    monoE (1/2) [(0, 1), (2, 1)],
    monoE (-1/2) [(1, 3), (3, 1)],
    monoE (1/2) [(1, 2), (2, 1)],
    monoE (1/2) [(1, 1), (3, 1)]]

/-- The numerator `εR² Pz` of `X_z`, monomial form in `u, z, c, s`. -/
def nZp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/16) [(0, 6), (3, 1)],
    monoE (-3/8) [(0, 5), (3, 1)],
    monoE (-9/16) [(0, 4), (3, 1)],
    monoE (1/4) [(0, 3), (3, 1)],
    monoE (3/4) [(0, 2), (1, 2), (3, 1)],
    monoE (-1/2) [(0, 2), (1, 1), (2, 1)],
    monoE (1) [(0, 2), (3, 1)],
    monoE (3/2) [(0, 1), (1, 2), (3, 1)],
    monoE (-1) [(0, 1), (1, 1), (2, 1)],
    monoE (1/2) [(0, 1), (3, 1)],
    monoE (3/4) [(1, 2), (3, 1)],
    monoE (-1/2) [(1, 1), (2, 1)]]

/-- Numerator `R·a` of the `dR`-coefficient `a` of the flux primitive. -/
def Pap : PolyExpr ℂ (Fin 6) := sumE [
    monoE (1/32) [(0, 4), (2, 1)],
    monoE (1/8) [(0, 3), (2, 1)],
    monoE (-1/4) [(0, 1), (2, 1)],
    monoE (-3/8) [(1, 2), (2, 1)],
    monoE (-1/4) [(1, 1), (3, 1)],
    monoE (-1) [(1, 1)]]

/-- Numerator `R²·b` of the `dz`-coefficient `b` of the flux primitive. -/
def Pbp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/16) [(0, 4), (1, 1), (2, 1)],
    monoE (-1/16) [(0, 4), (3, 1)],
    monoE (-1/4) [(0, 3), (1, 1), (2, 1)],
    monoE (-1/4) [(0, 3), (3, 1)],
    monoE (-3/8) [(0, 2), (1, 1), (2, 1)],
    monoE (-3/8) [(0, 2), (3, 1)],
    monoE (-1/4) [(0, 1), (1, 1), (2, 1)],
    monoE (-1/4) [(0, 1), (3, 1)],
    monoE (-1/4) [(1, 3), (2, 1)],
    monoE (-1/4) [(1, 2), (3, 1)],
    monoE (1/4) [(1, 1), (2, 1)]]

/-- The torsion numerator `P = (D² (X − DX·V₀)) × V₀` (`V₀ = (u, z)`), monomial form; the torsion
density is `T₀ = R³ P / (D³ W₀²)`. -/
def Pp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (1/128) [(0, 11), (3, 2)],
    monoE (-1/64) [(0, 10), (1, 1), (2, 1), (3, 1)],
    monoE (1/16) [(0, 10), (3, 2)],
    monoE (-1/64) [(0, 9), (1, 2), (2, 2)],
    monoE (-1/64) [(0, 9), (1, 2), (3, 2)],
    monoE (-9/64) [(0, 9), (1, 1), (2, 1), (3, 1)],
    monoE (27/128) [(0, 9), (3, 2)],
    monoE (-3/16) [(0, 9), (3, 1)],
    monoE (1/64) [(0, 8), (1, 3), (2, 1), (3, 1)],
    monoE (-5/32) [(0, 8), (1, 2), (2, 2)],
    monoE (-1/8) [(0, 8), (1, 2), (3, 2)],
    monoE (-25/64) [(0, 8), (1, 1), (2, 1), (3, 1)],
    monoE (7/16) [(0, 8), (3, 2)],
    monoE (-5/4) [(0, 8), (3, 1)],
    monoE (7/16) [(0, 7), (1, 3), (2, 1), (3, 1)],
    monoE (-31/32) [(0, 7), (1, 2), (2, 2)],
    monoE (-11/32) [(0, 7), (1, 2), (3, 2)],
    monoE (3/8) [(0, 7), (1, 2), (3, 1)],
    monoE (-5/16) [(0, 7), (1, 1), (2, 1), (3, 1)],
    monoE (-1/4) [(0, 7), (1, 1), (2, 1)],
    monoE (25/32) [(0, 7), (3, 2)],
    monoE (-25/8) [(0, 7), (3, 1)],
    monoE (71/32) [(0, 6), (1, 3), (2, 1), (3, 1)],
    monoE (-25/8) [(0, 6), (1, 2), (2, 2)],
    monoE (-5/16) [(0, 6), (1, 2), (3, 2)],
    monoE (9/4) [(0, 6), (1, 2), (3, 1)],
    monoE (-5/32) [(0, 6), (1, 1), (2, 1), (3, 1)],
    monoE (-11/8) [(0, 6), (1, 1), (2, 1)],
    monoE (5/4) [(0, 6), (3, 2)],
    monoE (-15/4) [(0, 6), (3, 1)],
    monoE (1/4) [(0, 5), (1, 5), (2, 1), (3, 1)],
    monoE (-1/4) [(0, 5), (1, 4), (2, 2)],
    monoE (1/4) [(0, 5), (1, 4), (3, 2)],
    monoE (33/8) [(0, 5), (1, 3), (2, 1), (3, 1)],
    monoE (-37/8) [(0, 5), (1, 2), (2, 2)],
    monoE (3/8) [(0, 5), (1, 2), (3, 2)],
    monoE (51/8) [(0, 5), (1, 2), (3, 1)],
    monoE (-7/4) [(0, 5), (1, 1), (2, 1), (3, 1)],
    monoE (-3) [(0, 5), (1, 1), (2, 1)],
    monoE (5/4) [(0, 5), (3, 2)],
    monoE (-35/16) [(0, 5), (3, 1)],
    monoE (3/4) [(0, 4), (1, 5), (2, 1), (3, 1)],
    monoE (-3/4) [(0, 4), (1, 4), (2, 2)],
    monoE (3/4) [(0, 4), (1, 4), (3, 2)],
    monoE (31/16) [(0, 4), (1, 3), (2, 1), (3, 1)],
    monoE (-2) [(0, 4), (1, 2), (2, 2)],
    monoE (1/2) [(0, 4), (1, 2), (3, 2)],
    monoE (21/2) [(0, 4), (1, 2), (3, 1)],
    monoE (-29/8) [(0, 4), (1, 1), (2, 1), (3, 1)],
    monoE (-25/8) [(0, 4), (1, 1), (2, 1)],
    monoE (1/2) [(0, 4), (3, 2)],
    monoE (-1/2) [(0, 4), (3, 1)],
    monoE (1/2) [(0, 3), (1, 5), (2, 1), (3, 1)],
    monoE (1/8) [(0, 3), (1, 4), (2, 2)],
    monoE (1) [(0, 3), (1, 4), (3, 2)],
    monoE (1/2) [(0, 3), (1, 4), (3, 1)],
    monoE (-5/2) [(0, 3), (1, 3), (2, 1), (3, 1)],
    monoE (9/4) [(0, 3), (1, 2), (2, 2)],
    monoE (-7/8) [(0, 3), (1, 2), (3, 2)],
    monoE (43/4) [(0, 3), (1, 2), (3, 1)],
    monoE (-2) [(0, 3), (1, 1), (2, 1), (3, 1)],
    monoE (-3/2) [(0, 3), (1, 1), (2, 1)],
    monoE (-7/8) [(0, 2), (1, 5), (2, 1), (3, 1)],
    monoE (9/4) [(0, 2), (1, 4), (2, 2)],
    monoE (2) [(0, 2), (1, 4), (3, 1)],
    monoE (-5/8) [(0, 2), (1, 3), (2, 1), (3, 1)],
    monoE (-1/2) [(0, 2), (1, 3), (2, 1)],
    monoE (2) [(0, 2), (1, 2), (2, 2)],
    monoE (-1) [(0, 2), (1, 2), (3, 2)],
    monoE (13/2) [(0, 2), (1, 2), (3, 1)],
    monoE (-1/4) [(0, 2), (1, 1), (2, 1)],
    monoE (1/4) [(0, 1), (1, 6), (2, 2)],
    monoE (1/4) [(0, 1), (1, 6), (3, 2)],
    monoE (-3/4) [(0, 1), (1, 5), (2, 1), (3, 1)],
    monoE (2) [(0, 1), (1, 4), (2, 2)],
    monoE (-3/8) [(0, 1), (1, 4), (3, 2)],
    monoE (5/2) [(0, 1), (1, 4), (3, 1)],
    monoE (2) [(0, 1), (1, 3), (2, 1), (3, 1)],
    monoE (-1) [(0, 1), (1, 3), (2, 1)],
    monoE (7/4) [(0, 1), (1, 2), (3, 1)],
    monoE (-1/4) [(1, 7), (2, 1), (3, 1)],
    monoE (1/2) [(1, 6), (2, 2)],
    monoE (1) [(1, 5), (2, 1), (3, 1)],
    monoE (1/2) [(1, 4), (3, 2)],
    monoE (1) [(1, 4), (3, 1)],
    monoE (-1/2) [(1, 3), (2, 1)]]

/-- The flow-form residual `D w_R − n_R` (variables `u, z, c, s, w_R, w_z`). -/
def resRp : PolyExpr ℂ (Fin 6) := sub (mul Dp (var 4)) nRp

/-- The flow-form residual `D w_z − n_z`. -/
def resZp : PolyExpr ℂ (Fin 6) := sub (mul Dp (var 5)) nZp

/-- `D` does not involve the velocities. -/
theorem noW_Dp : NoW Dp := by simp [NoW, Dp, sumE, monoE, npow]
/-- `n_R` does not involve the velocities. -/
theorem noW_nRp : NoW nRp := by simp [NoW, nRp, sumE, monoE, npow]
/-- `n_z` does not involve the velocities. -/
theorem noW_nZp : NoW nZp := by simp [NoW, nZp, sumE, monoE, npow]
/-- `P_a` does not involve the velocities. -/
theorem noW_Pap : NoW Pap := by simp [NoW, Pap, sumE, monoE, npow]
/-- `P_b` does not involve the velocities. -/
theorem noW_Pbp : NoW Pbp := by simp [NoW, Pbp, sumE, monoE, npow]
/-- `P` does not involve the velocities. -/
theorem noW_Pp : NoW Pp := by simp [NoW, Pp, sumE, monoE, npow]

/-! ## The polynomial identities -/

/-- Unfolding set for the concrete polynomials. -/
macro "poly_simp" : tactic =>
  `(tactic| simp only [phiD, pd, PolyExpr.deriv, PolyExpr.eval, Dp, nRp, nZp, Pap, Pbp, Pp,
    sumE, monoE, npow, Pi.single_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Fin.isValue, eval_npow])

/-- **Divergence-free identity** in `𝔸`. -/
theorem divFree (x : Fin 6 → FA) :
    (1 + x 0) * phiD x Dp - 3 * PolyExpr.eval x nRp + (1 + x 0) * pd x 0 nRp +
      (1 + x 0) * pd x 1 nZp = 0 := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **Flux primitive identity** (a) in `𝔸`. -/
theorem flux_a (x : Fin 6 → FA) :
    (1 + x 0) * pd x 0 Pbp - 2 * PolyExpr.eval x Pbp - (1 + x 0) ^ 2 * pd x 1 Pap =
      PolyExpr.eval x Dp := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **Flux primitive identity** (b) in `𝔸`. -/
theorem flux_b (x : Fin 6 → FA) :
    (1 + x 0) ^ 2 * phiD x Pap = PolyExpr.eval x nZp := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **Flux primitive identity** (c) in `𝔸`. -/
theorem flux_c (x : Fin 6 → FA) :
    (1 + x 0) * phiD x Pbp = -PolyExpr.eval x nRp := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **The torsion numerator** in `𝔸`. -/
theorem torsion_poly (x : Fin 6 → FA) :
    PolyExpr.eval x Pp =
      (PolyExpr.eval x nRp * PolyExpr.eval x Dp -
          PolyExpr.eval x Dp * (pd x 0 nRp * x 0 + pd x 1 nRp * x 1) +
          PolyExpr.eval x nRp * (pd x 0 Dp * x 0 + pd x 1 Dp * x 1)) * x 1 -
        (PolyExpr.eval x nZp * PolyExpr.eval x Dp -
          PolyExpr.eval x Dp * (pd x 0 nZp * x 0 + pd x 1 nZp * x 1) +
          PolyExpr.eval x nZp * (pd x 0 Dp * x 0 + pd x 1 Dp * x 1)) * x 0 := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring


/-! ## The torus point and the derived quantities -/

/-- `D(K)`. -/
def Dof (u z : FA) : FA := PolyExpr.eval (xB u z) Dp

/-- The torsion numerator `P(K)`. -/
def Pof (u z : FA) : FA := PolyExpr.eval (xB u z) Pp

/-- The `R`-residual `D 𝓛R − n_R`. -/
def resR (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) resRp

/-- The `z`-residual `D 𝓛z − n_z`. -/
def resZ (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) resZp

/-- `resR = D 𝓛u − n_R`. -/
theorem resR_eq (ι : ℝ) (u z : FA) :
    resR ι u z = Dof u z * Lt ι u - PolyExpr.eval (xB u z) nRp := by
  rw [resR, resRp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z noW_Dp, eval_xK_xB ι u z noW_nRp]
  rfl

/-- `resZ = D 𝓛z − n_z`. -/
theorem resZ_eq (ι : ℝ) (u z : FA) :
    resZ ι u z = Dof u z * Lt ι z - PolyExpr.eval (xB u z) nZp := by
  rw [resZ, resZp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z noW_Dp, eval_xK_xB ι u z noW_nZp]
  rfl

/-- The polynomials have real (rational) coefficients. -/
theorem realConsts_all : Dp.RealConsts ∧ nRp.RealConsts ∧ nZp.RealConsts ∧ Pp.RealConsts ∧
    resRp.RealConsts ∧ resZp.RealConsts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [PolyExpr.RealConsts, Dp, nRp, nZp, Pp, resRp, resZp, sumE, monoE, PolyExpr.npow,
    map_div₀, map_neg, map_ofNat]

/-! ## The instance of the abstract interface -/

/-- **The rational stellarator `field (1/4)` as a field in flow form**: the polynomials
`Dp, nRp, nZp, Pap, Pbp, Pp` with the identities `divFree`, `flux_a`, `flux_b`, `flux_c`,
`torsion_poly`. -/
def field14 : FlowField where
  Dp := Dp
  nRp := nRp
  nZp := nZp
  Pap := Pap
  Pbp := Pbp
  Pp := Pp
  noW_Dp := noW_Dp
  noW_nRp := noW_nRp
  noW_nZp := noW_nZp
  real_Dp := realConsts_all.1
  real_nRp := realConsts_all.2.1
  real_nZp := realConsts_all.2.2.1
  real_Pp := realConsts_all.2.2.2.1
  divFree := fun u z => divFree (xB u z)
  flux_a := fun u z => flux_a (xB u z)
  flux_b := fun u z => flux_b (xB u z)
  flux_c := fun u z => flux_c (xB u z)
  torsion_poly := fun u z => torsion_poly (xB u z)

/-- `D(K)` of the instance is `D(K)` of `field (1/4)`. -/
theorem field14_Dof (u z : FA) : field14.Dof u z = Dof u z := rfl

/-- `P(K)` of the instance is `P(K)` of `field (1/4)`. -/
theorem field14_Pof (u z : FA) : field14.Pof u z = Pof u z := rfl

/-- The residual polynomial of the instance is `resRp`. -/
theorem field14_resRp : field14.resRp = resRp := rfl

/-- The residual polynomial of the instance is `resZp`. -/
theorem field14_resZp : field14.resZp = resZp := rfl

/-- **Sanity**: the `R`-residual of the instance is the `R`-residual of `field (1/4)`. -/
theorem field14_resR (ι : ℝ) (u z : FA) : field14.resR ι u z = resR ι u z := rfl

/-- The `z`-residual of the instance is the `z`-residual of `field (1/4)`. -/
theorem field14_resZ (ι : ℝ) (u z : FA) : field14.resZ ι u z = resZ ι u z := rfl

end PlasmaLean.Design.KamNewton
