/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCNegStarCheck
public import PlasmaLean.Design.RationalStellaratorGCNegTorusReal
public import PlasmaLean.Design.RationalStellaratorForeverCert

/-!
# The `v∥ < 0` guiding-centre torus `K₀` is star-shaped about the magnetic axis

The certified approximate guiding-centre torus of `gcFlow (−1/256)` (`ι_B`)
`K₀ = (R₀, z₀) = (1 + Re F_{u₀G}, Re F_{z₀G})` (`Design/RationalStellaratorGCNegTorusAdm`; real
functions `Rof u₀G`, `Zof z₀G`) winds around the exact magnetic axis `R = 1, z = 0` of
`field (1/4)` as a radial graph:

* **`gc_radial_ge`**: `(R₀ − 1) cos θ + z₀ sin θ ≥ 0.028` (star-shapedness with respect to the
  flow angle `θ`: the polar angle of `(R₀ − 1, z₀)` about the axis has the smooth lift
  `θ + arctan(…)`);
* **`gc_winding_ge`**: `(R₀ − 1) ∂_θ z₀ − z₀ ∂_θ R₀ ≥ 0.0058` (the polar angle increases strictly
  with `θ`).

(Numerically: radial value in `[0.055, 0.187]`, winding rate `≥ 0.0070`; mean `0.01106`.) This GC
torus is shifted outwards (`R ∈ [0.905, 1.187]`) but still encircles `R = 1`, so the tube
coordinates `rt, θs, φs` about the exact axis serve for it as well.

**Method** (as `RationalStellaratorForeverCert` for torus A): `u₀G = 2^{−101} e^{−i(Nθ+Mψ)} P_U`,
`z₀G = −i 2^{−101} e^{−i(Nθ+Mψ)} P_Z` with integer grid polynomials `P_U = PH 4`, `P_Z = PH 5`
(and `∂_θ` grids `PH 8`, `PH 9`) (`eval_xH_ctr`, from `eval_phiK`), so the two quantities are the
values on the torus `u = e^{iθ}, v = e^{iψ}` of the integer polynomials `radPolyG` and
`windPolyG` divided by `2^{102} u^{N+1} v^M`, resp. `2^{202} u^{2N} v^{2M}` (`evalC_radPolyG`,
`evalC_windPolyG`); the kernel checks `check_radG`, `check_windG` bound their centre coefficients
against the exact `ℓ¹` norm of the remainder.

**Sanity.** `eval_phiK_X`: the polynomial variable `u` evaluates to `e^{iθ}`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open PlasmaLean.Design.RationalStellaratorGC

open Polynomial PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton
  PlasmaLean.Design.KamTorusA WEll1Z2 Complex

/-! ## Evaluation of grid centres -/

/-- `e^{iψ}`. -/
def vψ (ψ : ℝ) : ℂ := Complex.exp (ψ * I)

/-- **Evaluation of `phiK`**: the strip-algebra image of an integer polynomial evaluates to the
polynomial at `u = e^{iθ}`, `v = e^{iψ}`. -/
theorem eval_phiK (P : P2) (θ ψ : ℝ) : WEll1Z2.eval (phiK P) θ ψ = evalC (uu θ) (vψ ψ) P := by
  have h : (evalHom θ ψ).comp phiK = evalC (uu θ) (vψ ψ) := by
    apply Polynomial.ringHom_ext
    · intro a
      have : ((evalHom θ ψ).comp phiK).comp Polynomial.C =
          (evalC (uu θ) (vψ ψ)).comp Polynomial.C := by
        apply Polynomial.ringHom_ext
        · intro n; simp [phiK, evalC]
        · simp only [RingHom.coe_comp, Function.comp_apply, phiK, evalC,
            Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
          simp [evalHom, eval_mode, fourierMode, uu]
      exact congrArg (fun f => f a) this
    · simp only [RingHom.coe_comp, Function.comp_apply, phiK, evalC, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      simp [evalHom, eval_mode, fourierMode, vψ]
  exact congrArg (fun f => f P) h

/-- **Sanity**: the polynomial variable `u` evaluates to `e^{iθ}`. -/
theorem eval_phiK_X (θ ψ : ℝ) :
    WEll1Z2.eval (phiK (Polynomial.C Polynomial.X)) θ ψ = uu θ := by
  rw [eval_phiK]; simp [evalC]

/-- `e^{−i(Nθ + Mψ)} = (uᴺ vᴹ)⁻¹`. -/
theorem fourierMode_neg (N M : ℕ) (θ ψ : ℝ) :
    fourierMode (-(N : ℤ), -(M : ℤ)) θ ψ = (uu θ ^ N * vψ ψ ^ M)⁻¹ := by
  simp only [fourierMode, uu, vψ, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_neg]
  congr 1
  push_cast; ring

/-- **Evaluation of a high-resolution centre** of weight `(1, 0, p)`:
`F_{xH i} = (2^{101} i^p)⁻¹ P_i(u, v) (uᴺ vᴹ)⁻¹`. -/
theorem eval_ctr_one (p : ℕ) (P : P2) (θ ψ : ℝ) :
    WEll1Z2.eval (ctr SH NH MH (1, 0, p) P) θ ψ =
      (scal SH (1, 0, p))⁻¹ * evalC (uu θ) (vψ ψ) P * (uu θ ^ NH * vψ ψ ^ MH)⁻¹ := by
  rw [ctr, Theory.KAM.eval_smul', WEll1Z2.eval_mul, eval_phiK, neg_offs, eval_mode]
  simp only [one_mul, add_zero]
  rw [fourierMode_neg, mul_assoc]

/-- `|e^{iθ}| = 1`. -/
theorem norm_vψ (ψ : ℝ) : ‖vψ ψ‖ = 1 := by
  rw [vψ, Complex.norm_exp_ofReal_mul_I]

/-- `uᴺ vᴹ ≠ 0`. -/
theorem uv_ne_zero (θ ψ : ℝ) (a b : ℕ) : uu θ ^ a * vψ ψ ^ b ≠ 0 := by
  simp [uu, vψ, Complex.exp_ne_zero]

/-- The grid polynomial of `u₀G` on the torus. -/
theorem evalC_PU (θ ψ : ℝ) : evalC (uu θ) (vψ ψ) (PH 4) =
    (2 : ℂ) ^ 101 * WEll1Z2.eval u₀G θ ψ * (uu θ ^ NH * vψ ψ ^ MH) := by
  have h := eval_ctr_one 0 (PH 4) θ ψ
  rw [show ctr SH NH MH (1, 0, 0) (PH 4) = u₀G from rfl, scal, SH] at h
  rw [h]
  have hu : uu θ ≠ 0 := Complex.exp_ne_zero _
  have hv : vψ ψ ≠ 0 := Complex.exp_ne_zero _; field_simp; ring

/-- The grid polynomial of `z₀G` on the torus. -/
theorem evalC_PZ (θ ψ : ℝ) : evalC (uu θ) (vψ ψ) (PH 5) =
    (2 : ℂ) ^ 101 * I * WEll1Z2.eval z₀G θ ψ * (uu θ ^ NH * vψ ψ ^ MH) := by
  have h := eval_ctr_one 1 (PH 5) θ ψ
  rw [show ctr SH NH MH (1, 0, 1) (PH 5) = z₀G from rfl, scal, SH] at h
  rw [h]
  have hu : uu θ ≠ 0 := Complex.exp_ne_zero _
  have hv : vψ ψ ≠ 0 := Complex.exp_ne_zero _; field_simp; ring

/-- The grid polynomial of `∂_θ u₀G` on the torus. -/
theorem evalC_PthU (θ ψ : ℝ) : evalC (uu θ) (vψ ψ) (PH 8) =
    -((2 : ℂ) ^ 101 * I) * WEll1Z2.eval (dTh u₀G) θ ψ * (uu θ ^ NH * vψ ψ ^ MH) := by
  have h := eval_ctr_one 3 (PH 8) θ ψ
  rw [show ctr SH NH MH (1, 0, 3) (PH 8) = xH 8 from rfl, dTh_xH_thU, scal, SH] at h
  rw [h]
  have hu : uu θ ≠ 0 := Complex.exp_ne_zero _
  have hv : vψ ψ ≠ 0 := Complex.exp_ne_zero _
  have hI : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  rw [hI]; field_simp

/-- The grid polynomial of `∂_θ z₀G` on the torus. -/
theorem evalC_PthZ (θ ψ : ℝ) : evalC (uu θ) (vψ ψ) (PH 9) =
    (2 : ℂ) ^ 101 * WEll1Z2.eval (dTh z₀G) θ ψ * (uu θ ^ NH * vψ ψ ^ MH) := by
  have h := eval_ctr_one 0 (PH 9) θ ψ
  rw [show ctr SH NH MH (1, 0, 0) (PH 9) = xH 9 from rfl, dTh_xH_thZ, scal, SH] at h
  rw [h]
  have hu : uu θ ≠ 0 := Complex.exp_ne_zero _
  have hv : vψ ψ ≠ 0 := Complex.exp_ne_zero _; field_simp; ring

/-! ## The radial and winding polynomials -/

/-- The radial polynomial `Ŵ = (P_U + P_Z) + (P_U − P_Z) u²` of `K₀`. -/
noncomputable def radPolyG : P2 := (PH 4 + PH 5) + (PH 4 - PH 5) * uSqP

/-- The winding polynomial `N̂ = P_U P_{θZ} − P_Z P_{θU}` of `K₀`. -/
noncomputable def windPolyG : P2 := PH 4 * PH 9 - PH 5 * PH 8

/-- The radial value `(R₀ − 1) cos θ + z₀ sin θ` of `K₀`. -/
def radG (θ φ : ℝ) : ℝ := (Rof u₀G θ φ - 1) * Real.cos θ + Zof z₀G θ φ * Real.sin θ

/-- The winding rate `(R₀ − 1) ∂_θ z₀ − z₀ ∂_θ R₀` of `K₀`. -/
def windG (θ φ : ℝ) : ℝ :=
  (Rof u₀G θ φ - 1) * (WEll1Z2.eval (dTh z₀G) θ (psi φ)).re -
    Zof z₀G θ φ * (WEll1Z2.eval (dTh u₀G) θ (psi φ)).re

/-- `Ŵ` on the torus: `2^{102} u^{N+1} v^M` times the radial value. -/
theorem evalC_radPolyG (θ φ : ℝ) : evalC (uu θ) (vψ (psi φ)) radPolyG =
    (((2 : ℝ) ^ 102 * radG θ φ : ℝ) : ℂ) * (uu θ ^ (NH + 1) * vψ (psi φ) ^ MH) := by
  have hU := evalC_PU θ (psi φ)
  have hZ := evalC_PZ θ (psi φ)
  rw [eval_ofReal_re isReal_u₀G] at hU
  rw [eval_ofReal_re isReal_z₀G] at hZ
  have hr := rad_identity θ (WEll1Z2.eval u₀G θ (psi φ)).re (WEll1Z2.eval z₀G θ (psi φ)).re
  rw [radPolyG, map_add, map_add, map_mul, map_sub, hU, hZ, uSqP, evalC_monomial, radG, Rof, Zof,
    add_sub_cancel_left]
  push_cast at hr ⊢
  linear_combination ((2 : ℂ) ^ 101 * (uu θ ^ NH * vψ (psi φ) ^ MH)) * hr

/-- `N̂` on the torus: `2^{202} u^{2N} v^{2M}` times the winding rate. -/
theorem evalC_windPolyG (θ φ : ℝ) : evalC (uu θ) (vψ (psi φ)) windPolyG =
    (((2 : ℝ) ^ 202 * windG θ φ : ℝ) : ℂ) * (uu θ ^ (2 * NH) * vψ (psi φ) ^ (2 * MH)) := by
  have hU := evalC_PU θ (psi φ)
  have hZ := evalC_PZ θ (psi φ)
  have hA := evalC_PthU θ (psi φ)
  have hB := evalC_PthZ θ (psi φ)
  rw [eval_ofReal_re isReal_u₀G] at hU
  rw [eval_ofReal_re isReal_z₀G] at hZ
  rw [eval_ofReal_re (isReal_dTh isReal_u₀G)] at hA
  rw [eval_ofReal_re (isReal_dTh isReal_z₀G)] at hB
  rw [windPolyG, map_sub, map_mul, map_mul, hU, hZ, hA, hB, windG, Rof, Zof, add_sub_cancel_left]
  push_cast
  linear_combination ((2 : ℂ) ^ 202 * (uu θ ^ NH * vψ (psi φ) ^ MH) ^ 2 *
    ((WEll1Z2.eval z₀G θ (psi φ)).re : ℂ) * ((WEll1Z2.eval (dTh u₀G) θ (psi φ)).re : ℂ)) * I_sq

/-- The centre monomial of `Ŵ`. -/
noncomputable def radMonoG : P2 := monomial MH (monomial (NH + 1) (c0radG : ℤ))

/-- The centre monomial of `N̂`. -/
noncomputable def windMonoG : P2 := monomial (2 * MH) (monomial (2 * NH) (c0windG : ℤ))

/-- The exact `ℓ¹` norm of `Ŵ − c0radG u^{N+1} v^M` is the kernel digit sum. -/
theorem l1_radSubG : l1 (radPolyG - radMonoG) = l1Kron 130 13 radIntG := by
  have hk : kron 130 83 (radPolyG - radMonoG) = radIntG := by
    rw [map_sub, radPolyG, map_add, map_add, map_mul, map_sub, kronH, kronH, kron_uSqP, radMonoG,
      kron_monomial, radIntG, pow2_eq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← hk]
  have h4 := boxH 4
  have h5 := boxH 5
  simp only [BxH] at h4 h5
  refine l1_eq_l1Kron (a := 2 * NH + 2) (J := 2 * MH) (by norm_num) ?_ (by norm_num [NH])
    (by norm_num [MH]) ?_
  · unfold radPolyG
    exact InBox.sub (InBox.add ((h4.add h5).mono (by omega) le_rfl)
      (((h4.sub h5).mul (InBox.monomial _ _ _)).mono le_rfl (by omega)))
      ((InBox.monomial _ _ _).mono (by omega) (by omega))
  · have hA : l1 (PH 4 + PH 5) ≤ LH 4 + LH 5 := l1_add' (l1H 4) (l1H 5)
    have hB : l1 (PH 4 - PH 5) ≤ LH 4 + LH 5 := l1_sub' (l1H 4) (l1H 5)
    have hUl : l1 uSqP ≤ 1 := by rw [uSqP, l1_monomial]; simp
    have hW : l1 radPolyG ≤ 2 * (LH 4 + LH 5) := by
      unfold radPolyG
      have := l1_add' hA (l1_mul' hB hUl)
      omega
    have hM : l1 radMonoG ≤ c0radG := by rw [radMonoG, l1_monomial]; simp
    exact (l1_sub' hW hM).trans_lt apriori_radG

/-- The exact `ℓ¹` norm of `N̂ − c0windG u^{2N} v^{2M}` is the kernel digit sum. -/
theorem l1_windSubG : l1 (windPolyG - windMonoG) = l1Kron 257 15 windIntG := by
  have hk : kron 257 161 (windPolyG - windMonoG) = windIntG := by
    rw [map_sub, windPolyG, map_sub, map_mul, map_mul, kronH, kronH, kronH, kronH, windMonoG,
      kron_monomial, windIntG, pow2_eq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← hk]
  have h4 := boxH 4
  have h5 := boxH 5
  have h8 := boxH 8
  have h9 := boxH 9
  simp only [BxH] at h4 h5 h8 h9
  refine l1_eq_l1Kron (a := 4 * NH) (J := 4 * MH) (by norm_num) ?_ (by norm_num [NH])
    (by norm_num [MH]) ?_
  · unfold windPolyG
    exact InBox.sub (InBox.sub ((h4.mul h9).mono (by omega) (by omega))
      ((h5.mul h8).mono (by omega) (by omega)))
      ((InBox.monomial _ _ _).mono (by omega) (by omega))
  · have hW : l1 windPolyG ≤ LH 4 * LH 9 + LH 5 * LH 8 := by
      unfold windPolyG
      exact l1_sub' (l1_mul' (l1H 4) (l1H 9)) (l1_mul' (l1H 5) (l1H 8))
    have hM : l1 windMonoG ≤ c0windG := by rw [windMonoG, l1_monomial]; simp
    exact (l1_sub' hW hM).trans_lt apriori_windG

/-! ## The certified bounds -/

/-- **`K₀` is star-shaped about the magnetic axis in its flow angle**:
`(R₀ − 1) cos θ + z₀ sin θ ≥ 0.028`. -/
theorem gc_radial_ge (θ φ : ℝ) : 7 / 250 ≤ radG θ φ := by
  have hκ : (0 : ℝ) < 2 ^ 102 := by positivity
  have hlow := le_of_evalC (norm_uu θ) (norm_vψ (psi φ)) hκ (c0radG : ℤ) (evalC_radPolyG θ φ)
  rw [show (monomial MH (monomial (NH + 1) ((c0radG : ℕ) : ℤ)) : P2) = radMonoG from rfl,
    l1_radSubG] at hlow
  have c : 250 * (l1Kron 130 13 radIntG : ℝ) + 7 * 2 ^ 102 ≤ 250 * (c0radG : ℝ) := by
    exact_mod_cast check_radG
  push_cast at hlow
  refine le_trans ?_ hlow
  rw [le_div_iff₀ hκ]; linarith

/-- **The polar angle of `K₀` about the axis increases with `θ`**:
`(R₀ − 1) ∂_θ z₀ − z₀ ∂_θ R₀ ≥ 0.0058`. -/
theorem gc_winding_ge (θ φ : ℝ) : 29 / 5000 ≤ windG θ φ := by
  have hκ : (0 : ℝ) < 2 ^ 202 := by positivity
  have hlow := le_of_evalC (norm_uu θ) (norm_vψ (psi φ)) hκ (c0windG : ℤ)
    (evalC_windPolyG θ φ)
  rw [show (monomial (2 * MH) (monomial (2 * NH) ((c0windG : ℕ) : ℤ)) : P2) = windMonoG from rfl,
    l1_windSubG] at hlow
  have c : 5000 * (l1Kron 257 15 windIntG : ℝ) + 29 * 2 ^ 202 ≤ 5000 * (c0windG : ℝ) := by
    exact_mod_cast check_windG
  push_cast at hlow
  refine le_trans ?_ hlow
  rw [le_div_iff₀ hκ]; linarith

end PlasmaLean.Design.RationalStellaratorGCNeg
