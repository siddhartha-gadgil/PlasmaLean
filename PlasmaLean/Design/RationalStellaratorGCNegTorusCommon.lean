/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTorusCommon
public import PlasmaLean.Design.RationalStellaratorGCNegIota

/-!
# Common steps of the ball certificates of the `v∥ < 0` guiding-centre torus

The steps of `Design/RationalStellaratorGCTorusCommon` (centres of `cos 2φ`, `sin 2φ`, the node
step `vstep`, exact steps) are field- and transform-independent and are reused as they are. The
only transform-dependent step is the transport input: `step_Linput` here is the version for
`ι_B = (161 − √5)/1178` with its dyadic approximation `ι_q = IqB / 2^96`
(`Design/RationalStellaratorGCNegIota`).

**Sanity.** `step_Linput_zero`: for `u = 0` the transport input has radius `0`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open PlasmaLean.Design.RationalStellaratorGC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronBall
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-- **The transport input** `2^96 𝓛u` with the dyadic rotational transform `ι_q ≈ ι_B`: if the
centre is `dS IqB 2^97 u = 2^96 𝓛_{ι_q} u`, then
`‖2^96 𝓛_{ι_B} u − centre‖ ≤ 2^96 |ι_B − ι_q| ‖∂_θ u‖`. -/
theorem step_Linput {r : ℝ} {u xc : FA} (hu : Ana u)
    (hx : xc = dS (((IqB : ℕ) : ℤ) : ℂ) ((((2 : ℕ) ^ 97 : ℕ) : ℤ) : ℂ) u) {Bth : ℚ}
    (hth : Bd r (dTh u) (Bth : ℝ)) {e : ℚ} (he : (2 : ℚ) ^ 96 * (1 / 10 ^ 29) * Bth ≤ e) :
    Bd r ((2 : ℂ) ^ 96 • Lt iotaB u - xc) e := by
  have e1 : xc = (2 : ℂ) ^ 96 • Lt iotaBq u := by
    rw [hx, Lt, ← dS_smul_symbol _ _ _ hu]
    congr 1
    · push_cast; rw [IqB_eq]
    · push_cast; ring
  have e2 : (2 : ℂ) ^ 96 • Lt iotaB u - xc =
      ((2 : ℂ) ^ 96 * ((iotaB - iotaBq : ℝ) : ℂ)) • dTh u := by
    rw [e1, ← smul_sub, Lt, Lt, dTh, mul_smul]
    congr 1
    have h1 : dS (iotaB : ℂ) 2 u = dS (iotaBq : ℂ) 2 u +
        dS (((iotaB - iotaBq : ℝ) : ℂ)) 0 u := by
      rw [← dS_add_symbol _ _ _ _ hu]; congr 1 <;> push_cast <;> ring
    have h2 : dS (((iotaB - iotaBq : ℝ) : ℂ)) 0 u =
        (((iotaB - iotaBq : ℝ) : ℂ)) • dS 1 0 u := by
      rw [← dS_smul_symbol _ _ _ hu]; congr 1 <;> ring
    rw [h1, h2]; abel
  rw [e2]
  refine (hth.smul _).le ?_
  have hi := iotaB_sub_iotaBq
  rw [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  have hB : (0 : ℝ) ≤ Bth := hth.nonneg
  have he' : (2 : ℝ) ^ 96 * (1 / 10 ^ 29) * (Bth : ℝ) ≤ (e : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 he; push_cast at this; exact this
  calc (2 : ℝ) ^ 96 * |iotaB - iotaBq| * Bth ≤ 2 ^ 96 * (1 / 10 ^ 29) * Bth := by gcongr
    _ ≤ (e : ℝ) := he'

/-- Sanity: for `u = 0` the transport input is exact. -/
theorem step_Linput_zero {r : ℝ} :
    Bd r ((2 : ℂ) ^ 96 • Lt iotaB (0 : FA) -
      dS (((IqB : ℕ) : ℤ) : ℂ) ((((2 : ℕ) ^ 97 : ℕ) : ℤ) : ℂ) 0) 0 := by
  have h := step_Linput (r := r) (u := 0) (Bth := 0) (e := 0) Ana.zero rfl
    (by simpa [dTh] using Bd_zero r) (by norm_num)
  simpa using h

end PlasmaLean.Design.RationalStellaratorGCNeg
