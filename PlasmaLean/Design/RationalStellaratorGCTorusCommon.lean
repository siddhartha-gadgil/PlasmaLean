/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallGrid
public import PlasmaLean.Design.RationalStellaratorGCInstance
public import PlasmaLean.Theory.KAM.InvSqrtApprox
public import PlasmaLean.Design.KamTorusAWeighted
public import PlasmaLean.Design.KamTorusA

/-!
# Common steps of the ball certificates of the guiding-centre torus

Shared lemmas of the two ball pipelines of the guiding-centre torus certificate
(`Design/RationalStellaratorGCTorusResidual`, `Design/RationalStellaratorGCTorusAdmL`):

* the centres of the constant variables: `cos 2φ` and `sin 2φ` (`ctr_cPoly`, `ctr_sPoly`) and
  their norms on strips `e^r ≤ 74315/2^16` (`Bd_cS_q`, `Bd_sS_q`);
* `isqG_le`: a rational upper bound of `(1 − m)^{−1/2}`;
* **the node step** `vstep`: from the norm nodes `‖V₀ − 1‖`, `‖V₀² − 1‖`,
  `‖V₀²(1 + E) − 1‖` and a bound of `‖E‖`, the ball `‖(1 + E)^{−1/2} − V₀‖ ≤ ε`
  (`invSqrt_approx_bound` with the Neumann inverse of `V₀`);
* `exp_rA_le'`: the strip `r_A = 0.1257` satisfies the weight condition.

**Sanity.** `isqG_le_zero`: `(1 − 0)^{−1/2} ≤ 1`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronBall
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-- The centre of `C = v² − 1` (weight `(0, 1, 3)`) is `cos 2φ`. -/
theorem ctr_cPoly (S N M : ℕ) : ctr S N M (0, 1, 3) cPoly = cS := by
  have hP : phiK cPoly = mode 0 (0, 2) - 1 := by
    rw [cPoly, map_sub, phiK_monomial, phiK_monomial]
    simp [mode_zero_pair]
  rw [ctr, hP, sub_mul, one_mul, mode_mul, cS]
  have e1 : ((0 : ℤ), (2 : ℤ)) + -ofsW N M (0, 1, 3) = (0, 1) := by ext <;> simp [ofsW]
  have e2 : -ofsW N M (0, 1, 3) = (0, -1) := by ext <;> simp [ofsW]
  rw [e1, e2]
  have e3 : (scal S (0, 1, 3))⁻¹ = I / 2 := by
    simp only [scal, mul_zero, zero_add, pow_one]
    rw [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]
    field_simp
    rw [I_sq]
  rw [e3]

/-- The centre of `S = v² + 1` (weight `(0, 1, 0)`) is `sin 2φ`. -/
theorem ctr_sPoly (S N M : ℕ) : ctr S N M (0, 1, 0) sPoly = sS := by
  have hP : phiK sPoly = mode 0 (0, 2) + 1 := by
    rw [sPoly, map_add, phiK_monomial, phiK_monomial]
    simp [mode_zero_pair]
  rw [ctr, hP, add_mul, one_mul, mode_mul, sS]
  have e1 : ((0 : ℤ), (2 : ℤ)) + -ofsW N M (0, 1, 0) = (0, 1) := by ext <;> simp [ofsW]
  have e2 : -ofsW N M (0, 1, 0) = (0, -1) := by ext <;> simp [ofsW]
  rw [e1, e2]
  have e3 : (scal S (0, 1, 0))⁻¹ = 1 / 2 := by
    simp only [scal, mul_zero, zero_add, pow_one, pow_zero, mul_one]
    norm_num
  rw [e3]

/-- `‖cos 2φ‖_r ≤ 74315/2^16` on strips with `e^r ≤ 74315/2^16`. -/
theorem Bd_cS_q {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) :
    Bd r cS (((74315 / 2 ^ 16 : ℚ) : ℚ) : ℝ) :=
  (Bd_cS r).le (by push_cast at hq ⊢; linarith)

/-- `‖sin 2φ‖_r ≤ 74315/2^16` on strips with `e^r ≤ 74315/2^16`. -/
theorem Bd_sS_q {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) :
    Bd r sS (((74315 / 2 ^ 16 : ℚ) : ℚ) : ℝ) :=
  (Bd_sS r).le (by push_cast at hq ⊢; linarith)

/-- The strip `r_A` satisfies the weight condition. -/
theorem exp_rA_le' : Real.exp KamTorusA.rA ≤ (74315 : ℕ) / 2 ^ 16 := KamTorusA.exp_rA_le

/-- **A rational bound of `(1 − m)^{−1/2}`**: `g² (1 − m) ≥ 1`, `g ≥ 0` give `isqG 1 m ≤ g`. -/
theorem isqG_le {m g : ℝ} (hm : m < 1) (hg0 : 0 ≤ g) (hg : 1 ≤ g ^ 2 * (1 - m)) :
    isqG 1 m ≤ g := by
  unfold isqG
  have h1 : 0 < 1 - m := by linarith
  have hs : 0 < Real.sqrt (1 - m) := Real.sqrt_pos.2 h1
  have hgp : 0 < g := by
    rcases hg0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hg; norm_num at hg
  rw [inv_le_comm₀ hs hgp, Real.le_sqrt (by positivity) h1.le, inv_pow,
    inv_le_iff_one_le_mul₀ (by positivity)]
  linarith

/-- **Sanity**: `(1 − 0)^{−1/2} ≤ 1`. -/
theorem isqG_le_zero : isqG 1 0 ≤ 1 := isqG_le (by norm_num) (by norm_num) (by norm_num)

/-- **The node step.** From the norm nodes `‖V₀ − 1‖ ≤ a`, `‖V₀² − 1‖ ≤ n₂`,
`‖V₀²(1 + E) − 1‖ ≤ η` and `‖E‖ ≤ e`, with rational choices `b ≥ 1/(1 − a)`,
`m ≥ max(b² n₂, e)`, `g ≥ (1 − m)^{−1/2}`: `‖(1 + E)^{−1/2} − V₀‖ ≤ ½ g³ b² η ≤ ε`. -/
theorem vstep {r : ℝ} (hr : 0 ≤ r) {E V0 : FA} {a n2 η b m g ε e : ℝ}
    (h1 : Bd r (V0 - 1) a) (h2 : Bd r (V0 ^ 2 - 1) n2) (h3 : Bd r (V0 ^ 2 * (1 + E) - 1) η)
    (hE : Bd r E e) (ha : a < 1) (hb : 1 / (1 - a) ≤ b) (hm1 : b ^ 2 * n2 ≤ m) (hm2 : e ≤ m)
    (hm : m < 1) (hg0 : 0 ≤ g) (hg : 1 ≤ g ^ 2 * (1 - m)) (hsmall : g ^ 3 / 2 * m + a < 2)
    (heps : g ^ 3 / 2 * (b ^ 2 * η) ≤ ε) :
    Bd r (invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + E) - V0) ε := by
  have h1' : Bd r (V0 - algebraMap ℂ FA 1) a := by rwa [map_one]
  obtain ⟨hu, hVi⟩ := Bd.inverse hr h1' (by rw [norm_one]; exact ha)
  rw [norm_one] at hVi
  have hinv : V0 * Ring.inverse V0 = 1 := Ring.mul_inverse_cancel _ hu
  have hb' : Bd r (Ring.inverse V0) b := hVi.le hb
  have hVi2 : Bd r (Ring.inverse V0 ^ 2 - 1) m := by
    have e1 : Ring.inverse V0 ^ 2 - 1 = Ring.inverse V0 ^ 2 * (-(V0 ^ 2 - 1)) := by
      linear_combination (Ring.inverse V0 * V0 + 1) * hinv
    rw [e1]
    exact ((hb'.pow hr 2).mul hr h2.neg).le hm1
  have hx : Bd r (algebraMap ℂ FA ((1 : ℝ) : ℂ) + E - 1) m := by
    rw [Complex.ofReal_one, map_one, add_sub_cancel_left]; exact hE.le hm2
  have hg' : isqG 1 m ≤ g := isqG_le hm hg0 hg
  have hgn : 0 ≤ isqG 1 m := isqG_nonneg 1 m
  have hm0 : 0 ≤ m := hE.nonneg.trans hm2
  have hsm : isqG 1 m ^ 3 / 2 * m + a < 2 := by
    have : isqG 1 m ^ 3 ≤ g ^ 3 := pow_le_pow_left₀ hgn hg' 3
    nlinarith
  have hη : Bd r (V0 ^ 2 * (algebraMap ℂ FA ((1 : ℝ) : ℂ) + E) - 1) η := by
    rw [Complex.ofReal_one, map_one]; exact h3
  have h := invSqrt_approx_bound hr hinv hx hVi2 hm h1 hsm hb' hη
  refine h.le (le_trans ?_ heps)
  have hη0 : 0 ≤ η := h3.nonneg
  have : isqG 1 m ^ 3 ≤ g ^ 3 := pow_le_pow_left₀ hgn hg' 3
  have hb2 : 0 ≤ b ^ 2 * η := by positivity
  nlinarith

/-- **An exact step of a ball chain**: a variable whose value is its centre has radius `0`. -/
theorem step_exact {r : ℝ} {X x : FA} {e : ℚ} (h : X = x) (he : 0 ≤ e) : Bd r (X - x) e := by
  rw [h, sub_self]; exact (Bd_zero r).le (by exact_mod_cast he)

/-- **The transport input** `2^96 𝓛u` with the dyadic rotational transform: if the centre is
`dS Iq 2^97 u = 2^96 𝓛_{ι_q} u`, then `‖2^96 𝓛_ι u − centre‖ ≤ 2^96 |ι − ι_q| ‖∂_θ u‖`. -/
theorem step_Linput {r : ℝ} {u xc : FA} (hu : Ana u)
    (hx : xc = dS (((KamTorusA.Iq : ℕ) : ℤ) : ℂ) ((((2 : ℕ) ^ 97 : ℕ) : ℤ) : ℂ) u) {Bth : ℚ}
    (hth : Bd r (dTh u) (Bth : ℝ)) {e : ℚ} (he : (2 : ℚ) ^ 96 * (1 / 10 ^ 29) * Bth ≤ e) :
    Bd r ((2 : ℂ) ^ 96 • Lt KamTorusA.iota u - xc) e := by
  have e1 : xc = (2 : ℂ) ^ 96 • Lt KamTorusA.iotaQ u := by
    rw [hx, Lt, ← dS_smul_symbol _ _ _ hu]
    congr 1
    · push_cast; rw [KamTorusA.Iq_eq, KamTorusA.Q]
    · push_cast; ring
  have e2 : (2 : ℂ) ^ 96 • Lt KamTorusA.iota u - xc =
      ((2 : ℂ) ^ 96 * ((KamTorusA.iota - KamTorusA.iotaQ : ℝ) : ℂ)) • dTh u := by
    rw [e1, ← smul_sub, Lt, Lt, dTh, mul_smul]
    congr 1
    have h1 : dS (KamTorusA.iota : ℂ) 2 u = dS (KamTorusA.iotaQ : ℂ) 2 u +
        dS (((KamTorusA.iota - KamTorusA.iotaQ : ℝ) : ℂ)) 0 u := by
      rw [← dS_add_symbol _ _ _ _ hu]; congr 1 <;> push_cast <;> ring
    have h2 : dS (((KamTorusA.iota - KamTorusA.iotaQ : ℝ) : ℂ)) 0 u =
        (((KamTorusA.iota - KamTorusA.iotaQ : ℝ) : ℂ)) • dS 1 0 u := by
      rw [← dS_smul_symbol _ _ _ hu]; congr 1 <;> ring
    rw [h1, h2]; abel
  rw [e2]
  refine (hth.smul _).le ?_
  have hi := KamTorusA.iota_sub_iotaQ
  rw [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  have hB : (0 : ℝ) ≤ Bth := hth.nonneg
  have he' : (2 : ℝ) ^ 96 * (1 / 10 ^ 29) * (Bth : ℝ) ≤ (e : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 he; push_cast at this; exact this
  calc (2 : ℝ) ^ 96 * |KamTorusA.iota - KamTorusA.iotaQ| * Bth ≤
        2 ^ 96 * (1 / 10 ^ 29) * Bth := by gcongr
    _ ≤ (e : ℝ) := he'

end PlasmaLean.Design.RationalStellaratorGC
