/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamIteration
public import PlasmaLean.Design.KamTorusASurrogate

/-!
# Admissibility near torus A: uniform frame and twist bounds (KAM route, K3d)

Every analytic torus `K = (1 + u, z)` that is `μ = 10⁻¹⁰`-close to torus A (`Design/KamTorusAStrip`)
in `u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z` on a strip `0 < ρ ≤ r_A` satisfies the bounds required by the Newton
step (`AdmBounds`), with fixed explicit constants (`torusA_adm`):

* the torus: `‖u‖ ≤ 0.228 + μ`, …, `‖𝓛u‖ ≤ 0.1375·0.236 + 0.13 + μ` (torus A plus `μ`);
* the field polynomials and their partial derivatives, by the majorants of
  `Theory/KAM/Composition` (`‖D‖ ≤ 1.64`, `‖∂_uD‖ ≤ 3.09`, …);
* `‖D⁻¹‖ ≤ 1/(1 − 0.4831)` (Neumann around `d₀ ≥ 1`, from `‖D(K₀) − d₀‖ ≤ 0.483`),
  `‖R⁻¹‖ ≤ 1/(1 − ‖u‖)`, `‖W₀⁻¹‖ ≤ 1/(0.01813 − 0.004079)` (Neumann around the surrogate value
  `w_S`, from `Design/KamTorusASurrogate`);
* **the torsion and the twist**, through the approximate inverse `q` of `D³W₀²` of the surrogate:
  `T₀(K) = Y(K)·(1 + X(K))⁻¹` with `Y = R³ P q`, `X = q D³ W₀² − 1`; on the surrogate
  `‖Y‖ ≤ 19.655`, `Re⟨Y⟩ ≥ 0.3986`, `‖X‖ ≤ 5.13 × 10⁻⁶`, and the Lipschitz bounds of the polynomials
  `R³P` and `D³W₀²` transport these to `K` (distance `≤ 10⁻⁶`): `‖T₀(K)‖ ≤ 19.83`,
  `|⟨T₀(K)⟩| ≥ 0.225`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamTorusA WEll1Z2 PolyExpr

/-! ## The constants -/

/-- The displacement budget `μ = 10⁻¹⁰`. -/
def μA : ℝ := 1 / 10 ^ 10
/-- The bound `e^{r_A} ≤ 74315/2^16` of `cos 2φ`, `sin 2φ`. -/
def acA : ℝ := 74315 / 2 ^ 16
/-- `‖u‖`. -/
def auA : ℝ := 228 / 1000 + μA
/-- `‖z‖`. -/
def azA : ℝ := 224 / 1000 + μA
/-- `‖∂_θu‖`. -/
def aRtA : ℝ := 236 / 1000 + μA
/-- `‖∂_θz‖`. -/
def aztA : ℝ := 231 / 1000 + μA
/-- `‖𝓛u‖`. -/
def aLRA : ℝ := 1375 / 10000 * (236 / 1000) + 130 / 1000 + μA
/-- `‖𝓛z‖`. -/
def aLzA : ℝ := 1375 / 10000 * (231 / 1000) + 126 / 1000 + μA
/-- Bounds of `xB u z = (u, z, c, s, 0, 0)`. -/
def avB : Fin 6 → ℝ := ![auA, azA, acA, acA, 0, 0]

/-- `e^{r_A} ≤ acA`. -/
theorem exp_rA_le_acA : Real.exp rA ≤ acA := by
  have := exp_rA_le; rw [acA]; push_cast at this; exact this

/-! ## Torus bounds -/

section Torus

variable {ρ : ℝ} {u z : FA} (hρA : ρ ≤ rA) (hC : Close ρ iota u z u₀ z₀ μA)
include hρA hC

/-- `‖u‖_ρ ≤ 0.228 + μ`. -/
theorem adm_u : Bd ρ u auA := by
  have := (Bd_u₀.strip hρA).add hC.du
  rwa [add_sub_cancel] at this

/-- `‖z‖_ρ ≤ 0.224 + μ`. -/
theorem adm_z : Bd ρ z azA := by
  have := (Bd_z₀.strip hρA).add hC.dz
  rwa [add_sub_cancel] at this

/-- `‖∂_θu‖_ρ ≤ 0.236 + μ`. -/
theorem adm_Rt : Bd ρ (dTh u) aRtA := by
  have := (Bd_Rθ₀.strip hρA).add hC.dut
  rwa [add_sub_cancel] at this

/-- `‖∂_θz‖_ρ ≤ 0.231 + μ`. -/
theorem adm_zt : Bd ρ (dTh z) aztA := by
  have := (Bd_zθ₀.strip hρA).add hC.dzt
  rwa [add_sub_cancel] at this

/-- `‖𝓛u‖_ρ`. -/
theorem adm_LR : Bd ρ (Lt iota u) aLRA := by
  have h0 := Bd_Lt iota_nonneg ana_u₀ Bd_Rθ₀ Bd_Rψ₀
  have hi := torusAIota_bounds.2
  have h1 : Bd ρ (Lt iota u₀) (1375 / 10000 * (236 / 1000) + 130 / 1000) :=
    (h0.strip hρA).le (by
      have : iota * (236 / 1000) ≤ 1375 / 10000 * (236 / 1000) := by
        unfold iota; unfold torusAIota at hi; gcongr
      linarith)
  have := h1.add hC.duL
  rwa [add_sub_cancel] at this

/-- `‖𝓛z‖_ρ`. -/
theorem adm_Lz : Bd ρ (Lt iota z) aLzA := by
  have h0 := Bd_Lt iota_nonneg ana_z₀ Bd_zθ₀ Bd_zψ₀
  have hi := torusAIota_bounds.2
  have h1 : Bd ρ (Lt iota z₀) (1375 / 10000 * (231 / 1000) + 126 / 1000) :=
    (h0.strip hρA).le (by
      have : iota * (231 / 1000) ≤ 1375 / 10000 * (231 / 1000) := by
        unfold iota; unfold torusAIota at hi; gcongr
      linarith)
  have := h1.add hC.dzL
  rwa [add_sub_cancel] at this

omit hC in
/-- `e^ρ ≤ acA`. -/
theorem adm_exp : Real.exp ρ ≤ acA := (Real.exp_le_exp.2 hρA).trans exp_rA_le_acA

/-- The variables `xB u z` are bounded by `avB`. -/
theorem adm_xB : ∀ i, Bd ρ (xB u z i) (avB i) := by
  intro i
  fin_cases i
  · exact adm_u hρA hC
  · exact adm_z hρA hC
  · exact (Bd_cS ρ).le (adm_exp hρA)
  · exact (Bd_sS ρ).le (adm_exp hρA)
  · exact Bd_zero ρ
  · exact Bd_zero ρ

end Torus

/-! ## Field bounds by majorants -/

/-- Unfolding set for majorant computations. -/
macro "maj_norm" : tactic =>
  `(tactic| (simp only [PolyExpr.maj, PolyExpr.majD, Dp, nRp, nZp, sumE, monoE, PolyExpr.npow,
    avB, auA, azA, acA, μA, Pi.single_apply, Matrix.cons_val, Fin.isValue, norm_div, norm_neg,
    norm_one, Complex.norm_ofNat, Complex.norm_intCast]; norm_num))

/-- The unit directions are bounded. -/
theorem Bd_single (ρ : ℝ) (i j : Fin 6) :
    Bd ρ ((Pi.single i (1 : FA) : Fin 6 → FA) j) ((Pi.single i (1 : ℝ) : Fin 6 → ℝ) j) := by
  by_cases h : j = i
  · subst h; simpa using Bd_one ρ
  · simpa [h] using Bd_zero ρ

/-- The majorant of `D`. -/
theorem maj_D : PolyExpr.maj avB Dp ≤ 164 / 100 := by maj_norm

/-- The majorant of `n_R`. -/
theorem maj_nR : PolyExpr.maj avB nRp ≤ 42 / 100 := by maj_norm
/-- The majorant of `n_z`. -/
theorem maj_nZ : PolyExpr.maj avB nZp ≤ 45 / 100 := by maj_norm
/-- The majorant of `∂_u D`. -/
theorem maj_Du : PolyExpr.majD avB (Pi.single 0 1) Dp ≤ 309 / 100 := by maj_norm
/-- The majorant of `∂_z D`. -/
theorem maj_Dz : PolyExpr.majD avB (Pi.single 1 1) Dp ≤ 61 / 100 := by maj_norm
/-- The majorant of `∂_u n_R`. -/
theorem maj_nRu : PolyExpr.majD avB (Pi.single 0 1) nRp ≤ 171 / 100 := by maj_norm
/-- The majorant of `∂_z n_R`. -/
theorem maj_nRz : PolyExpr.majD avB (Pi.single 1 1) nRp ≤ 108 / 100 := by maj_norm
/-- The majorant of `∂_u n_z`. -/
theorem maj_nZu : PolyExpr.majD avB (Pi.single 0 1) nZp ≤ 159 / 100 := by maj_norm
/-- The majorant of `∂_z n_z`. -/
theorem maj_nZz : PolyExpr.majD avB (Pi.single 1 1) nZp ≤ 143 / 100 := by maj_norm

section Field

variable {ρ : ℝ} {u z : FA} (hρ : 0 < ρ) (hρA : ρ ≤ rA) (hC : Close ρ iota u z u₀ z₀ μA)
include hρ hρA hC

/-- Value bounds of the field polynomials. -/
theorem adm_eval (e : PolyExpr ℂ (Fin 6)) {B : ℝ} (hB : PolyExpr.maj avB e ≤ B) :
    Bd ρ (PolyExpr.eval (xB u z) e) B :=
  (Bd.eval hρ.le (adm_xB hρA hC) e).le hB

/-- Partial derivative bounds of the field polynomials. -/
theorem adm_pd (i : Fin 6) (e : PolyExpr ℂ (Fin 6)) {B : ℝ}
    (hB : PolyExpr.majD avB (Pi.single i 1) e ≤ B) : Bd ρ (pd (xB u z) i e) B :=
  (Bd.deriv hρ.le (adm_xB hρA hC) (Bd_single ρ i) e).le hB

end Field

/-! ## The inverses -/

/-- Bounds of `xB u₀ z₀`. -/
def a0B : Fin 6 → ℝ := ![228 / 1000, 224 / 1000, acA, acA, 0, 0]
/-- The displacement profile `(μ, μ, 0, 0, 0, 0)`. -/
def μB : Fin 6 → ℝ := ![μA, μA, 0, 0, 0, 0]

/-- The Lipschitz majorant of `D` near torus A. -/
theorem lip_D : PolyExpr.majD (a0B + μB) μB Dp ≤ 1 / 10 ^ 8 := by
  simp only [PolyExpr.maj, PolyExpr.majD, Dp, sumE, monoE, PolyExpr.npow, a0B, μB, acA, μA,
    Pi.add_apply, Matrix.cons_val, Fin.isValue, norm_div, norm_neg, norm_one, Complex.norm_ofNat]
  norm_num

/-- `‖D⁻¹‖ ≤ 1/(1 − 0.4831)`. -/
def sDA : ℝ := 1 / (1 - 4831 / 10000)
/-- `‖R⁻¹‖ ≤ 1/(1 − ‖u‖)`. -/
def sRA : ℝ := 1 / (1 - auA)
/-- `‖W₀⁻¹‖ ≤ 1/(0.01813 − 0.004079)`. -/
def sWA : ℝ := 1 / (1813 / 100000 - 4079 / 10 ^ 6)

section Inverses

variable {ρ : ℝ} {u z : FA} (hρ : 0 < ρ) (hρA : ρ ≤ rA) (hC : Close ρ iota u z u₀ z₀ μA)
include hρ hρA hC

/-- `‖D(K) − d₀‖_ρ ≤ 0.483 + 10⁻⁸`. -/
theorem adm_Dsub : Bd ρ (Dof u z - algebraMap ℂ FA (dA0 : ℂ)) (483 / 1000 + 1 / 10 ^ 8) := by
  have hx : ∀ i, Bd ρ (xB u₀ z₀ i) (a0B i) := by
    intro i
    fin_cases i
    · exact Bd_u₀.strip hρA
    · exact Bd_z₀.strip hρA
    · exact (Bd_cS ρ).le (adm_exp hρA)
    · exact (Bd_sS ρ).le (adm_exp hρA)
    · exact Bd_zero ρ
    · exact Bd_zero ρ
  have hh : ∀ i, Bd ρ ((xB u z - xB u₀ z₀) i) (μB i) := by
    intro i
    fin_cases i
    · exact hC.du
    · exact hC.dz
    · simpa [xB, μB] using Bd_zero ρ
    · simpa [xB, μB] using Bd_zero ρ
    · simpa [xB, μB] using Bd_zero ρ
    · simpa [xB, μB] using Bd_zero ρ
  have hL := Bd.eval_add_sub hρ.le hx hh Dp
  rw [add_sub_cancel] at hL
  have e : Dof u z - algebraMap ℂ FA (dA0 : ℂ) = (Dof u₀ z₀ - algebraMap ℂ FA (dA0 : ℂ)) +
      (PolyExpr.eval (xB u z) Dp - PolyExpr.eval (xB u₀ z₀) Dp) := by
    simp only [Dof]; ring
  rw [e]
  exact ((Bd_D₀.strip hρA).add hL).le (by linarith [lip_D])

/-- **`D` is invertible**, `‖D⁻¹‖_ρ ≤ sDA`. -/
theorem adm_Di : IsUnit (Dof u z) ∧ Bd ρ (Ring.inverse (Dof u z)) sDA := by
  have hd0 := torusA_weighted_D.1
  have hn : ‖(dA0 : ℂ)‖ = dA0 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  obtain ⟨hu, hb⟩ := Bd.inverse hρ.le (adm_Dsub hρ hρA hC) (by rw [hn]; linarith)
  refine ⟨hu, hb.le ?_⟩
  rw [hn, sDA]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

/-- **`R` is invertible**, `‖R⁻¹‖_ρ ≤ sRA`. -/
theorem adm_Ri : IsUnit (1 + u) ∧ Bd ρ (Ring.inverse (1 + u)) sRA := by
  have h1 : Bd ρ ((1 + u) - algebraMap ℂ FA 1) auA := by
    rw [map_one, add_sub_cancel_left]; exact adm_u hρA hC
  obtain ⟨hu, hb⟩ := Bd.inverse hρ.le h1 (by rw [norm_one]; norm_num [auA, μA])
  exact ⟨hu, by simpa [sRA] using hb⟩

/-- Distance to the surrogate (values). -/
def dvA : ℝ := μA + 22 / 10 ^ 8
/-- Distance to the surrogate (`θ`-derivatives). -/
def ddA : ℝ := μA + 77 / 10 ^ 8

omit hρ in
/-- `‖u − u_S‖_ρ ≤ dvA` etc. -/
theorem adm_dist : Bd ρ (u - uS) dvA ∧ Bd ρ (z - zS) dvA ∧ Bd ρ (dTh u - dTh uS) ddA ∧
    Bd ρ (dTh z - dTh zS) ddA := by
  obtain ⟨-, ⟨h1, h2, h3, h4⟩, -⟩ := torusA_surrogate
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hC.du.add (h1.strip hρA); rw [sub_add_sub_cancel] at this
    exact this.le (by simp [dvA])
  · have := hC.dz.add (h2.strip hρA); rw [sub_add_sub_cancel] at this
    exact this.le (by simp [dvA])
  · have := hC.dut.add (h3.strip hρA); rw [sub_add_sub_cancel] at this
    exact this.le (by simp [ddA])
  · have := hC.dzt.add (h4.strip hρA); rw [sub_add_sub_cancel] at this
    exact this.le (by simp [ddA])

/-- **`W₀` is invertible**, `‖W₀⁻¹‖_ρ ≤ sWA`. -/
theorem adm_Wi : IsUnit (W0of u z) ∧ Bd ρ (Ring.inverse (W0of u z)) sWA := by
  obtain ⟨-, ⟨h1, h2, h3, h4⟩, ⟨hW, hw1, hw2⟩, -⟩ := torusA_surrogate
  obtain ⟨d1, d2, d3, d4⟩ := adm_dist hρA hC
  have hRtS : Bd ρ (dTh uS) (236 / 1000 + 77 / 10 ^ 8) := by
    have := (Bd_Rθ₀.strip hρA).sub (h3.strip hρA); rwa [sub_sub_cancel] at this
  have hztS : Bd ρ (dTh zS) (231 / 1000 + 77 / 10 ^ 8) := by
    have := (Bd_zθ₀.strip hρA).sub (h4.strip hρA); rwa [sub_sub_cancel] at this
  have hρ0 := hρ.le
  have e : W0of u z - algebraMap ℂ FA (wS : ℂ) = (W0of uS zS - algebraMap ℂ FA (wS : ℂ)) +
      ((dTh u - dTh uS) * z + dTh uS * (z - zS) - ((dTh z - dTh zS) * u + dTh zS * (u - uS))) := by
    simp only [W0of]; ring
  have hb : Bd ρ (W0of u z - algebraMap ℂ FA (wS : ℂ)) (4079 / 10 ^ 6) := by
    rw [e]
    refine ((hW.strip hρA).add (((d3.mul hρ0 (adm_z hρA hC)).add (hRtS.mul hρ0 d2)).sub
      ((d4.mul hρ0 (adm_u hρA hC)).add (hztS.mul hρ0 d1)))).le ?_
    norm_num [dvA, ddA, azA, auA, μA]
  have hn : ‖(wS : ℂ)‖ = -wS := by
    rw [Complex.norm_real, Real.norm_of_nonpos (by linarith)]
  obtain ⟨hu, hi⟩ := Bd.inverse hρ0 hb (by rw [hn]; linarith)
  refine ⟨hu, hi.le ?_⟩
  rw [hn, sWA]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

end Inverses

/-! ## The torsion and the twist -/

/-- `W₀ = a z − b u` as a polynomial in `(u, z, c, s, a = ∂_θu, b = ∂_θz)`. -/
def Wp : PolyExpr ℂ (Fin 6) := sub (mul (var 4) (var 1)) (mul (var 5) (var 0))
/-- `D³ W₀²`. -/
def Fp : PolyExpr ℂ (Fin 6) := mul (npow Dp 3) (npow Wp 2)
/-- `R³ P`. -/
def RPp : PolyExpr ℂ (Fin 6) := mul (npow (add (const 1) (var 0)) 3) Pp
/-- The variables `(u, z, c, s, ∂_θu, ∂_θz)`. -/
def xW (u z : FA) : Fin 6 → FA := ![u, z, cS, sS, dTh u, dTh z]

/-- `F(K) = D³ W₀²`. -/
theorem eval_Fp (u z : FA) : PolyExpr.eval (xW u z) Fp = Dof u z ^ 3 * W0of u z ^ 2 := by
  have h : PolyExpr.eval (xW u z) Dp = Dof u z :=
    eval_congr_noW (fun i hi => by fin_cases i <;> simp_all [xW, xB]) Dp noW_Dp
  simp only [Fp, Wp, PolyExpr.eval, PolyExpr.eval_npow]
  rw [h]; rfl

/-- `RP(K) = R³ P`. -/
theorem eval_RPp (u z : FA) : PolyExpr.eval (xW u z) RPp = (1 + u) ^ 3 * Pof u z := by
  have h : PolyExpr.eval (xW u z) Pp = Pof u z :=
    eval_congr_noW (fun i hi => by fin_cases i <;> simp_all [xW, xB]) Pp noW_Pp
  simp only [RPp, PolyExpr.eval, PolyExpr.eval_npow, h, Algebra.algebraMap_eq_smul_one, one_smul]
  rfl

/-- Bounds of the surrogate variables `xW u_S z_S`. -/
def aSW : Fin 6 → ℝ :=
  ![228 / 1000 + 22 / 10 ^ 8, 224 / 1000 + 22 / 10 ^ 8, acA, acA, 236 / 1000 + 77 / 10 ^ 8,
    231 / 1000 + 77 / 10 ^ 8]
/-- The distance profile to the surrogate. -/
def bSW : Fin 6 → ℝ := ![dvA, dvA, 0, 0, ddA, ddA]

/-- The majorant derivative of a power. -/
theorem majD_npow {σ : Type*} (a b : σ → ℝ) (p : PolyExpr ℂ σ) :
    ∀ k : ℕ, PolyExpr.majD a b (npow p (k + 1)) =
      (k + 1) * PolyExpr.maj a p ^ k * PolyExpr.majD a b p
  | 0 => by simp [npow, PolyExpr.majD, PolyExpr.maj]
  | k + 1 => by
    rw [npow, PolyExpr.majD, majD_npow a b p k, PolyExpr.maj_npow]
    push_cast; ring

/-- Unfolding set for the majorant numerics near the surrogate. -/
macro "majS_norm" : tactic =>
  `(tactic| (simp only [PolyExpr.maj, PolyExpr.majD, Wp, Dp, Pp, sumE, monoE, PolyExpr.npow, aSW,
    bSW, dvA, ddA, acA, μA, Pi.add_apply, Matrix.cons_val, Fin.isValue, norm_div, norm_neg,
    norm_one, Complex.norm_ofNat]; norm_num))

/-- Majorant of `D` near the surrogate. -/
theorem mS_D : PolyExpr.maj (aSW + bSW) Dp ≤ 16389 / 10000 := by majS_norm
/-- Majorant derivative of `D` near the surrogate. -/
theorem dS_D : PolyExpr.majD (aSW + bSW) bSW Dp ≤ 8122 / 10 ^ 10 := by majS_norm
/-- Majorant of `W₀` near the surrogate. -/
theorem mS_W : PolyExpr.maj (aSW + bSW) Wp ≤ 10554 / 100000 := by majS_norm
/-- Majorant derivative of `W₀` near the surrogate. -/
theorem dS_W : PolyExpr.majD (aSW + bSW) bSW Wp ≤ 4509 / 10 ^ 10 := by majS_norm
set_option maxHeartbeats 4000000 in
-- the torsion numerator has 86 monomials; the exact rational evaluation needs more heartbeats
/-- Majorant of `P` near the surrogate. -/
theorem mS_P : PolyExpr.maj (aSW + bSW) Pp ≤ 1182 / 10000 := by majS_norm
set_option maxHeartbeats 4000000 in
-- the torsion numerator has 86 monomials; the exact rational evaluation needs more heartbeats
/-- Majorant derivative of `P` near the surrogate. -/
theorem dS_P : PolyExpr.majD (aSW + bSW) bSW Pp ≤ 464 / 10 ^ 9 := by majS_norm

/-- The Lipschitz majorant of `D³W₀²`. -/
theorem lip_F : PolyExpr.majD (aSW + bSW) bSW Fp ≤ 5 / 10 ^ 7 := by
  rw [Fp, PolyExpr.majD, majD_npow _ _ _ 2, majD_npow _ _ _ 1, PolyExpr.maj_npow,
    PolyExpr.maj_npow]
  have h1 := mS_D; have h2 := dS_D; have h3 := mS_W; have h4 := dS_W
  have hab : ∀ i, 0 ≤ (aSW + bSW) i := fun i => by
    fin_cases i <;> norm_num [aSW, bSW, dvA, ddA, acA, μA]
  have hb : ∀ i, 0 ≤ bSW i := fun i => by
    fin_cases i <;> norm_num [bSW, dvA, ddA, μA]
  have n1 := PolyExpr.maj_nonneg (𝕜 := ℂ) hab Dp
  have n2 := PolyExpr.majD_nonneg (𝕜 := ℂ) hab hb Dp
  have n3 := PolyExpr.maj_nonneg (𝕜 := ℂ) hab Wp
  have n4 := PolyExpr.majD_nonneg (𝕜 := ℂ) hab hb Wp
  calc ((2 : ℕ) + 1 : ℝ) * PolyExpr.maj (aSW + bSW) Dp ^ 2 * PolyExpr.majD (aSW + bSW) bSW Dp *
          PolyExpr.maj (aSW + bSW) Wp ^ 2 +
        PolyExpr.maj (aSW + bSW) Dp ^ 3 *
          (((1 : ℕ) + 1 : ℝ) * PolyExpr.maj (aSW + bSW) Wp ^ 1 * PolyExpr.majD (aSW + bSW) bSW Wp)
      ≤ ((2 : ℕ) + 1 : ℝ) * (16389 / 10000) ^ 2 * (8122 / 10 ^ 10) * (10554 / 100000) ^ 2 +
        (16389 / 10000) ^ 3 * (((1 : ℕ) + 1 : ℝ) * (10554 / 100000) ^ 1 * (4509 / 10 ^ 10)) := by
        gcongr
    _ ≤ _ := by norm_num

/-- The Lipschitz majorant of `R³ P`. -/
theorem lip_RP : PolyExpr.majD (aSW + bSW) bSW RPp ≤ 1 / 10 ^ 6 := by
  rw [RPp, PolyExpr.majD, majD_npow _ _ _ 2, PolyExpr.maj_npow]
  have hab : ∀ i, 0 ≤ (aSW + bSW) i := fun i => by
    fin_cases i <;> norm_num [aSW, bSW, dvA, ddA, acA, μA]
  have hb : ∀ i, 0 ≤ bSW i := fun i => by
    fin_cases i <;> norm_num [bSW, dvA, ddA, μA]
  have h1 := mS_P; have h2 := dS_P
  have n1 := PolyExpr.maj_nonneg (𝕜 := ℂ) hab Pp
  have n2 := PolyExpr.majD_nonneg (𝕜 := ℂ) hab hb Pp
  have e1 : PolyExpr.maj (aSW + bSW) (add (const (1 : ℂ)) (var 0) : PolyExpr ℂ (Fin 6)) =
      1 + (228 / 1000 + 22 / 10 ^ 8 + (μA + 22 / 10 ^ 8)) := by
    simp [PolyExpr.maj, aSW, bSW, dvA]
  have e2 : PolyExpr.majD (aSW + bSW) bSW (add (const (1 : ℂ)) (var 0) : PolyExpr ℂ (Fin 6)) =
      μA + 22 / 10 ^ 8 := by
    simp [PolyExpr.majD, bSW, dvA]
  rw [e1, e2]
  calc ((2 : ℕ) + 1 : ℝ) * (1 + (228 / 1000 + 22 / 10 ^ 8 + (μA + 22 / 10 ^ 8))) ^ 2 *
          (μA + 22 / 10 ^ 8) * PolyExpr.maj (aSW + bSW) Pp +
        (1 + (228 / 1000 + 22 / 10 ^ 8 + (μA + 22 / 10 ^ 8))) ^ 3 *
          PolyExpr.majD (aSW + bSW) bSW Pp
      ≤ ((2 : ℕ) + 1 : ℝ) * (1 + (228 / 1000 + 22 / 10 ^ 8 + (μA + 22 / 10 ^ 8))) ^ 2 *
          (μA + 22 / 10 ^ 8) * (1182 / 10000) +
        (1 + (228 / 1000 + 22 / 10 ^ 8 + (μA + 22 / 10 ^ 8))) ^ 3 * (464 / 10 ^ 9) := by
        have : 0 ≤ μA := by norm_num [μA]
        gcongr
    _ ≤ _ := by norm_num [μA]

/-- The torsion bound `‖T₀‖ ≤ 19.84`. -/
def tTA : ℝ := 1984 / 100
/-- The twist bound `|⟨T₀⟩| ≥ 0.22`. -/
def τA : ℝ := 22 / 100

section Twist

variable {ρ : ℝ} {u z : FA} (hρ : 0 < ρ) (hρA : ρ ≤ rA) (hC : Close ρ iota u z u₀ z₀ μA)
include hρ hρA hC

omit hρ hC in
/-- The surrogate variables are bounded by `aSW`. -/
theorem adm_xWS : ∀ i, Bd ρ (xW uS zS i) (aSW i) := by
  obtain ⟨-, ⟨h1, h2, h3, h4⟩, -⟩ := torusA_surrogate
  intro i
  fin_cases i
  · have := (Bd_u₀.strip hρA).sub (h1.strip hρA); rwa [sub_sub_cancel] at this
  · have := (Bd_z₀.strip hρA).sub (h2.strip hρA); rwa [sub_sub_cancel] at this
  · exact (Bd_cS ρ).le (adm_exp hρA)
  · exact (Bd_sS ρ).le (adm_exp hρA)
  · have := (Bd_Rθ₀.strip hρA).sub (h3.strip hρA); rwa [sub_sub_cancel] at this
  · have := (Bd_zθ₀.strip hρA).sub (h4.strip hρA); rwa [sub_sub_cancel] at this

omit hρ in
/-- The displacement from the surrogate is bounded by `bSW`. -/
theorem adm_xWd : ∀ i, Bd ρ ((xW u z - xW uS zS) i) (bSW i) := by
  obtain ⟨d1, d2, d3, d4⟩ := adm_dist hρA hC
  intro i
  fin_cases i
  · exact d1
  · exact d2
  · simpa [xW, bSW] using Bd_zero ρ
  · simpa [xW, bSW] using Bd_zero ρ
  · exact d3
  · exact d4

/-- **Torsion and twist near torus A**: `‖T₀(K)‖_ρ ≤ 19.84` and `|⟨T₀(K)⟩| ≥ 0.22`. -/
theorem adm_T : Bd ρ (Talg u z) tTA ∧ τA ≤ ‖avg (Talg u z)‖ := by
  obtain ⟨⟨-, -, -, -, -, ana_q⟩, -, -, ⟨hX4, hq⟩, ⟨hX5, hav, -⟩⟩ := torusA_surrogate
  have hρ0 := hρ.le
  have hF := Bd.eval_add_sub hρ0 (adm_xWS hρA) (adm_xWd hρA hC) Fp
  have hRP := Bd.eval_add_sub hρ0 (adm_xWS hρA) (adm_xWd hρA hC) RPp
  rw [add_sub_cancel] at hF hRP
  replace hF := hF.le lip_F
  replace hRP := hRP.le lip_RP
  set Fk := PolyExpr.eval (xW u z) Fp with hFk
  set RPk := PolyExpr.eval (xW u z) RPp with hRPk
  have hFS : PolyExpr.eval (xW uS zS) Fp = Dof uS zS ^ 3 * W0of uS zS ^ 2 := eval_Fp uS zS
  have hRPS : PolyExpr.eval (xW uS zS) RPp = (1 + uS) ^ 3 * Pof uS zS := eval_RPp uS zS
  rw [hFS] at hF; rw [hRPS] at hRP
  -- `X = q F − 1` and `Y = RP q`
  have hX : Bd ρ (qS * Fk - 1) (513 / 10 ^ 8 + 16162 * (5 / 10 ^ 7)) := by
    have e : qS * Fk - 1 = (qS * Dof uS zS ^ 3 * W0of uS zS ^ 2 - 1) +
        qS * (Fk - Dof uS zS ^ 3 * W0of uS zS ^ 2) := by ring
    rw [e]; exact (hX4.strip hρA).add ((hq.strip hρA).mul hρ0 hF)
  have hY : Bd ρ (RPk * qS) (19655 / 1000 + 1 / 10 ^ 6 * 16162) := by
    have e : RPk * qS = (1 + uS) ^ 3 * Pof uS zS * qS + (RPk - (1 + uS) ^ 3 * Pof uS zS) * qS := by
      ring
    rw [e]; exact (hX5.strip hρA).add (hRP.mul hρ0 (hq.strip hρA))
  have hX1 : Bd ρ (qS * Fk - algebraMap ℂ FA 1) (513 / 10 ^ 8 + 16162 * (5 / 10 ^ 7)) := by
    rwa [map_one]
  obtain ⟨hU, hInv⟩ := Bd.inverse hρ0 hX1 (by rw [norm_one]; norm_num)
  rw [norm_one] at hInv
  -- the representation `T₀ = Y (1 + X)⁻¹`
  obtain ⟨hDu, -⟩ := adm_Di hρ hρA hC
  obtain ⟨hWu, -⟩ := adm_Wi hρ hρA hC
  have hrep : Talg u z = RPk * qS * Ring.inverse (qS * Fk) := by
    refine ext_eval fun θ ψ => ?_
    have hD := eval_ne_zero_of_unit hDu θ ψ
    have hW := eval_ne_zero_of_unit hWu θ ψ
    have hU' : IsUnit (qS * (Dof u z ^ 3 * W0of u z ^ 2)) := by rw [← eval_Fp]; exact hU
    have hQ := eval_ne_zero_of_unit hU' θ ψ
    rw [hFk, eval_Fp]
    rw [hRPk, eval_RPp]
    simp only [Talg, Di, Wi, eval_mul, eval_pow', eval_inverse hDu, eval_inverse hWu,
      eval_inverse hU', eval_add', eval_one] at hQ ⊢
    have hq0 : eval qS θ ψ ≠ 0 := left_ne_zero_of_mul hQ
    field_simp
  have hyb : (0 : ℝ) < 1 - (513 / 10 ^ 8 + 16162 * (5 / 10 ^ 7)) := by norm_num
  refine ⟨?_, ?_⟩
  · rw [hrep]
    refine (hY.mul hρ0 hInv).le ?_
    norm_num [tTA]
  · -- `(1 + X)⁻¹ = 1 − X (1 + X)⁻¹`
    have hI : Ring.inverse (qS * Fk) = 1 - (qS * Fk - 1) * Ring.inverse (qS * Fk) := by
      have := Ring.mul_inverse_cancel _ hU
      linear_combination this
    have e : Talg u z = RPk * qS - RPk * qS * (qS * Fk - 1) * Ring.inverse (qS * Fk) := by
      rw [hrep]; nth_rewrite 1 [hI]; ring
    rw [e, avg_sub]
    have h1 : ‖avg (RPk * qS * (qS * Fk - 1) * Ring.inverse (qS * Fk))‖ ≤
        (19655 / 1000 + 1 / 10 ^ 6 * 16162) * (513 / 10 ^ 8 + 16162 * (5 / 10 ^ 7)) *
          (1 / (1 - (513 / 10 ^ 8 + 16162 * (5 / 10 ^ 7)))) :=
      ((hY.mul hρ0 hX).mul hρ0 hInv).norm_avg_le hρ0
    have h2 : ‖avg ((RPk - (1 + uS) ^ 3 * Pof uS zS) * qS)‖ ≤ 1 / 10 ^ 6 * 16162 :=
      (hRP.mul hρ0 (hq.strip hρA)).norm_avg_le hρ0
    have h3 : avg (RPk * qS) = avg ((1 + uS) ^ 3 * Pof uS zS * qS) +
        avg ((RPk - (1 + uS) ^ 3 * Pof uS zS) * qS) := by
      rw [← avg_add]; ring_nf
    have h4 : (3986 / 10000 : ℝ) ≤ ‖avg ((1 + uS) ^ 3 * Pof uS zS * qS)‖ :=
      hav.trans (Complex.re_le_norm _)
    have h5 := norm_sub_norm_le (avg (RPk * qS))
      (avg (RPk * qS * (qS * Fk - 1) * Ring.inverse (qS * Fk)))
    have h6 := norm_sub_norm_le (avg ((1 + uS) ^ 3 * Pof uS zS * qS))
      (-avg ((RPk - (1 + uS) ^ 3 * Pof uS zS) * qS))
    rw [sub_neg_eq_add, ← h3, norm_neg] at h6
    have h7 : ‖avg (RPk * qS) - avg (RPk * qS * (qS * Fk - 1) * Ring.inverse (qS * Fk))‖ ≥
        ‖avg (RPk * qS)‖ - ‖avg (RPk * qS * (qS * Fk - 1) * Ring.inverse (qS * Fk))‖ := by
      have := norm_sub_norm_le (avg (RPk * qS))
        (avg (RPk * qS * (qS * Fk - 1) * Ring.inverse (qS * Fk)))
      linarith
    unfold τA
    norm_num at h1
    linarith

end Twist

end PlasmaLean.Design.KamNewton
