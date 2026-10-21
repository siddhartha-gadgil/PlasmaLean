/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowFieldS
public import PlasmaLean.Design.KamFlowFrame

/-!
# The symplectic frame for a flow field with an inverse-square-root node (KAM route)

The frame of `Design/KamFlowFrame`, verbatim, for a field `F : FlowFieldS`
(`Design/KamFlowFieldS`): the expressions may contain the node `isqrt c d = (c + d)^{−1/2}`, the
flux primitive has a `dφ`-component `P_c`, and the identities of the interface hold at tori where
the expressions are strip valid. The frame hypotheses `FlowFieldS.FrameHyp` therefore contain the
validity `F.Good u z`; with it the chain rule `dS_evalB` (`PolyExprS.dS_evalS`) and analyticity
of all field quantities hold as before.

**Identities** (same statements as for `FlowField`): `LR_eq`, `dTh_LR`, `frame_decomp_R/Z`,
`torsion_coord`, `S_coord` (area preservation via `divFree`), `eta2_flux` and `avg_eta2` (the flux
identity, now with the extra term `∂_θ P_c(K)` in the `dφ`-component of the pulled-back primitive),
`linear_residual_R/Z`, `newton_error_R/Z`.

**Sanity.** `frame_det` (`w (∂_θK × N) = 1`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM Complex WEll1Z2

namespace FlowFieldS

variable (F : FlowFieldS)

section Frame

variable (ι : ℝ) (u z : FA)

/-- `D(K)`. -/
def DD : FA := F.Dof u z
/-- `D⁻¹`. -/
def Di : FA := Ring.inverse (F.Dof u z)
/-- `n_R`. -/
def nR : FA := PolyExprS.eval (xB u z) F.nRp
/-- `n_z`. -/
def nZ : FA := PolyExprS.eval (xB u z) F.nZp
/-- `∂_u D`. -/
def Du : FA := pdS (xB u z) 0 F.Dp
/-- `∂_z D`. -/
def Dz : FA := pdS (xB u z) 1 F.Dp
/-- `∂_u n_R`. -/
def nRu : FA := pdS (xB u z) 0 F.nRp
/-- `∂_z n_R`. -/
def nRz : FA := pdS (xB u z) 1 F.nRp
/-- `∂_u n_z`. -/
def nZu : FA := pdS (xB u z) 0 F.nZp
/-- `∂_z n_z`. -/
def nZz : FA := pdS (xB u z) 1 F.nZp
/-- `Ê_R = E_R / D`. -/
def EhR : FA := F.resR ι u z * F.Di u z
/-- `Ê_z = E_z / D`. -/
def EhZ : FA := F.resZ ι u z * F.Di u z
/-- `X_R = n_R / D`. -/
def XR : FA := F.nR u z * F.Di u z
/-- `X_z = n_z / D`. -/
def XZ : FA := F.nZ u z * F.Di u z
/-- `(DX)_{RR}`. -/
def A11 : FA := (F.nRu u z - F.XR u z * F.Du u z) * F.Di u z
/-- `(DX)_{Rz}`. -/
def A12 : FA := (F.nRz u z - F.XR u z * F.Dz u z) * F.Di u z
/-- `(DX)_{zR}`. -/
def A21 : FA := (F.nZu u z - F.XZ u z * F.Du u z) * F.Di u z
/-- `(DX)_{zz}`. -/
def A22 : FA := (F.nZz u z - F.XZ u z * F.Dz u z) * F.Di u z
/-- The area density `w = D/R³`. -/
def wD : FA := F.Dof u z * Ri u ^ 3
/-- `h = R³/(D W₀) = 1/(w W₀)`. -/
def hN : FA := (1 + u) ^ 3 * F.Di u z * Wi u z
/-- `N_R = h u`. -/
def NR : FA := F.hN u z * u
/-- `N_z = h z`. -/
def NZ : FA := F.hN u z * z
/-- The first frame coordinate of the error, `η₁ = W₀⁻¹ (Ê × V₀)`. -/
def eta1 : FA := Wi u z * (z * F.EhR ι u z - u * F.EhZ ι u z)
/-- The second frame coordinate of the error, `η₂ = w (∂_θK × Ê)`. -/
def eta2 : FA := F.wD u z * (Rt u * F.EhZ ι u z - zt z * F.EhR ι u z)
/-- The algebraic torsion density `T₀ = R³ P / (D³ W₀²)`. -/
def Talg : FA := (1 + u) ^ 3 * F.Di u z ^ 3 * Wi u z ^ 2 * F.Pof u z
/-- The torsion `T = T₀ + R³ D⁻¹ W₀⁻² (Ê × V₀)`. -/
def Tor : FA :=
  F.Talg u z + (1 + u) ^ 3 * F.Di u z * Wi u z ^ 2 * (F.EhR ι u z * z - F.EhZ ι u z * u)
/-- The remainder coefficient `S = −(∇D·Ê)/D + 3Ê_R/R − (∂_θÊ × V₀)/W₀`. -/
def Scoef : FA :=
  -((F.Du u z * F.EhR ι u z + F.Dz u z * F.EhZ ι u z) * F.Di u z) + 3 * Ri u * F.EhR ι u z -
    Wi u z * (dTh (F.EhR ι u z) * z - dTh (F.EhZ ι u z) * u)

/-- `R`-component of `𝓛N − DX·N` (with `𝓛N = (𝓛h) V₀ + h 𝓛K`, product rule). -/
def YRt : FA :=
  Lt ι (F.hN u z) * u + F.hN u z * LR ι u - (F.A11 u z * F.NR u z + F.A12 u z * F.NZ u z)
/-- `z`-component of `𝓛N − DX·N`. -/
def YZt : FA :=
  Lt ι (F.hN u z) * z + F.hN u z * Lz ι z - (F.A21 u z * F.NR u z + F.A22 u z * F.NZ u z)
/-- `P_a(K)`. -/
def Pa : FA := PolyExprS.eval (xB u z) F.Pap
/-- `P_b(K)`. -/
def Pb : FA := PolyExprS.eval (xB u z) F.Pbp
/-- `P_c(K)`, the `dφ`-coefficient of the flux primitive at the torus. -/
def Pc : FA := PolyExprS.eval (xB u z) F.Pcp
/-- The flux primitive coefficient `a = P_a / R`. -/
def aF : FA := F.Pa u z * Ri u
/-- The flux primitive coefficient `b = P_b / R²`. -/
def bF : FA := F.Pb u z * Ri u ^ 2
/-- The `dθ`-component `A = a ∂_θR + b ∂_θz` of the pulled-back primitive. -/
def AF : FA := F.aF u z * Rt u + F.bF u z * zt z
/-- The `dφ`-component `B = a ∂_φR + b ∂_φz + c` of the pulled-back primitive. -/
def BF : FA := F.aF u z * dPh u + F.bF u z * dPh z + F.Pc u z

end Frame


/-- The Taylor remainder of the `R`-residual. -/
def QR (ι : ℝ) (u z ΔR ΔZ : FA) : FA :=
  PolyExprS.eval (xK ι u z + hDel ι ΔR ΔZ) F.resRp - PolyExprS.eval (xK ι u z) F.resRp -
    PolyExprS.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resRp

/-- The Taylor remainder of the `z`-residual. -/
def QZ (ι : ℝ) (u z ΔR ΔZ : FA) : FA :=
  PolyExprS.eval (xK ι u z + hDel ι ΔR ΔZ) F.resZp - PolyExprS.eval (xK ι u z) F.resZp -
    PolyExprS.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resZp

/-- Standing hypotheses of the frame: analytic torus, invertible `D`, `R`, `W₀` with analytic
inverses. -/
structure FrameHyp (u z : FA) : Prop where
  /-- `u = R − 1` is analytic. -/
  ana_u : Ana u
  /-- `z` is analytic. -/
  ana_z : Ana z
  /-- `D` is invertible. -/
  unit_D : IsUnit (F.Dof u z)
  /-- `R` is invertible. -/
  unit_R : IsUnit (1 + u)
  /-- `W₀` is invertible. -/
  unit_W : IsUnit (W0of u z)
  /-- `D⁻¹` is analytic. -/
  ana_Di : Ana (Ring.inverse (F.Dof u z))
  /-- `R⁻¹` is analytic. -/
  ana_Ri : Ana (Ring.inverse (1 + u))
  /-- `W₀⁻¹` is analytic. -/
  ana_Wi : Ana (Ring.inverse (W0of u z))
  /-- The field expressions are strip valid at the torus. -/
  good : F.Good u z


namespace FrameHyp

variable {F : FlowFieldS} {ι : ℝ} {u z : FA} (H : F.FrameHyp u z)
include H

/-- The variables of `xB` are analytic. -/
theorem ana_xB : ∀ i, Ana (xB u z i) := fun i => by
  fin_cases i
  · exact H.ana_u
  · exact H.ana_z
  · exact ana_cS
  · exact ana_sS
  · exact Ana.zero
  · exact Ana.zero

/-- The variables of `xK` are analytic. -/
theorem ana_xK : ∀ i, Ana (xK ι u z i) := fun i => by
  fin_cases i
  · exact H.ana_u
  · exact H.ana_z
  · exact ana_cS
  · exact ana_sS
  · exact H.ana_u.d _ _
  · exact H.ana_z.d _ _

omit H in
/-- The unit vectors are analytic. -/
theorem ana_single (i : Fin 6) : ∀ j, Ana ((Pi.single i 1 : Fin 6 → FA) j) := fun j => by
  by_cases h : j = i
  · subst h; simpa using Ana.one
  · simpa [h] using Ana.zero

/-- Expressions valid wherever the field is valid are analytic at the torus. -/
theorem ana_evalB {e : PolyExprS ℂ (Fin 6)} (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e) :
    Ana (PolyExprS.eval (xB u z) e) := by
  obtain ⟨ρ, hρ, a, hx, hv⟩ := H.good
  exact ⟨ρ, _, hρ, PolyExprS.Bd.evalS hρ.le hx (he a hv)⟩

/-- Partial derivatives of valid expressions are analytic at the torus. -/
theorem ana_pdB (i : Fin 6) {e : PolyExprS ℂ (Fin 6)}
    (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e) : Ana (pdS (xB u z) i e) := by
  obtain ⟨ρ, hρ, a, hx, hv⟩ := H.good
  exact PolyExprS.SValid.ana_deriv ⟨ρ, hρ, a, hx, he a hv⟩ (ana_single i)

/-- Chain rule for valid expressions of the torus (any multiplier). -/
theorem dS_evalB (a b : ℂ) {e : PolyExprS ℂ (Fin 6)}
    (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e) :
    dS a b (PolyExprS.eval (xB u z) e) =
      pdS (xB u z) 0 e * dS a b u + pdS (xB u z) 1 e * dS a b z +
        pdS (xB u z) 2 e * dS a b cS + pdS (xB u z) 3 e * dS a b sS := by
  obtain ⟨ρ, hρ, a', hx, hv⟩ := H.good
  rw [PolyExprS.dS_evalS a b hρ hx (he a' hv), deriv_eq_sum_pdS, Fin.sum_univ_six]
  have h4 : xB u z 4 = 0 := rfl
  have h5 : xB u z 5 = 0 := rfl
  rw [h4, h5, dS_zero]
  simp only [xB]
  simp only [Matrix.cons_val, Fin.isValue]
  ring

/-- `∂_θ` of a polynomial of the torus. -/
theorem dTh_evalB {e : PolyExprS ℂ (Fin 6)} (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e) :
    dTh (PolyExprS.eval (xB u z) e) = pdS (xB u z) 0 e * Rt u + pdS (xB u z) 1 e * zt z := by
  have := H.dS_evalB 1 0 he
  rw [dTh, this, show dS 1 0 cS = 0 from dTh_cS, show dS 1 0 sS = 0 from dTh_sS]
  simp only [mul_zero, add_zero]; rfl

/-- `𝓛` of a polynomial of the torus: `∇P·𝓛K + ∂_φP`. -/
theorem Lt_evalB {e : PolyExprS ℂ (Fin 6)} (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e) :
    Lt ι (PolyExprS.eval (xB u z) e) =
      pdS (xB u z) 0 e * LR ι u + pdS (xB u z) 1 e * Lz ι z + phiDS (xB u z) e := by
  have := H.dS_evalB (ι : ℂ) 2 he
  rw [Lt, this, show dS ι 2 cS = Lt ι cS from rfl, show dS ι 2 sS = Lt ι sS from rfl, Lt_cS,
    Lt_sS, two_smul_eq, two_smul_eq]
  simp only [LR, Lz, Lt, phiDS, xB, Matrix.cons_val, Fin.isValue]
  ring

/-- `∂_φ` of a polynomial of the torus. -/
theorem dPh_evalB {e : PolyExprS ℂ (Fin 6)} (he : ∀ a, F.Valid6 a → PolyExprS.Valid a e) :
    dPh (PolyExprS.eval (xB u z) e) =
      pdS (xB u z) 0 e * dPh u + pdS (xB u z) 1 e * dPh z + phiDS (xB u z) e := by
  have := H.dS_evalB 0 2 he
  rw [dPh, this, show dS 0 2 cS = dPh cS from rfl, show dS 0 2 sS = dPh sS from rfl, dPh_cS,
    dPh_sS, two_smul_eq, two_smul_eq]
  simp only [dPh, phiDS, xB, Matrix.cons_val, Fin.isValue]
  ring

/-! ### Units and pointwise evaluation -/

/-- `D D⁻¹ = 1`. -/
theorem D_Di : F.Dof u z * F.Di u z = 1 := Ring.mul_inverse_cancel _ H.unit_D
/-- `R R⁻¹ = 1`. -/
theorem R_Ri : (1 + u) * Ri u = 1 := Ring.mul_inverse_cancel _ H.unit_R
/-- `W₀ W₀⁻¹ = 1`. -/
theorem W_Wi : W0of u z * Wi u z = 1 := Ring.mul_inverse_cancel _ H.unit_W

/-- `D ≠ 0` pointwise. -/
theorem eval_D_ne (θ ψ : ℝ) : eval (F.Dof u z) θ ψ ≠ 0 := eval_ne_zero_of_unit H.unit_D θ ψ
/-- `R ≠ 0` pointwise. -/
theorem eval_R_ne (θ ψ : ℝ) : 1 + eval u θ ψ ≠ 0 := by
  have := eval_ne_zero_of_unit H.unit_R θ ψ; rwa [eval_add', eval_one] at this
/-- `W₀ ≠ 0` pointwise. -/
theorem eval_W_ne (θ ψ : ℝ) :
    eval (dTh u) θ ψ * eval z θ ψ - eval (dTh z) θ ψ * eval u θ ψ ≠ 0 := by
  have := eval_ne_zero_of_unit H.unit_W θ ψ
  rwa [W0of, eval_sub', eval_mul, eval_mul] at this

/-- `D⁻¹` pointwise. -/
theorem eval_Di (θ ψ : ℝ) : eval (F.Di u z) θ ψ = (eval (F.Dof u z) θ ψ)⁻¹ :=
  eval_inverse H.unit_D θ ψ
/-- `R⁻¹` pointwise. -/
theorem eval_Ri (θ ψ : ℝ) : eval (Ri u) θ ψ = (1 + eval u θ ψ)⁻¹ := by
  rw [Ri, eval_inverse H.unit_R, eval_add', eval_one]
/-- `W₀⁻¹` pointwise. -/
theorem eval_Wi (θ ψ : ℝ) :
    eval (Wi u z) θ ψ = (eval (dTh u) θ ψ * eval z θ ψ - eval (dTh z) θ ψ * eval u θ ψ)⁻¹ := by
  rw [Wi, eval_inverse H.unit_W, W0of, eval_sub', eval_mul, eval_mul]

end FrameHyp


namespace FrameHyp

variable {F : FlowFieldS} {ι : ℝ} {u z : FA} (H : F.FrameHyp u z)
include H

/-! ### Analyticity of the frame objects -/

/-- Analyticity: `anaDi`. -/
theorem anaDi : Ana (F.Di u z) := H.ana_Di
/-- Analyticity: `anaRi`. -/
theorem anaRi : Ana (Ri u) := H.ana_Ri
/-- Analyticity: `anaWi`. -/
theorem anaWi : Ana (Wi u z) := H.ana_Wi
/-- Analyticity: `ana_Rt`. -/
theorem ana_Rt : Ana (Rt u) := H.ana_u.d 1 0
/-- Analyticity: `ana_zt`. -/
theorem ana_zt : Ana (zt z) := H.ana_z.d 1 0
/-- Analyticity: `ana_LR`. -/
theorem ana_LR : Ana (LR ι u) := H.ana_u.d ι 2
/-- Analyticity: `ana_Lz`. -/
theorem ana_Lz : Ana (Lz ι z) := H.ana_z.d ι 2
/-- Analyticity: `ana_D`. -/
theorem ana_D : Ana (F.Dof u z) := H.ana_evalB (fun _ h => h.1)
/-- Analyticity: `ana_nR`. -/
theorem ana_nR : Ana (F.nR u z) := H.ana_evalB (fun _ h => h.2.1)
/-- Analyticity: `ana_nZ`. -/
theorem ana_nZ : Ana (F.nZ u z) := H.ana_evalB (fun _ h => h.2.2.1)
/-- Analyticity: `ana_resR`. -/
theorem ana_resR : Ana (F.resR ι u z) := by
  rw [F.resR_eq]; exact (H.ana_D.mul (H.ana_u.d _ _)).sub H.ana_nR
/-- Analyticity: `ana_resZ`. -/
theorem ana_resZ : Ana (F.resZ ι u z) := by
  rw [F.resZ_eq]; exact (H.ana_D.mul (H.ana_z.d _ _)).sub H.ana_nZ
/-- Analyticity: `ana_EhR`. -/
theorem ana_EhR : Ana (F.EhR ι u z) := H.ana_resR.mul H.anaDi
/-- Analyticity: `ana_EhZ`. -/
theorem ana_EhZ : Ana (F.EhZ ι u z) := H.ana_resZ.mul H.anaDi
/-- Analyticity: `ana_XR`. -/
theorem ana_XR : Ana (F.XR u z) := H.ana_nR.mul H.anaDi
/-- Analyticity: `ana_XZ`. -/
theorem ana_XZ : Ana (F.XZ u z) := H.ana_nZ.mul H.anaDi
/-- Analyticity: `ana_R`. -/
theorem ana_R : Ana (1 + u) := Ana.one.add H.ana_u
/-- Analyticity: `ana_hN`. -/
theorem ana_hN : Ana (F.hN u z) := ((H.ana_R.pow 3).mul H.anaDi).mul H.anaWi
/-- Analyticity: `ana_wD`. -/
theorem ana_wD : Ana (F.wD u z) := H.ana_D.mul (H.anaRi.pow 3)
/-- Analyticity: `ana_W`. -/
theorem ana_W : Ana (W0of u z) := (H.ana_Rt.mul H.ana_z).sub (H.ana_zt.mul H.ana_u)
/-- Analyticity of the torsion numerator. -/
theorem ana_Pof : Ana (F.Pof u z) := by
  have p := fun (i : Fin 6) => H.ana_pdB i (e := F.Dp) (fun _ h => h.1)
  have q := fun (i : Fin 6) => H.ana_pdB i (e := F.nRp) (fun _ h => h.2.1)
  have r := fun (i : Fin 6) => H.ana_pdB i (e := F.nZp) (fun _ h => h.2.2.1)
  have hD : Ana (F.Dof u z) := H.ana_D
  have hnR : Ana (PolyExprS.eval (xB u z) F.nRp) := H.ana_nR
  have hnZ : Ana (PolyExprS.eval (xB u z) F.nZp) := H.ana_nZ
  unfold FlowFieldS.Pof
  exact ((((hnR.mul hD).sub (hD.mul (((q 0).mul H.ana_u).add ((q 1).mul H.ana_z)))).add
      (hnR.mul (((p 0).mul H.ana_u).add ((p 1).mul H.ana_z)))).mul H.ana_z).sub
    ((((hnZ.mul hD).sub (hD.mul (((r 0).mul H.ana_u).add ((r 1).mul H.ana_z)))).add
      (hnZ.mul (((p 0).mul H.ana_u).add ((p 1).mul H.ana_z)))).mul H.ana_u)

/-- Close an identity with inverses pointwise (`field_simp`). -/
macro "unit_closeS" H:term : tactic =>
  `(tactic| (try simp only [Rt, zt]
             refine ext_eval fun θ ψ => ?_
             have hD := ($H).eval_D_ne θ ψ
             have hR := ($H).eval_R_ne θ ψ
             have hW := ($H).eval_W_ne θ ψ
             have hW' : eval (dTh u) θ ψ * eval z θ ψ - eval u θ ψ * eval (dTh z) θ ψ ≠ 0 := by
               rw [mul_comm (eval u θ ψ)]; exact hW
             have hW'' : eval z θ ψ * eval (dTh u) θ ψ - eval u θ ψ * eval (dTh z) θ ψ ≠ 0 := by
               rw [mul_comm (eval u θ ψ), mul_comm (eval z θ ψ)]; exact hW
             eval_push
             simp only [($H).eval_Di, ($H).eval_Ri, ($H).eval_Wi]
             first | (field_simp; done) | (field_simp; ring)))

/-- `w h = W₀⁻¹`. -/
theorem wD_hN : F.wD u z * F.hN u z = Wi u z := by
  simp only [wD, hN]; unit_closeS H

/-- `h W₀ = R³ D⁻¹`. -/
theorem hN_W : F.hN u z * W0of u z = (1 + u) ^ 3 * F.Di u z := by
  simp only [hN, W0of]; unit_closeS H

/-- `w W₀ h = 1`. -/
theorem wWh : F.wD u z * W0of u z * F.hN u z = 1 := by
  simp only [wD, hN, W0of]; unit_closeS H

/-- **Sanity: the frame is symplectic**, `w (∂_θK × N) = 1`. -/
theorem frame_det : F.wD u z * (Rt u * F.NZ u z - zt z * F.NR u z) = 1 := by
  simp only [wD, NZ, NR, hN]; unit_closeS H

/-- **`𝓛K = X + Ê`** (`R` component). -/
theorem LR_eq : LR ι u = F.XR u z + F.EhR ι u z := by
  have e := F.resR_eq ι u z
  simp only [XR, EhR, nR, LR]
  rw [e]; unit_closeS H

/-- **`𝓛K = X + Ê`** (`z` component). -/
theorem Lz_eq : Lz ι z = F.XZ u z + F.EhZ ι u z := by
  have e := F.resZ_eq ι u z
  simp only [XZ, EhZ, nZ, Lz]
  rw [e]; unit_closeS H

/-- **Frame decomposition**: `Y = (W₀⁻¹ Y × V₀) ∂_θK + (w ∂_θK × Y) N` (`R` component). -/
theorem frame_decomp_R (YR YZ : FA) :
    YR = Wi u z * (YR * z - YZ * u) * Rt u + F.wD u z * (Rt u * YZ - zt z * YR) * F.NR u z := by
  simp only [wD, NR, hN]; unit_closeS H

/-- **Frame decomposition** (`z` component). -/
theorem frame_decomp_Z (YR YZ : FA) :
    YZ = Wi u z * (YR * z - YZ * u) * zt z + F.wD u z * (Rt u * YZ - zt z * YR) * F.NZ u z := by
  simp only [wD, NZ, hN]; unit_closeS H

/-- The error is the frame combination of its coordinates: `Ê = η₁ ∂_θK + η₂ N`. -/
theorem Eh_decomp :
    F.EhR ι u z = F.eta1 ι u z * Rt u + F.eta2 ι u z * F.NR u z ∧
      F.EhZ ι u z = F.eta1 ι u z * zt z + F.eta2 ι u z * F.NZ u z := by
  refine ⟨?_, ?_⟩
  · have := H.frame_decomp_R (F.EhR ι u z) (F.EhZ ι u z)
    rw [eta1, eta2]; linear_combination this
  · have := H.frame_decomp_Z (F.EhR ι u z) (F.EhZ ι u z)
    rw [eta1, eta2]; linear_combination this

/-- `∂_θ` of the inverse of `D`. -/
theorem dTh_Di : dTh (F.Di u z) = -(F.Di u z ^ 2 * (F.Du u z * Rt u + F.Dz u z * zt z)) := by
  rw [Di, dTh, dS_inverse 1 0 H.ana_D H.unit_D H.ana_Di]
  have := H.dTh_evalB (fun _ h => h.1)
  rw [dTh] at this
  rw [Dof, this]; rfl

/-- **`𝓛 ∂_θK = DX·∂_θK + ∂_θÊ`** (`R` component, as `∂_θ 𝓛R`). -/
theorem dTh_LR :
    dTh (LR ι u) = F.A11 u z * Rt u + F.A12 u z * zt z + dTh (F.EhR ι u z) := by
  rw [H.LR_eq, dTh, dS_add 1 0 H.ana_XR H.ana_EhR, XR, dS_mul 1 0 H.ana_nR H.anaDi]
  have h1 := H.dTh_evalB (fun _ h => h.2.1)
  have h2 := H.dTh_Di
  rw [dTh] at h1 h2
  rw [nR, h1, h2, ← nR, ← dTh]
  simp only [A11, A12, XR, nRu, nRz, Du, Dz]
  ring

/-- **`𝓛 ∂_θK = DX·∂_θK + ∂_θÊ`** (`z` component). -/
theorem dTh_Lz :
    dTh (Lz ι z) = F.A21 u z * Rt u + F.A22 u z * zt z + dTh (F.EhZ ι u z) := by
  rw [H.Lz_eq, dTh, dS_add 1 0 H.ana_XZ H.ana_EhZ, XZ, dS_mul 1 0 H.ana_nZ H.anaDi]
  have h1 := H.dTh_evalB (fun _ h => h.2.2.1)
  have h2 := H.dTh_Di
  rw [dTh] at h1 h2
  rw [nZ, h1, h2, ← nZ, ← dTh]
  simp only [A21, A22, XZ, nZu, nZz, Du, Dz]
  ring

/-- `𝓛 N_R = (𝓛h) u + h 𝓛R` (product rule). -/
theorem Lt_NR : Lt ι (F.NR u z) = Lt ι (F.hN u z) * u + F.hN u z * LR ι u := by
  rw [NR, Lt, dS_mul _ _ H.ana_hN H.ana_u]; rfl

/-- `𝓛 N_z = (𝓛h) z + h 𝓛z` (product rule). -/
theorem Lt_NZ : Lt ι (F.NZ u z) = Lt ι (F.hN u z) * z + F.hN u z * Lz ι z := by
  rw [NZ, Lt, dS_mul _ _ H.ana_hN H.ana_z]; rfl

omit H in
/-- The torsion numerator in terms of the field and its partial derivatives. -/
theorem Pof_eq : F.Pof u z =
    (F.nR u z * F.Dof u z - F.Dof u z * (F.nRu u z * u + F.nRz u z * z) +
        F.nR u z * (F.Du u z * u + F.Dz u z * z)) * z -
      (F.nZ u z * F.Dof u z - F.Dof u z * (F.nZu u z * u + F.nZz u z * z) +
        F.nZ u z * (F.Du u z * u + F.Dz u z * z)) * u := by
  rfl

/-- **Torsion coordinate**: the `∂_θK`-coordinate of `𝓛N − DX·N` is the torsion `T`. -/
theorem torsion_coord :
    Wi u z * (F.YRt ι u z * z - F.YZt ι u z * u) = F.Tor ι u z := by
  simp only [YRt, YZt, Tor, Talg, NR, NZ, hN, A11, A12, A21, A22, XR, XZ]
  rw [H.LR_eq, H.Lz_eq, Pof_eq]
  simp only [XR, XZ]
  unit_closeS H

/-- **Divergence-free identity solved for `∂_φ D`**: `∂_φD = 3 n_R/R − ∂_u n_R − ∂_z n_z`. -/
theorem phiD_eq : phiDS (xB u z) F.Dp = 3 * F.nR u z * Ri u - F.nRu u z - F.nZz u z := by
  have hd := F.divFree u z H.good
  simp only [nR, nRu, nZz]
  linear_combination Ri u * hd -
    (phiDS (xB u z) F.Dp + pdS (xB u z) 0 F.nRp + pdS (xB u z) 1 F.nZp) * H.R_Ri

/-- `𝓛 (1 + u)⁻¹ = −R⁻² 𝓛R`. -/
theorem Lt_Ri : Lt ι (Ri u) = -(Ri u ^ 2 * LR ι u) := by
  rw [Lt, Ri, dS_inverse _ _ H.ana_R H.unit_R H.ana_Ri, dS_add _ _ Ana.one H.ana_u, dS_one,
    zero_add]; rfl

/-- **`𝓛w + w tr DX = (∇w · Ê)`** (the divergence-free identity at work). -/
theorem Ltw_trA :
    Lt ι (F.wD u z) = Ri u ^ 3 * (F.Du u z * F.EhR ι u z + F.Dz u z * F.EhZ ι u z) -
      3 * F.Dof u z * Ri u ^ 4 * F.EhR ι u z - F.wD u z * (F.A11 u z + F.A22 u z) := by
  have hpow : Lt ι (Ri u ^ 3) = ((2 + 1 : ℕ) : FA) * Ri u ^ 2 * Lt ι (Ri u) :=
    dS_pow _ _ H.anaRi 2
  rw [wD, Lt, dS_mul _ _ H.ana_D (H.anaRi.pow 3), ← Lt, ← Lt, hpow, H.Lt_Ri]
  have hD := H.Lt_evalB (ι := ι) (fun _ h => h.1)
  rw [← Dof] at hD
  rw [hD, H.phiD_eq, H.LR_eq, H.Lz_eq]
  simp only [A11, A22, XR, XZ, Du, Dz, nRu, nZz, nR, nZ]
  push_cast
  unit_closeS H

/-- `𝓛 h = −h² 𝓛(w W₀)` (from `w W₀ h = 1` by the product rule). -/
theorem Lt_hN : Lt ι (F.hN u z) = -(F.hN u z ^ 2 * Lt ι (F.wD u z * W0of u z)) := by
  have h1 : Lt ι (F.wD u z * W0of u z * F.hN u z) = 0 := by rw [H.wWh, Lt, dS_one]
  rw [Lt, dS_mul _ _ (H.ana_wD.mul H.ana_W) H.ana_hN, ← Lt, ← Lt] at h1
  linear_combination F.hN u z * h1 - Lt ι (F.hN u z) * H.wWh

/-- `𝓛 W₀` by the product rule. -/
theorem Lt_W : Lt ι (W0of u z) =
    Lt ι (Rt u) * z + Rt u * Lz ι z - (Lt ι (zt z) * u + zt z * LR ι u) := by
  change dS (ι : ℂ) 2 (Rt u * z - zt z * u) = _
  rw [dS_sub _ _ (H.ana_Rt.mul H.ana_z) (H.ana_zt.mul H.ana_u),
    dS_mul _ _ H.ana_Rt H.ana_z, dS_mul _ _ H.ana_zt H.ana_u]; rfl

/-- `𝓛 ∂_θ R = ∂_θ 𝓛 R`. -/
theorem Lt_Rt : Lt ι (Rt u) = dTh (LR ι u) := by
  rw [Lt, Rt, dTh, LR, Lt, dS_dS_comm _ _ _ _ H.ana_u]; rfl

/-- `𝓛 ∂_θ z = ∂_θ 𝓛 z`. -/
theorem Lt_zt : Lt ι (zt z) = dTh (Lz ι z) := by
  rw [Lt, zt, dTh, Lz, Lt, dS_dS_comm _ _ _ _ H.ana_z]; rfl

/-- **Second frame coordinate of `𝓛N − DX·N`**: it is `S`, linear in the error (approximate
reducibility; uses area preservation through `Ltw_trA`). -/
theorem S_coord :
    F.wD u z * (Rt u * F.YZt ι u z - zt z * F.YRt ι u z) = F.Scoef ι u z := by
  have hLwW : Lt ι (F.wD u z * W0of u z) =
      Lt ι (F.wD u z) * W0of u z + F.wD u z * Lt ι (W0of u z) := by
    rw [Lt, dS_mul _ _ H.ana_wD H.ana_W]; rfl
  simp only [YRt, YZt]
  rw [H.Lt_hN, hLwW, H.Lt_W, H.Lt_Rt, H.Lt_zt, H.dTh_LR, H.dTh_Lz, H.Ltw_trA, H.LR_eq, H.Lz_eq]
  simp only [Scoef, NR, NZ, hN, wD, A11, A12, A21, A22, XR, XZ, W0of]
  unit_closeS H

/-! ### The flux identity -/

/-- Analyticity: `ana_Pa`. -/
theorem ana_Pa : Ana (F.Pa u z) := H.ana_evalB (fun _ h => h.2.2.2.1)
/-- Analyticity: `ana_Pb`. -/
theorem ana_Pb : Ana (F.Pb u z) := H.ana_evalB (fun _ h => h.2.2.2.2.1)
/-- Analyticity: `ana_aF`. -/
theorem ana_aF : Ana (F.aF u z) := H.ana_Pa.mul H.anaRi
/-- Analyticity: `ana_bF`. -/
theorem ana_bF : Ana (F.bF u z) := H.ana_Pb.mul (H.anaRi.pow 2)
/-- Analyticity: `ana_dPh_u`. -/
theorem ana_dPh_u : Ana (dPh u) := H.ana_u.d 0 2
/-- Analyticity: `ana_dPh_z`. -/
theorem ana_dPh_z : Ana (dPh z) := H.ana_z.d 0 2

/-- `∂_θ R⁻¹ = −R⁻² ∂_θR` and `∂_φ R⁻¹ = −R⁻² ∂_φR`. -/
theorem d_Ri (a b : ℂ) : dS a b (Ri u) = -(Ri u ^ 2 * dS a b u) := by
  rw [Ri, dS_inverse _ _ H.ana_R H.unit_R H.ana_Ri, dS_add _ _ Ana.one H.ana_u, dS_one, zero_add]

/-- `∂ R⁻² = 2 R⁻¹ ∂ R⁻¹`. -/
theorem d_Ri2 (a b : ℂ) : dS a b (Ri u ^ 2) = 2 * Ri u * dS a b (Ri u) := by
  have := dS_pow a b H.anaRi 1
  rw [show (1 + 1 : ℕ) = 2 from rfl] at this
  rw [this]; push_cast; ring

/-- Flux identity (b) solved: `∂_φ P_a = n_z / R² + R ∂_u P_c`. -/
theorem phiPa_eq : phiDS (xB u z) F.Pap =
    F.nZ u z * Ri u ^ 2 + (1 + u) * pdS (xB u z) 0 F.Pcp := by
  have hb := F.flux_b u z H.good
  simp only [nZ]
  linear_combination Ri u ^ 2 * hb - (phiDS (xB u z) F.Pap - (1 + u) * pdS (xB u z) 0 F.Pcp) *
    ((1 + u) * Ri u + 1) * H.R_Ri

/-- Flux identity (c) solved: `∂_φ P_b = −n_R / R + R² ∂_z P_c`. -/
theorem phiPb_eq : phiDS (xB u z) F.Pbp =
    -(F.nR u z * Ri u) + (1 + u) ^ 2 * pdS (xB u z) 1 F.Pcp := by
  have hc := F.flux_c u z H.good
  simp only [nR]
  linear_combination Ri u * hc - (phiDS (xB u z) F.Pbp - (1 + u) ^ 2 * pdS (xB u z) 1 F.Pcp) *
    H.R_Ri

/-- Flux identity (a) solved: `∂_u P_b = (D + 2P_b + R² ∂_z P_a)/R`. -/
theorem pbu_eq : pdS (xB u z) 0 F.Pbp =
    (F.Dof u z + 2 * F.Pb u z + (1 + u) ^ 2 * pdS (xB u z) 1 F.Pap) * Ri u := by
  have ha := F.flux_a u z H.good
  simp only [Pb, Dof]
  linear_combination Ri u * ha - pdS (xB u z) 0 F.Pbp * H.R_Ri

/-- **Flux identity**: `η₂ = w (∂_θK × Ê) = ∂_θ B − ∂_φ A`, the exterior derivative of the
pulled-back primitive of the flux form. -/
theorem eta2_flux : F.eta2 ι u z = dTh (F.BF u z) - dPh (F.AF u z) := by
  have hcomm_u : dTh (dPh u) = dPh (Rt u) := by
    rw [dTh, dPh, Rt, dTh, dS_dS_comm _ _ _ _ H.ana_u]; rfl
  have hcomm_z : dTh (dPh z) = dPh (zt z) := by
    rw [dTh, dPh, zt, dTh, dS_dS_comm _ _ _ _ H.ana_z]; rfl
  have hPc : dTh (F.Pc u z) = pdS (xB u z) 0 F.Pcp * Rt u + pdS (xB u z) 1 F.Pcp * zt z :=
    H.dTh_evalB (fun _ h => h.2.2.2.2.2)
  have hBF : dTh (F.BF u z) = dTh (F.aF u z) * dPh u + F.aF u z * dTh (dPh u) +
      (dTh (F.bF u z) * dPh z + F.bF u z * dTh (dPh z)) + dTh (F.Pc u z) := by
    rw [BF, dTh, dS_add _ _ ((H.ana_aF.mul H.ana_dPh_u).add (H.ana_bF.mul H.ana_dPh_z))
      (show Ana (F.Pc u z) from H.ana_evalB (fun _ h => h.2.2.2.2.2)),
      dS_add _ _ (H.ana_aF.mul H.ana_dPh_u) (H.ana_bF.mul H.ana_dPh_z),
      dS_mul _ _ H.ana_aF H.ana_dPh_u, dS_mul _ _ H.ana_bF H.ana_dPh_z]; rfl
  have hAF : dPh (F.AF u z) = dPh (F.aF u z) * Rt u + F.aF u z * dPh (Rt u) +
      (dPh (F.bF u z) * zt z + F.bF u z * dPh (zt z)) := by
    rw [AF, dPh, dS_add _ _ (H.ana_aF.mul H.ana_Rt) (H.ana_bF.mul H.ana_zt),
      dS_mul _ _ H.ana_aF H.ana_Rt, dS_mul _ _ H.ana_bF H.ana_zt]; rfl
  have haθ : dTh (F.aF u z) = (pdS (xB u z) 0 F.Pap * Rt u + pdS (xB u z) 1 F.Pap * zt z) * Ri u +
      F.Pa u z * (-(Ri u ^ 2 * Rt u)) := by
    have h := H.dTh_evalB (fun _ h => h.2.2.2.1)
    simp only [dTh] at h
    rw [aF, dTh, dS_mul _ _ H.ana_Pa H.anaRi, Pa, h, H.d_Ri]; rfl
  have haφ : dPh (F.aF u z) = (pdS (xB u z) 0 F.Pap * dPh u + pdS (xB u z) 1 F.Pap * dPh z +
      phiDS (xB u z) F.Pap) * Ri u + F.Pa u z * (-(Ri u ^ 2 * dPh u)) := by
    have h := H.dPh_evalB (fun _ h => h.2.2.2.1)
    simp only [dPh] at h
    rw [aF, dPh, dS_mul _ _ H.ana_Pa H.anaRi, Pa, h, H.d_Ri]; rfl
  have hbθ : dTh (F.bF u z) =
      (pdS (xB u z) 0 F.Pbp * Rt u + pdS (xB u z) 1 F.Pbp * zt z) * Ri u ^ 2 +
      F.Pb u z * (2 * Ri u * (-(Ri u ^ 2 * Rt u))) := by
    have h := H.dTh_evalB (fun _ h => h.2.2.2.2.1)
    simp only [dTh] at h
    rw [bF, dTh, dS_mul _ _ H.ana_Pb (H.anaRi.pow 2), Pb, h, H.d_Ri2, H.d_Ri]; rfl
  have hbφ : dPh (F.bF u z) = (pdS (xB u z) 0 F.Pbp * dPh u + pdS (xB u z) 1 F.Pbp * dPh z +
      phiDS (xB u z) F.Pbp) * Ri u ^ 2 + F.Pb u z * (2 * Ri u * (-(Ri u ^ 2 * dPh u))) := by
    have h := H.dPh_evalB (fun _ h => h.2.2.2.2.1)
    simp only [dPh] at h
    rw [bF, dPh, dS_mul _ _ H.ana_Pb (H.anaRi.pow 2), Pb, h, H.d_Ri2, H.d_Ri]; rfl
  have hER : F.EhR ι u z = (ι : ℂ) • Rt u + dPh u - F.XR u z := by
    have h := Lt_eq ι H.ana_u
    rw [show Rt u = dTh u from rfl, ← h, ← LR, H.LR_eq]; ring
  have hEZ : F.EhZ ι u z = (ι : ℂ) • zt z + dPh z - F.XZ u z := by
    have h := Lt_eq ι H.ana_z
    rw [show zt z = dTh z from rfl, ← h, ← Lz, H.Lz_eq]; ring
  rw [hBF, hPc, hAF, haθ, haφ, hbθ, hbφ, hcomm_u, hcomm_z, H.phiPa_eq, H.phiPb_eq, H.pbu_eq]
  simp only [eta2, wD, hER, hEZ, XR, XZ, Algebra.smul_def]
  unit_closeS H

/-- **`⟨η₂⟩ = 0` exactly** (zero flux through the torus). -/
theorem avg_eta2 : avg (F.eta2 ι u z) = 0 := by
  rw [H.eta2_flux, avg_sub, dTh, dPh, avg_dS, avg_dS, sub_zero]

/-! ### The Newton correction -/

/-- `𝓛N − DX·N = T ∂_θK + S N` (`R` component). -/
theorem YR_eq : F.YRt ι u z = F.Tor ι u z * Rt u + F.Scoef ι u z * F.NR u z := by
  have h := H.frame_decomp_R (F.YRt ι u z) (F.YZt ι u z)
  rw [H.torsion_coord, H.S_coord] at h
  exact h

/-- `𝓛N − DX·N = T ∂_θK + S N` (`z` component). -/
theorem YZ_eq : F.YZt ι u z = F.Tor ι u z * zt z + F.Scoef ι u z * F.NZ u z := by
  have h := H.frame_decomp_Z (F.YRt ι u z) (F.YZt ι u z)
  rw [H.torsion_coord, H.S_coord] at h
  exact h

/-- **The linearised equation up to a quadratic remainder.** If `𝓛ξ₂ = −η₂` and
`𝓛ξ₁ = −(η₁ + T ξ₂)`, then `ΔK = ξ₁ ∂_θK + ξ₂ N` satisfies
`𝓛ΔK − DX·ΔK + Ê = ξ₂ S N + ξ₁ ∂_θÊ` (`R` component). -/
theorem linear_residual_R {ξ1 ξ2 : FA} (h1 : Ana ξ1) (h2 : Ana ξ2)
    (hL1 : Lt ι ξ1 = -(F.eta1 ι u z + F.Tor ι u z * ξ2)) (hL2 : Lt ι ξ2 = -F.eta2 ι u z) :
    Lt ι (ξ1 * Rt u + ξ2 * F.NR u z) -
        (F.A11 u z * (ξ1 * Rt u + ξ2 * F.NR u z) + F.A12 u z * (ξ1 * zt z + ξ2 * F.NZ u z)) +
          F.EhR ι u z = F.Scoef ι u z * ξ2 * F.NR u z + ξ1 * dTh (F.EhR ι u z) := by
  have hNR : Ana (F.NR u z) := H.ana_hN.mul H.ana_u
  rw [Lt, dS_add _ _ (h1.mul H.ana_Rt) (h2.mul hNR), dS_mul _ _ h1 H.ana_Rt,
    dS_mul _ _ h2 hNR]
  rw [show dS (ι : ℂ) 2 ξ1 = Lt ι ξ1 from rfl, show dS (ι : ℂ) 2 ξ2 = Lt ι ξ2 from rfl,
    show dS (ι : ℂ) 2 (Rt u) = Lt ι (Rt u) from rfl,
    show dS (ι : ℂ) 2 (F.NR u z) = Lt ι (F.NR u z) from rfl]
  rw [hL1, hL2, H.Lt_Rt, H.dTh_LR, H.Lt_NR]
  have hY := H.YR_eq (ι := ι)
  have hE := (H.Eh_decomp (ι := ι)).1
  simp only [YRt] at hY
  linear_combination ξ2 * hY + hE

/-- **The linearised equation up to a quadratic remainder** (`z` component). -/
theorem linear_residual_Z {ξ1 ξ2 : FA} (h1 : Ana ξ1) (h2 : Ana ξ2)
    (hL1 : Lt ι ξ1 = -(F.eta1 ι u z + F.Tor ι u z * ξ2)) (hL2 : Lt ι ξ2 = -F.eta2 ι u z) :
    Lt ι (ξ1 * zt z + ξ2 * F.NZ u z) -
        (F.A21 u z * (ξ1 * Rt u + ξ2 * F.NR u z) + F.A22 u z * (ξ1 * zt z + ξ2 * F.NZ u z)) +
          F.EhZ ι u z = F.Scoef ι u z * ξ2 * F.NZ u z + ξ1 * dTh (F.EhZ ι u z) := by
  have hNZ : Ana (F.NZ u z) := H.ana_hN.mul H.ana_z
  rw [Lt, dS_add _ _ (h1.mul H.ana_zt) (h2.mul hNZ), dS_mul _ _ h1 H.ana_zt,
    dS_mul _ _ h2 hNZ]
  rw [show dS (ι : ℂ) 2 ξ1 = Lt ι ξ1 from rfl, show dS (ι : ℂ) 2 ξ2 = Lt ι ξ2 from rfl,
    show dS (ι : ℂ) 2 (zt z) = Lt ι (zt z) from rfl,
    show dS (ι : ℂ) 2 (F.NZ u z) = Lt ι (F.NZ u z) from rfl]
  rw [hL1, hL2, H.Lt_zt, H.dTh_Lz, H.Lt_NZ]
  have hY := H.YZ_eq (ι := ι)
  have hE := (H.Eh_decomp (ι := ι)).2
  simp only [YZt] at hY
  linear_combination ξ2 * hY + hE

/-- The perturbed residual variables. -/
theorem xK_add {ΔR ΔZ : FA} (hR : Ana ΔR) (hZ : Ana ΔZ) :
    xK ι (u + ΔR) (z + ΔZ) = xK ι u z + hDel ι ΔR ΔZ := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp [xK, hDel]
  · simp [xK, hDel]
  · simp only [xK, hDel, Pi.add_apply]
    exact dS_add _ _ H.ana_u hR
  · simp only [xK, hDel, Pi.add_apply]
    exact dS_add _ _ H.ana_z hZ

omit H in
/-- The derivative of the `R`-residual along the perturbation. -/
theorem deriv_resR (ΔR ΔZ : FA) :
    PolyExprS.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resRp =
      (ΔR * F.Du u z + ΔZ * F.Dz u z) * LR ι u + F.Dof u z * Lt ι ΔR -
        (ΔR * F.nRu u z + ΔZ * F.nRz u z) := by
  simp only [resRp, PolyExprS.deriv, deriv_eq_sum_pdS _ _ F.Dp, deriv_eq_sum_pdS _ _ F.nRp,
    Fin.sum_univ_six]
  rw [pdS_noW (i := 4) (by norm_num) F.Dp F.noW_Dp, pdS_noW (i := 5) (by norm_num) F.Dp F.noW_Dp,
    pdS_noW (i := 4) (by norm_num) F.nRp F.noW_nRp,
    pdS_noW (i := 5) (by norm_num) F.nRp F.noW_nRp, pdS_xK_xB ι u z 0 F.noW_Dp,
    pdS_xK_xB ι u z 1 F.noW_Dp,
    pdS_xK_xB ι u z 0 F.noW_nRp, pdS_xK_xB ι u z 1 F.noW_nRp, eval_xK_xB_S ι u z F.noW_Dp]
  simp [hDel, xK, Du, Dz, nRu, nRz, LR, Dof, PolyExprS.eval]

omit H in
/-- The derivative of the `z`-residual along the perturbation. -/
theorem deriv_resZ (ΔR ΔZ : FA) :
    PolyExprS.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resZp =
      (ΔR * F.Du u z + ΔZ * F.Dz u z) * Lz ι z + F.Dof u z * Lt ι ΔZ -
        (ΔR * F.nZu u z + ΔZ * F.nZz u z) := by
  simp only [resZp, PolyExprS.deriv, deriv_eq_sum_pdS _ _ F.Dp, deriv_eq_sum_pdS _ _ F.nZp,
    Fin.sum_univ_six]
  rw [pdS_noW (i := 4) (by norm_num) F.Dp F.noW_Dp, pdS_noW (i := 5) (by norm_num) F.Dp F.noW_Dp,
    pdS_noW (i := 4) (by norm_num) F.nZp F.noW_nZp,
    pdS_noW (i := 5) (by norm_num) F.nZp F.noW_nZp, pdS_xK_xB ι u z 0 F.noW_Dp,
    pdS_xK_xB ι u z 1 F.noW_Dp,
    pdS_xK_xB ι u z 0 F.noW_nZp, pdS_xK_xB ι u z 1 F.noW_nZp, eval_xK_xB_S ι u z F.noW_Dp]
  simp [hDel, xK, Du, Dz, nZu, nZz, Lz, Dof, PolyExprS.eval]

/-- **The new residual** (`R` component):
`E_R(K + ΔK) = D (𝓛ΔR − (DX·ΔK)_R + Ê_R) + (∇D·ΔK) Ê_R + Q_R`. -/
theorem newton_error_R {ΔR ΔZ : FA} (hR : Ana ΔR) (hZ : Ana ΔZ) :
    F.resR ι (u + ΔR) (z + ΔZ) =
      F.Dof u z * (Lt ι ΔR - (F.A11 u z * ΔR + F.A12 u z * ΔZ) + F.EhR ι u z) +
        (F.Du u z * ΔR + F.Dz u z * ΔZ) * F.EhR ι u z + F.QR ι u z ΔR ΔZ := by
  have e1 : F.resR ι (u + ΔR) (z + ΔZ) =
      F.resR ι u z + PolyExprS.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resRp + F.QR ι u z ΔR ΔZ := by
    rw [resR, H.xK_add hR hZ, QR, resR]; ring
  rw [e1, deriv_resR, H.LR_eq]
  simp only [EhR, A11, A12, XR, Du, Dz, nRu, nRz, nR]
  unit_closeS H

/-- **The new residual** (`z` component). -/
theorem newton_error_Z {ΔR ΔZ : FA} (hR : Ana ΔR) (hZ : Ana ΔZ) :
    F.resZ ι (u + ΔR) (z + ΔZ) =
      F.Dof u z * (Lt ι ΔZ - (F.A21 u z * ΔR + F.A22 u z * ΔZ) + F.EhZ ι u z) +
        (F.Du u z * ΔR + F.Dz u z * ΔZ) * F.EhZ ι u z + F.QZ ι u z ΔR ΔZ := by
  have e1 : F.resZ ι (u + ΔR) (z + ΔZ) =
      F.resZ ι u z + PolyExprS.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resZp + F.QZ ι u z ΔR ΔZ := by
    rw [resZ, H.xK_add hR hZ, QZ, resZ]; ring
  rw [e1, deriv_resZ, H.Lz_eq]
  simp only [EhZ, A21, A22, XZ, Du, Dz, nZu, nZz, nZ]
  unit_closeS H

end FrameHyp

end FlowFieldS

end PlasmaLean.Design.KamNewton
