/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowFieldG
public import PlasmaLean.Design.KamFlowFrame

/-!
# The symplectic frame for a generalised flow field (moving centre, `R₀`, exponent `p`)

The frame of `Design/KamFlowFrame` for a field `F : FlowFieldG` (`Design/KamFlowFieldG`):
`R = R₀ + u` (`F.R`), the area density `w = D/R^p`, the flux primitive
`α = (P_a/R^{k_a}) dR + (P_b/R^{k_b}) dz`, and the frame vector `V₀ = K − A(φ)` about the moving
centre `A` (`F.V0R`, `F.V0Z`), with `W₀ = ∂_θK × V₀` (`F.W0`).

**Objects.** As in `KamFlowFrame`: `Ê = E/D`, `X = n/D`, `A = DX`, `w = D R^{−p}`,
`N = h V₀` with `h = R^p/(D W₀)`, `η₁ = W₀⁻¹ (Ê × V₀)`, `η₂ = w (∂_θK × Ê)`, the torsion
`T = T₀ + R^p D⁻¹ W₀⁻² (Ê × V₀)` with `T₀ = R^p P/(D³W₀²)`, and
`S = −(∇D·Ê)/D + p Ê_R/R − (∂_θÊ × V₀)/W₀`.

**Identities** (the same statements as in `KamFlowFrame`, now with the centre and the exponent):
* `frame_decomp_R/Z`, `Eh_decomp`, `frame_det` (`w (∂_θK × N) = 1`);
* `torsion_coord`: the `∂_θK`-coordinate of `𝓛N − DX·N` is `T` — here `𝓛N = (𝓛h)V₀ + h(𝓛K − A')`
  and the centre's velocity `A'` enters through the torsion numerator `P` (`Pof_eq`);
* `S_coord`: the second coordinate is `S`; the centre's velocity cancels (it is the same for
  every frame), and the divergence-free identity enters with the exponent `p` (`Ltw_trA`);
* `eta2_flux`, `avg_eta2`: `η₂ = ∂_θB − ∂_φA` and `⟨η₂⟩ = 0` (independent of the frame);
* `linear_residual_R/Z`, `newton_error_R/Z`: the Newton step's linear and quadratic parts.

**Sanity.** `FlowField.toG_hN`, `toG_Tor`, `toG_Scoef`, `toG_eta1`, `toG_eta2`: for
`F.toG` (`R₀ = 1`, `p = 3`, centre `0`) the frame objects are those of `KamFlowFrame`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PolyExpr Complex WEll1Z2

/-- `dS` of a power of an inverse: `∂ (x⁻¹)^k = −k (x⁻¹)^{k+1} ∂x` (any `k`, including `0`). -/
theorem dS_inv_pow (a b : ℂ) {x : FA} (hx : Ana x) (hu : IsUnit x) (hi : Ana (Ring.inverse x)) :
    ∀ k : ℕ, dS a b (Ring.inverse x ^ k) = -((k : FA) * Ring.inverse x ^ (k + 1) * dS a b x)
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, dS_mul _ _ (hi.pow k) hi, dS_inv_pow a b hx hu hi k, dS_inverse _ _ hx hu hi]
    push_cast; ring

namespace FlowFieldG

variable (F : FlowFieldG)

section Frame

variable (ι : ℝ) (u z : FA)

/-- `D⁻¹`. -/
def Di : FA := Ring.inverse (F.Dof u z)
/-- `W₀⁻¹`. -/
def Wi : FA := Ring.inverse (F.W0 u z)
/-- `n_R`. -/
def nR : FA := PolyExpr.eval (xB u z) F.nRp
/-- `n_z`. -/
def nZ : FA := PolyExpr.eval (xB u z) F.nZp
/-- `∂_u D`. -/
def Du : FA := pd (xB u z) 0 F.Dp
/-- `∂_z D`. -/
def Dz : FA := pd (xB u z) 1 F.Dp
/-- `∂_u n_R`. -/
def nRu : FA := pd (xB u z) 0 F.nRp
/-- `∂_z n_R`. -/
def nRz : FA := pd (xB u z) 1 F.nRp
/-- `∂_u n_z`. -/
def nZu : FA := pd (xB u z) 0 F.nZp
/-- `∂_z n_z`. -/
def nZz : FA := pd (xB u z) 1 F.nZp
/-- The centre velocity `a_R'`. -/
def ApR : FA := cenD F.aRp
/-- The centre velocity `a_z'`. -/
def ApZ : FA := cenD F.aZp
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
/-- The area density `w = D/R^p`. -/
def wD : FA := F.Dof u z * F.Ri u ^ F.p
/-- `h = R^p/(D W₀) = 1/(w W₀)`. -/
def hN : FA := F.R u ^ F.p * F.Di u z * F.Wi u z
/-- `N_R = h V₀_R`. -/
def NR : FA := F.hN u z * F.V0R u
/-- `N_z = h V₀_z`. -/
def NZ : FA := F.hN u z * F.V0Z z
/-- The first frame coordinate of the error, `η₁ = W₀⁻¹ (Ê × V₀)`. -/
def eta1 : FA := F.Wi u z * (F.V0Z z * F.EhR ι u z - F.V0R u * F.EhZ ι u z)
/-- The second frame coordinate of the error, `η₂ = w (∂_θK × Ê)`. -/
def eta2 : FA := F.wD u z * (Rt u * F.EhZ ι u z - zt z * F.EhR ι u z)
/-- The algebraic torsion density `T₀ = R^p P / (D³ W₀²)`. -/
def Talg : FA := F.R u ^ F.p * F.Di u z ^ 3 * F.Wi u z ^ 2 * F.Pof u z
/-- The torsion `T = T₀ + R^p D⁻¹ W₀⁻² (Ê × V₀)`. -/
def Tor : FA :=
  F.Talg u z + F.R u ^ F.p * F.Di u z * F.Wi u z ^ 2 *
    (F.EhR ι u z * F.V0Z z - F.EhZ ι u z * F.V0R u)
/-- The remainder coefficient `S = −(∇D·Ê)/D + p Ê_R/R − (∂_θÊ × V₀)/W₀`. -/
def Scoef : FA :=
  -((F.Du u z * F.EhR ι u z + F.Dz u z * F.EhZ ι u z) * F.Di u z) +
    (F.p : FA) * F.Ri u * F.EhR ι u z -
    F.Wi u z * (dTh (F.EhR ι u z) * F.V0Z z - dTh (F.EhZ ι u z) * F.V0R u)

/-- `R`-component of `𝓛N − DX·N` (`𝓛N = (𝓛h) V₀ + h (𝓛K − A')`, product rule). -/
def YRt : FA :=
  Lt ι (F.hN u z) * F.V0R u + F.hN u z * (LR ι u - F.ApR) -
    (F.A11 u z * F.NR u z + F.A12 u z * F.NZ u z)
/-- `z`-component of `𝓛N − DX·N`. -/
def YZt : FA :=
  Lt ι (F.hN u z) * F.V0Z z + F.hN u z * (Lz ι z - F.ApZ) -
    (F.A21 u z * F.NR u z + F.A22 u z * F.NZ u z)
/-- `P_a(K)`. -/
def Pa : FA := PolyExpr.eval (xB u z) F.Pap
/-- `P_b(K)`. -/
def Pb : FA := PolyExpr.eval (xB u z) F.Pbp
/-- The flux primitive coefficient `a = P_a / R^{k_a}`. -/
def aF : FA := F.Pa u z * F.Ri u ^ F.ka
/-- The flux primitive coefficient `b = P_b / R^{k_b}`. -/
def bF : FA := F.Pb u z * F.Ri u ^ F.kb
/-- The `dθ`-component `A = a ∂_θR + b ∂_θz` of the pulled-back primitive. -/
def AF : FA := F.aF u z * Rt u + F.bF u z * zt z
/-- The `dφ`-component `B = a ∂_φR + b ∂_φz` of the pulled-back primitive. -/
def BF : FA := F.aF u z * dPh u + F.bF u z * dPh z

end Frame

/-- The Taylor remainder of the `R`-residual. -/
def QR (ι : ℝ) (u z ΔR ΔZ : FA) : FA :=
  PolyExpr.eval (xK ι u z + hDel ι ΔR ΔZ) F.resRp - PolyExpr.eval (xK ι u z) F.resRp -
    PolyExpr.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resRp

/-- The Taylor remainder of the `z`-residual. -/
def QZ (ι : ℝ) (u z ΔR ΔZ : FA) : FA :=
  PolyExpr.eval (xK ι u z + hDel ι ΔR ΔZ) F.resZp - PolyExpr.eval (xK ι u z) F.resZp -
    PolyExpr.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resZp

/-- Standing hypotheses of the frame: analytic torus, invertible `D`, `R`, `W₀` with analytic
inverses. -/
structure FrameHyp (u z : FA) : Prop where
  /-- `u = R − R₀` is analytic. -/
  ana_u : Ana u
  /-- `z` is analytic. -/
  ana_z : Ana z
  /-- `D` is invertible. -/
  unit_D : IsUnit (F.Dof u z)
  /-- `R` is invertible. -/
  unit_R : IsUnit (F.R u)
  /-- `W₀` is invertible. -/
  unit_W : IsUnit (F.W0 u z)
  /-- `D⁻¹` is analytic. -/
  ana_Di : Ana (Ring.inverse (F.Dof u z))
  /-- `R⁻¹` is analytic. -/
  ana_Ri : Ana (F.Ri u)
  /-- `W₀⁻¹` is analytic. -/
  ana_Wi : Ana (Ring.inverse (F.W0 u z))

namespace FrameHyp

variable {F : FlowFieldG} {ι : ℝ} {u z : FA} (H : F.FrameHyp u z)
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

/-- Polynomials of the torus are analytic. -/
theorem ana_evalB (e : PolyExpr ℂ (Fin 6)) : Ana (PolyExpr.eval (xB u z) e) := Ana.eval H.ana_xB e

/-- Partial derivatives of polynomials of the torus are analytic. -/
theorem ana_pdB (i : Fin 6) (e : PolyExpr ℂ (Fin 6)) : Ana (pd (xB u z) i e) := by
  unfold pd
  induction e with
  | const c => exact Ana.zero
  | var j => by_cases h : j = i <;> simp [PolyExpr.deriv, h, Ana.one, Ana.zero]
  | add p q hp hq => exact hp.add hq
  | sub p q hp hq => exact hp.sub hq
  | mul p q hp hq => exact (hp.mul (H.ana_evalB q)).add ((H.ana_evalB p).mul hq)

/-- Chain rule for polynomials of the torus (any multiplier). -/
theorem dS_evalB (a b : ℂ) (e : PolyExpr ℂ (Fin 6)) :
    dS a b (PolyExpr.eval (xB u z) e) =
      pd (xB u z) 0 e * dS a b u + pd (xB u z) 1 e * dS a b z +
        pd (xB u z) 2 e * dS a b cS + pd (xB u z) 3 e * dS a b sS := by
  rw [dS_eval a b H.ana_xB, deriv_eq_sum, Fin.sum_univ_six]
  have h4 : xB u z 4 = 0 := rfl
  have h5 : xB u z 5 = 0 := rfl
  rw [h4, h5, dS_zero]
  simp only [xB]
  simp only [Matrix.cons_val, Fin.isValue]
  ring

/-- `∂_θ` of a polynomial of the torus. -/
theorem dTh_evalB (e : PolyExpr ℂ (Fin 6)) :
    dTh (PolyExpr.eval (xB u z) e) = pd (xB u z) 0 e * Rt u + pd (xB u z) 1 e * zt z := by
  have := H.dS_evalB 1 0 e
  rw [dTh, this, show dS 1 0 cS = 0 from dTh_cS, show dS 1 0 sS = 0 from dTh_sS]
  simp only [mul_zero, add_zero]; rfl

/-- `𝓛` of a polynomial of the torus: `∇P·𝓛K + ∂_φP`. -/
theorem Lt_evalB (e : PolyExpr ℂ (Fin 6)) :
    Lt ι (PolyExpr.eval (xB u z) e) =
      pd (xB u z) 0 e * LR ι u + pd (xB u z) 1 e * Lz ι z + phiD (xB u z) e := by
  have := H.dS_evalB (ι : ℂ) 2 e
  rw [Lt, this, show dS ι 2 cS = Lt ι cS from rfl, show dS ι 2 sS = Lt ι sS from rfl, Lt_cS,
    Lt_sS, two_smul_eq, two_smul_eq]
  simp only [LR, Lz, Lt, phiD, xB, Matrix.cons_val, Fin.isValue]
  ring

/-- `∂_φ` of a polynomial of the torus. -/
theorem dPh_evalB (e : PolyExpr ℂ (Fin 6)) :
    dPh (PolyExpr.eval (xB u z) e) =
      pd (xB u z) 0 e * dPh u + pd (xB u z) 1 e * dPh z + phiD (xB u z) e := by
  have := H.dS_evalB 0 2 e
  rw [dPh, this, show dS 0 2 cS = dPh cS from rfl, show dS 0 2 sS = dPh sS from rfl, dPh_cS,
    dPh_sS, two_smul_eq, two_smul_eq]
  simp only [dPh, phiD, xB, Matrix.cons_val, Fin.isValue]
  ring

/-! ### Units and pointwise evaluation -/

/-- `D D⁻¹ = 1`. -/
theorem D_Di : F.Dof u z * F.Di u z = 1 := Ring.mul_inverse_cancel _ H.unit_D
/-- `R R⁻¹ = 1`. -/
theorem R_Ri : F.R u * F.Ri u = 1 := Ring.mul_inverse_cancel _ H.unit_R
/-- `W₀ W₀⁻¹ = 1`. -/
theorem W_Wi : F.W0 u z * F.Wi u z = 1 := Ring.mul_inverse_cancel _ H.unit_W

/-- `D ≠ 0` pointwise. -/
theorem eval_D_ne (θ ψ : ℝ) : eval (F.Dof u z) θ ψ ≠ 0 := eval_ne_zero_of_unit H.unit_D θ ψ
/-- `R ≠ 0` pointwise. -/
theorem eval_R_ne (θ ψ : ℝ) : eval (F.R u) θ ψ ≠ 0 := eval_ne_zero_of_unit H.unit_R θ ψ
/-- `W₀ ≠ 0` pointwise. -/
theorem eval_W_ne (θ ψ : ℝ) :
    eval (dTh u) θ ψ * eval (F.V0Z z) θ ψ - eval (dTh z) θ ψ * eval (F.V0R u) θ ψ ≠ 0 := by
  have := eval_ne_zero_of_unit H.unit_W θ ψ
  rwa [W0, eval_sub', eval_mul, eval_mul] at this

/-- `W₀ ≠ 0` pointwise (another ordering of the factors). -/
theorem eval_W_ne' (θ ψ : ℝ) :
    eval (dTh u) θ ψ * eval (F.V0Z z) θ ψ - eval (F.V0R u) θ ψ * eval (dTh z) θ ψ ≠ 0 := by
  rw [mul_comm (eval (F.V0R u) θ ψ)]; exact H.eval_W_ne θ ψ
/-- `W₀ ≠ 0` pointwise (another ordering of the factors). -/
theorem eval_W_ne'' (θ ψ : ℝ) :
    eval (F.V0Z z) θ ψ * eval (dTh u) θ ψ - eval (F.V0R u) θ ψ * eval (dTh z) θ ψ ≠ 0 := by
  rw [mul_comm (eval (F.V0R u) θ ψ), mul_comm (eval (F.V0Z z) θ ψ)]; exact H.eval_W_ne θ ψ

/-- `D⁻¹` pointwise. -/
theorem eval_Di (θ ψ : ℝ) : eval (F.Di u z) θ ψ = (eval (F.Dof u z) θ ψ)⁻¹ :=
  eval_inverse H.unit_D θ ψ
/-- `R⁻¹` pointwise. -/
theorem eval_Ri (θ ψ : ℝ) : eval (F.Ri u) θ ψ = (eval (F.R u) θ ψ)⁻¹ :=
  eval_inverse H.unit_R θ ψ
/-- `W₀⁻¹` pointwise. -/
theorem eval_Wi (θ ψ : ℝ) :
    eval (F.Wi u z) θ ψ =
      (eval (dTh u) θ ψ * eval (F.V0Z z) θ ψ - eval (dTh z) θ ψ * eval (F.V0R u) θ ψ)⁻¹ := by
  rw [Wi, eval_inverse H.unit_W, W0, eval_sub', eval_mul, eval_mul]

/-! ### Analyticity of the frame objects -/

/-- Analyticity: `anaDi`. -/
theorem anaDi : Ana (F.Di u z) := H.ana_Di
/-- Analyticity: `anaRi`. -/
theorem anaRi : Ana (F.Ri u) := H.ana_Ri
/-- Analyticity: `anaWi`. -/
theorem anaWi : Ana (F.Wi u z) := H.ana_Wi
/-- Analyticity: `ana_Rt`. -/
theorem ana_Rt : Ana (Rt u) := H.ana_u.d 1 0
/-- Analyticity: `ana_zt`. -/
theorem ana_zt : Ana (zt z) := H.ana_z.d 1 0
/-- Analyticity: `ana_LR`. -/
theorem ana_LR : Ana (LR ι u) := H.ana_u.d ι 2
/-- Analyticity: `ana_Lz`. -/
theorem ana_Lz : Ana (Lz ι z) := H.ana_z.d ι 2
/-- Analyticity: `ana_D`. -/
theorem ana_D : Ana (F.Dof u z) := H.ana_evalB F.Dp
/-- Analyticity: `ana_nR`. -/
theorem ana_nR : Ana (F.nR u z) := H.ana_evalB F.nRp
/-- Analyticity: `ana_nZ`. -/
theorem ana_nZ : Ana (F.nZ u z) := H.ana_evalB F.nZp
/-- Analyticity: `ana_resR`. -/
theorem ana_resR : Ana (F.resR ι u z) := Ana.eval H.ana_xK F.resRp
/-- Analyticity: `ana_resZ`. -/
theorem ana_resZ : Ana (F.resZ ι u z) := Ana.eval H.ana_xK F.resZp
/-- Analyticity: `ana_EhR`. -/
theorem ana_EhR : Ana (F.EhR ι u z) := H.ana_resR.mul H.anaDi
/-- Analyticity: `ana_EhZ`. -/
theorem ana_EhZ : Ana (F.EhZ ι u z) := H.ana_resZ.mul H.anaDi
/-- Analyticity: `ana_XR`. -/
theorem ana_XR : Ana (F.XR u z) := H.ana_nR.mul H.anaDi
/-- Analyticity: `ana_XZ`. -/
theorem ana_XZ : Ana (F.XZ u z) := H.ana_nZ.mul H.anaDi
/-- Analyticity: `ana_R`. -/
theorem ana_R : Ana (F.R u) := ana_RofG _ H.ana_u
/-- Analyticity: `ana_V0R`. -/
theorem ana_V0R : Ana (F.V0R u) := F.ana_V0R H.ana_u
/-- Analyticity: `ana_V0Z`. -/
theorem ana_V0Z : Ana (F.V0Z z) := F.ana_V0Z H.ana_z
/-- Analyticity: `ana_hN`. -/
theorem ana_hN : Ana (F.hN u z) := ((H.ana_R.pow _).mul H.anaDi).mul H.anaWi
/-- Analyticity: `ana_wD`. -/
theorem ana_wD : Ana (F.wD u z) := H.ana_D.mul (H.anaRi.pow _)
/-- Analyticity: `ana_W`. -/
theorem ana_W : Ana (F.W0 u z) := (H.ana_Rt.mul H.ana_V0Z).sub (H.ana_zt.mul H.ana_V0R)

/-- Close an identity with inverses pointwise (`field_simp`); `R`, `V₀_R`, `V₀_z` are atoms. -/
macro "unit_closeG" H:term : tactic =>
  `(tactic| (try simp only [Rt, zt]
             refine ext_eval fun θ ψ => ?_
             have hD := ($H).eval_D_ne θ ψ
             have hR := ($H).eval_R_ne θ ψ
             have hW := ($H).eval_W_ne θ ψ
             have hW' := ($H).eval_W_ne' θ ψ
             have hW'' := ($H).eval_W_ne'' θ ψ
             eval_push
             simp only [($H).eval_Di, ($H).eval_Ri, ($H).eval_Wi, inv_pow]
             first | (field_simp; done) | (field_simp; ring)))

/-- `w h = W₀⁻¹`. -/
theorem wD_hN : F.wD u z * F.hN u z = F.Wi u z := by
  simp only [wD, hN]; unit_closeG H

/-- `h W₀ = R^p D⁻¹`. -/
theorem hN_W : F.hN u z * F.W0 u z = F.R u ^ F.p * F.Di u z := by
  simp only [hN, W0]; unit_closeG H

/-- `w W₀ h = 1`. -/
theorem wWh : F.wD u z * F.W0 u z * F.hN u z = 1 := by
  simp only [wD, hN, W0]; unit_closeG H

/-- **Sanity: the frame is symplectic**, `w (∂_θK × N) = 1`. -/
theorem frame_det : F.wD u z * (Rt u * F.NZ u z - zt z * F.NR u z) = 1 := by
  simp only [wD, NZ, NR, hN]; unit_closeG H

/-- **`𝓛K = X + Ê`** (`R` component). -/
theorem LR_eq : LR ι u = F.XR u z + F.EhR ι u z := by
  have e := F.resR_eq ι u z
  simp only [XR, EhR, nR, LR]
  rw [e]; unit_closeG H

/-- **`𝓛K = X + Ê`** (`z` component). -/
theorem Lz_eq : Lz ι z = F.XZ u z + F.EhZ ι u z := by
  have e := F.resZ_eq ι u z
  simp only [XZ, EhZ, nZ, Lz]
  rw [e]; unit_closeG H

/-- **Frame decomposition**: `Y = (W₀⁻¹ Y × V₀) ∂_θK + (w ∂_θK × Y) N` (`R` component). -/
theorem frame_decomp_R (YR YZ : FA) :
    YR = F.Wi u z * (YR * F.V0Z z - YZ * F.V0R u) * Rt u +
      F.wD u z * (Rt u * YZ - zt z * YR) * F.NR u z := by
  simp only [wD, NR, hN]; unit_closeG H

/-- **Frame decomposition** (`z` component). -/
theorem frame_decomp_Z (YR YZ : FA) :
    YZ = F.Wi u z * (YR * F.V0Z z - YZ * F.V0R u) * zt z +
      F.wD u z * (Rt u * YZ - zt z * YR) * F.NZ u z := by
  simp only [wD, NZ, hN]; unit_closeG H

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
  have := H.dTh_evalB F.Dp
  rw [dTh] at this
  rw [Dof, this]; rfl

/-- **`𝓛 ∂_θK = DX·∂_θK + ∂_θÊ`** (`R` component, as `∂_θ 𝓛R`). -/
theorem dTh_LR :
    dTh (LR ι u) = F.A11 u z * Rt u + F.A12 u z * zt z + dTh (F.EhR ι u z) := by
  rw [H.LR_eq, dTh, dS_add 1 0 H.ana_XR H.ana_EhR, XR, dS_mul 1 0 H.ana_nR H.anaDi]
  have h1 := H.dTh_evalB F.nRp
  have h2 := H.dTh_Di
  rw [dTh] at h1 h2
  rw [nR, h1, h2, ← nR, ← dTh]
  simp only [A11, A12, XR, nRu, nRz, Du, Dz]
  ring

/-- **`𝓛 ∂_θK = DX·∂_θK + ∂_θÊ`** (`z` component). -/
theorem dTh_Lz :
    dTh (Lz ι z) = F.A21 u z * Rt u + F.A22 u z * zt z + dTh (F.EhZ ι u z) := by
  rw [H.Lz_eq, dTh, dS_add 1 0 H.ana_XZ H.ana_EhZ, XZ, dS_mul 1 0 H.ana_nZ H.anaDi]
  have h1 := H.dTh_evalB F.nZp
  have h2 := H.dTh_Di
  rw [dTh] at h1 h2
  rw [nZ, h1, h2, ← nZ, ← dTh]
  simp only [A21, A22, XZ, nZu, nZz, Du, Dz]
  ring

/-- `𝓛 N_R = (𝓛h) V₀_R + h (𝓛R − a_R')` (product rule, moving centre). -/
theorem Lt_NR : Lt ι (F.NR u z) = Lt ι (F.hN u z) * F.V0R u + F.hN u z * (LR ι u - F.ApR) := by
  rw [NR, Lt, dS_mul _ _ H.ana_hN H.ana_V0R, ← Lt, ← Lt, F.Lt_V0R ι H.ana_u]; rfl

/-- `𝓛 N_z = (𝓛h) V₀_z + h (𝓛z − a_z')` (product rule, moving centre). -/
theorem Lt_NZ : Lt ι (F.NZ u z) = Lt ι (F.hN u z) * F.V0Z z + F.hN u z * (Lz ι z - F.ApZ) := by
  rw [NZ, Lt, dS_mul _ _ H.ana_hN H.ana_V0Z, ← Lt, ← Lt, F.Lt_V0Z ι H.ana_z]; rfl

omit H in
/-- The torsion numerator in terms of the field, the frame vector and the centre velocity. -/
theorem Pof_eq : F.Pof u z =
    (F.nR u z * F.Dof u z - F.Dof u z * (F.nRu u z * F.V0R u + F.nRz u z * F.V0Z z) +
        F.nR u z * (F.Du u z * F.V0R u + F.Dz u z * F.V0Z z) - F.Dof u z ^ 2 * F.ApR) * F.V0Z z -
      (F.nZ u z * F.Dof u z - F.Dof u z * (F.nZu u z * F.V0R u + F.nZz u z * F.V0Z z) +
        F.nZ u z * (F.Du u z * F.V0R u + F.Dz u z * F.V0Z z) - F.Dof u z ^ 2 * F.ApZ) *
        F.V0R u := by
  rw [Pof, F.torsion_poly]; rfl

/-- **Torsion coordinate**: the `∂_θK`-coordinate of `𝓛N − DX·N` is the torsion `T`. -/
theorem torsion_coord :
    F.Wi u z * (F.YRt ι u z * F.V0Z z - F.YZt ι u z * F.V0R u) = F.Tor ι u z := by
  simp only [YRt, YZt, Tor, Talg, NR, NZ, hN, A11, A12, A21, A22, XR, XZ]
  rw [H.LR_eq, H.Lz_eq, Pof_eq]
  simp only [XR, XZ]
  unit_closeG H

/-- **Divergence-free identity solved for `∂_φ D`**: `∂_φD = p n_R/R − ∂_u n_R − ∂_z n_z`. -/
theorem phiD_eq : phiD (xB u z) F.Dp = (F.p : FA) * F.nR u z * F.Ri u - F.nRu u z - F.nZz u z := by
  have hd := F.divFree u z
  have hr : RofG F.R₀ u * F.Ri u = 1 := H.R_Ri
  simp only [nR, nRu, nZz]
  linear_combination F.Ri u * hd -
    (phiD (xB u z) F.Dp + pd (xB u z) 0 F.nRp + pd (xB u z) 1 F.nZp) * hr

/-- `∂ R⁻¹ = −R⁻² ∂u`. -/
theorem d_Ri (a b : ℂ) : dS a b (F.Ri u) = -(F.Ri u ^ 2 * dS a b u) := by
  have h := dS_inverse a b H.ana_R H.unit_R H.ana_Ri
  rw [R, dS_RofG _ _ _ H.ana_u] at h
  exact h

/-- `∂ R^{−k} = −k R^{−k−1} ∂u`. -/
theorem d_Ri_pow (a b : ℂ) (k : ℕ) :
    dS a b (F.Ri u ^ k) = -((k : FA) * F.Ri u ^ (k + 1) * dS a b u) := by
  have h := dS_inv_pow a b H.ana_R H.unit_R H.ana_Ri k
  rw [R, dS_RofG _ _ _ H.ana_u] at h
  exact h

/-- **`𝓛w + w tr DX = (∇w · Ê)`** (the divergence-free identity at work, exponent `p`). -/
theorem Ltw_trA :
    Lt ι (F.wD u z) = F.Ri u ^ F.p * (F.Du u z * F.EhR ι u z + F.Dz u z * F.EhZ ι u z) -
      (F.p : FA) * F.Dof u z * F.Ri u ^ F.p * F.Ri u * F.EhR ι u z -
        F.wD u z * (F.A11 u z + F.A22 u z) := by
  rw [wD, Lt, dS_mul _ _ H.ana_D (H.anaRi.pow _), ← Lt, H.d_Ri_pow, ← Lt]
  have hD := H.Lt_evalB (ι := ι) F.Dp
  rw [← Dof] at hD
  rw [hD, H.phiD_eq, ← LR, H.LR_eq, H.Lz_eq, pow_succ]
  simp only [A11, A22, XR, XZ, Du, Dz, nRu, nZz, nR, nZ]
  unit_closeG H

/-- `𝓛 h = −h² 𝓛(w W₀)` (from `w W₀ h = 1` by the product rule). -/
theorem Lt_hN : Lt ι (F.hN u z) = -(F.hN u z ^ 2 * Lt ι (F.wD u z * F.W0 u z)) := by
  have h1 : Lt ι (F.wD u z * F.W0 u z * F.hN u z) = 0 := by rw [H.wWh, Lt, dS_one]
  rw [Lt, dS_mul _ _ (H.ana_wD.mul H.ana_W) H.ana_hN, ← Lt, ← Lt] at h1
  linear_combination F.hN u z * h1 - Lt ι (F.hN u z) * H.wWh

/-- `𝓛 W₀` by the product rule (the centre moves with velocity `A'`). -/
theorem Lt_W : Lt ι (F.W0 u z) =
    Lt ι (Rt u) * F.V0Z z + Rt u * (Lz ι z - F.ApZ) -
      (Lt ι (zt z) * F.V0R u + zt z * (LR ι u - F.ApR)) := by
  change dS (ι : ℂ) 2 (Rt u * F.V0Z z - zt z * F.V0R u) = _
  rw [dS_sub _ _ (H.ana_Rt.mul H.ana_V0Z) (H.ana_zt.mul H.ana_V0R),
    dS_mul _ _ H.ana_Rt H.ana_V0Z, dS_mul _ _ H.ana_zt H.ana_V0R, ← Lt, ← Lt, ← Lt, ← Lt,
    F.Lt_V0R ι H.ana_u, F.Lt_V0Z ι H.ana_z]; rfl

/-- `𝓛 ∂_θ R = ∂_θ 𝓛 R`. -/
theorem Lt_Rt : Lt ι (Rt u) = dTh (LR ι u) := by
  rw [Lt, Rt, dTh, LR, Lt, dS_dS_comm _ _ _ _ H.ana_u]; rfl

/-- `𝓛 ∂_θ z = ∂_θ 𝓛 z`. -/
theorem Lt_zt : Lt ι (zt z) = dTh (Lz ι z) := by
  rw [Lt, zt, dTh, Lz, Lt, dS_dS_comm _ _ _ _ H.ana_z]; rfl

/-- **Second frame coordinate of `𝓛N − DX·N`**: it is `S`, linear in the error (approximate
reducibility; uses area preservation through `Ltw_trA`; the centre velocity cancels). -/
theorem S_coord :
    F.wD u z * (Rt u * F.YZt ι u z - zt z * F.YRt ι u z) = F.Scoef ι u z := by
  have hLwW : Lt ι (F.wD u z * F.W0 u z) =
      Lt ι (F.wD u z) * F.W0 u z + F.wD u z * Lt ι (F.W0 u z) := by
    rw [Lt, dS_mul _ _ H.ana_wD H.ana_W]; rfl
  simp only [YRt, YZt]
  rw [H.Lt_hN, hLwW, H.Lt_W, H.Lt_Rt, H.Lt_zt, H.dTh_LR, H.dTh_Lz, H.Ltw_trA, H.LR_eq, H.Lz_eq]
  simp only [Scoef, NR, NZ, hN, wD, A11, A12, A21, A22, XR, XZ, W0]
  unit_closeG H

/-! ### The flux identity -/

/-- Analyticity: `ana_Pa`. -/
theorem ana_Pa : Ana (F.Pa u z) := H.ana_evalB F.Pap
/-- Analyticity: `ana_Pb`. -/
theorem ana_Pb : Ana (F.Pb u z) := H.ana_evalB F.Pbp
/-- Analyticity: `ana_aF`. -/
theorem ana_aF : Ana (F.aF u z) := H.ana_Pa.mul (H.anaRi.pow _)
/-- Analyticity: `ana_bF`. -/
theorem ana_bF : Ana (F.bF u z) := H.ana_Pb.mul (H.anaRi.pow _)
/-- Analyticity: `ana_dPh_u`. -/
theorem ana_dPh_u : Ana (dPh u) := H.ana_u.d 0 2
/-- Analyticity: `ana_dPh_z`. -/
theorem ana_dPh_z : Ana (dPh z) := H.ana_z.d 0 2

/-- **Flux identity**: `η₂ = w (∂_θK × Ê) = ∂_θ B − ∂_φ A`, the exterior derivative of the
pulled-back primitive of the flux form (independent of the frame centre). -/
theorem eta2_flux : F.eta2 ι u z = dTh (F.BF u z) - dPh (F.AF u z) := by
  have hcomm_u : dTh (dPh u) = dPh (Rt u) := by
    rw [dTh, dPh, Rt, dTh, dS_dS_comm _ _ _ _ H.ana_u]; rfl
  have hcomm_z : dTh (dPh z) = dPh (zt z) := by
    rw [dTh, dPh, zt, dTh, dS_dS_comm _ _ _ _ H.ana_z]; rfl
  have hBF : dTh (F.BF u z) = dTh (F.aF u z) * dPh u + F.aF u z * dTh (dPh u) +
      (dTh (F.bF u z) * dPh z + F.bF u z * dTh (dPh z)) := by
    rw [BF, dTh, dS_add _ _ (H.ana_aF.mul H.ana_dPh_u) (H.ana_bF.mul H.ana_dPh_z),
      dS_mul _ _ H.ana_aF H.ana_dPh_u, dS_mul _ _ H.ana_bF H.ana_dPh_z]; rfl
  have hAF : dPh (F.AF u z) = dPh (F.aF u z) * Rt u + F.aF u z * dPh (Rt u) +
      (dPh (F.bF u z) * zt z + F.bF u z * dPh (zt z)) := by
    rw [AF, dPh, dS_add _ _ (H.ana_aF.mul H.ana_Rt) (H.ana_bF.mul H.ana_zt),
      dS_mul _ _ H.ana_aF H.ana_Rt, dS_mul _ _ H.ana_bF H.ana_zt]; rfl
  have haθ : dTh (F.aF u z) =
      (pd (xB u z) 0 F.Pap * Rt u + pd (xB u z) 1 F.Pap * zt z) * F.Ri u ^ F.ka +
        F.Pa u z * (-((F.ka : FA) * F.Ri u ^ (F.ka + 1) * Rt u)) := by
    have h := H.dTh_evalB F.Pap
    simp only [dTh] at h
    rw [aF, dTh, dS_mul _ _ H.ana_Pa (H.anaRi.pow _), Pa, h, H.d_Ri_pow]; rfl
  have haφ : dPh (F.aF u z) = (pd (xB u z) 0 F.Pap * dPh u + pd (xB u z) 1 F.Pap * dPh z +
      phiD (xB u z) F.Pap) * F.Ri u ^ F.ka +
        F.Pa u z * (-((F.ka : FA) * F.Ri u ^ (F.ka + 1) * dPh u)) := by
    have h := H.dPh_evalB F.Pap
    simp only [dPh] at h
    rw [aF, dPh, dS_mul _ _ H.ana_Pa (H.anaRi.pow _), Pa, h, H.d_Ri_pow]; rfl
  have hbθ : dTh (F.bF u z) =
      (pd (xB u z) 0 F.Pbp * Rt u + pd (xB u z) 1 F.Pbp * zt z) * F.Ri u ^ F.kb +
        F.Pb u z * (-((F.kb : FA) * F.Ri u ^ (F.kb + 1) * Rt u)) := by
    have h := H.dTh_evalB F.Pbp
    simp only [dTh] at h
    rw [bF, dTh, dS_mul _ _ H.ana_Pb (H.anaRi.pow _), Pb, h, H.d_Ri_pow]; rfl
  have hbφ : dPh (F.bF u z) = (pd (xB u z) 0 F.Pbp * dPh u + pd (xB u z) 1 F.Pbp * dPh z +
      phiD (xB u z) F.Pbp) * F.Ri u ^ F.kb +
        F.Pb u z * (-((F.kb : FA) * F.Ri u ^ (F.kb + 1) * dPh u)) := by
    have h := H.dPh_evalB F.Pbp
    simp only [dPh] at h
    rw [bF, dPh, dS_mul _ _ H.ana_Pb (H.anaRi.pow _), Pb, h, H.d_Ri_pow]; rfl
  have hER : F.EhR ι u z = (ι : ℂ) • Rt u + dPh u - F.XR u z := by
    have h := Lt_eq ι H.ana_u
    rw [show Rt u = dTh u from rfl, ← h, ← LR, H.LR_eq]; ring
  have hEZ : F.EhZ ι u z = (ι : ℂ) • zt z + dPh z - F.XZ u z := by
    have h := Lt_eq ι H.ana_z
    rw [show zt z = dTh z from rfl, ← h, ← Lz, H.Lz_eq]; ring
  have ha := F.flux_a u z H.unit_R
  have hb := F.flux_b u z H.unit_R
  have hc := F.flux_c u z H.unit_R
  have hDDi : PolyExpr.eval (xB u z) F.Dp * F.Di u z = 1 := H.D_Di
  rw [← Ri] at ha hb hc
  rw [hBF, hAF, haθ, haφ, hbθ, hbφ, hcomm_u, hcomm_z]
  simp only [eta2, wD, hER, hEZ, XR, XZ, Algebra.smul_def, Pa, Pb, nR, nZ, Dof]
  linear_combination -(Rt u * dPh z - zt z * dPh u) * ha + Rt u * hb + zt z * hc -
    F.Ri u ^ F.p * (Rt u * PolyExpr.eval (xB u z) F.nZp - zt z * PolyExpr.eval (xB u z) F.nRp) *
      hDDi

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
  have hNR : Ana (F.NR u z) := H.ana_hN.mul H.ana_V0R
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
  have hNZ : Ana (F.NZ u z) := H.ana_hN.mul H.ana_V0Z
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
    PolyExpr.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resRp =
      (ΔR * F.Du u z + ΔZ * F.Dz u z) * LR ι u + F.Dof u z * Lt ι ΔR -
        (ΔR * F.nRu u z + ΔZ * F.nRz u z) := by
  simp only [resRp, PolyExpr.deriv, deriv_eq_sum _ _ F.Dp, deriv_eq_sum _ _ F.nRp, Fin.sum_univ_six]
  rw [pd_noW (i := 4) (by norm_num) F.Dp F.noW_Dp, pd_noW (i := 5) (by norm_num) F.Dp F.noW_Dp,
    pd_noW (i := 4) (by norm_num) F.nRp F.noW_nRp,
    pd_noW (i := 5) (by norm_num) F.nRp F.noW_nRp, pd_xK_xB ι u z 0 F.noW_Dp,
    pd_xK_xB ι u z 1 F.noW_Dp,
    pd_xK_xB ι u z 0 F.noW_nRp, pd_xK_xB ι u z 1 F.noW_nRp, eval_xK_xB ι u z F.noW_Dp]
  simp [hDel, xK, Du, Dz, nRu, nRz, LR, Dof, PolyExpr.eval]

omit H in
/-- The derivative of the `z`-residual along the perturbation. -/
theorem deriv_resZ (ΔR ΔZ : FA) :
    PolyExpr.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resZp =
      (ΔR * F.Du u z + ΔZ * F.Dz u z) * Lz ι z + F.Dof u z * Lt ι ΔZ -
        (ΔR * F.nZu u z + ΔZ * F.nZz u z) := by
  simp only [resZp, PolyExpr.deriv, deriv_eq_sum _ _ F.Dp, deriv_eq_sum _ _ F.nZp, Fin.sum_univ_six]
  rw [pd_noW (i := 4) (by norm_num) F.Dp F.noW_Dp, pd_noW (i := 5) (by norm_num) F.Dp F.noW_Dp,
    pd_noW (i := 4) (by norm_num) F.nZp F.noW_nZp,
    pd_noW (i := 5) (by norm_num) F.nZp F.noW_nZp, pd_xK_xB ι u z 0 F.noW_Dp,
    pd_xK_xB ι u z 1 F.noW_Dp,
    pd_xK_xB ι u z 0 F.noW_nZp, pd_xK_xB ι u z 1 F.noW_nZp, eval_xK_xB ι u z F.noW_Dp]
  simp [hDel, xK, Du, Dz, nZu, nZz, Lz, Dof, PolyExpr.eval]

/-- **The new residual** (`R` component):
`E_R(K + ΔK) = D (𝓛ΔR − (DX·ΔK)_R + Ê_R) + (∇D·ΔK) Ê_R + Q_R`. -/
theorem newton_error_R {ΔR ΔZ : FA} (hR : Ana ΔR) (hZ : Ana ΔZ) :
    F.resR ι (u + ΔR) (z + ΔZ) =
      F.Dof u z * (Lt ι ΔR - (F.A11 u z * ΔR + F.A12 u z * ΔZ) + F.EhR ι u z) +
        (F.Du u z * ΔR + F.Dz u z * ΔZ) * F.EhR ι u z + F.QR ι u z ΔR ΔZ := by
  have e1 : F.resR ι (u + ΔR) (z + ΔZ) =
      F.resR ι u z + PolyExpr.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resRp + F.QR ι u z ΔR ΔZ := by
    rw [resR, H.xK_add hR hZ, QR, resR]; ring
  rw [e1, deriv_resR, H.LR_eq]
  simp only [EhR, A11, A12, XR, Du, Dz, nRu, nRz, nR]
  unit_closeG H

/-- **The new residual** (`z` component). -/
theorem newton_error_Z {ΔR ΔZ : FA} (hR : Ana ΔR) (hZ : Ana ΔZ) :
    F.resZ ι (u + ΔR) (z + ΔZ) =
      F.Dof u z * (Lt ι ΔZ - (F.A21 u z * ΔR + F.A22 u z * ΔZ) + F.EhZ ι u z) +
        (F.Du u z * ΔR + F.Dz u z * ΔZ) * F.EhZ ι u z + F.QZ ι u z ΔR ΔZ := by
  have e1 : F.resZ ι (u + ΔR) (z + ΔZ) =
      F.resZ ι u z + PolyExpr.deriv (xK ι u z) (hDel ι ΔR ΔZ) F.resZp + F.QZ ι u z ΔR ΔZ := by
    rw [resZ, H.xK_add hR hZ, QZ, resZ]; ring
  rw [e1, deriv_resZ, H.Lz_eq]
  simp only [EhZ, A21, A22, XZ, Du, Dz, nZu, nZz, nZ]
  unit_closeG H

end FrameHyp

end FlowFieldG

/-! ## Reduction to the frame of `KamFlowFrame` -/

namespace FlowField

variable (F : FlowField) (ι : ℝ) (u z : FA)

/-- The frame hypotheses of `F.toG` are those of `F`. -/
theorem toG_frameHyp_iff : F.toG.FrameHyp u z ↔ F.FrameHyp u z := by
  have hR : F.toG.R u = 1 + u := F.toG_R u
  have hW : F.toG.W0 u z = W0of u z := F.toG_W0 u z
  constructor
  · intro H
    exact ⟨H.ana_u, H.ana_z, H.unit_D, hR ▸ H.unit_R, hW ▸ H.unit_W, H.ana_Di,
      by have := H.ana_Ri; rwa [FlowFieldG.Ri, ← FlowFieldG.R, hR] at this, hW ▸ H.ana_Wi⟩
  · intro H
    exact ⟨H.ana_u, H.ana_z, H.unit_D, hR ▸ H.unit_R, hW ▸ H.unit_W, H.ana_Di,
      by rw [FlowFieldG.Ri, ← FlowFieldG.R, hR]; exact H.ana_Ri, hW ▸ H.ana_Wi⟩

/-- **Sanity: the generalised `h` is the old one** for `F.toG`. -/
theorem toG_hN : F.toG.hN u z = F.hN u z := by
  rw [FlowFieldG.hN, F.toG_R, FlowFieldG.Wi, F.toG_W0]; rfl

/-- **Sanity: the generalised `η₁` is the old one**. -/
theorem toG_eta1 : F.toG.eta1 ι u z = F.eta1 ι u z := by
  rw [FlowFieldG.eta1, FlowFieldG.Wi, F.toG_W0, F.toG_V0R, F.toG_V0Z]; rfl

/-- **Sanity: the generalised `η₂` is the old one**. -/
theorem toG_eta2 : F.toG.eta2 ι u z = F.eta2 ι u z := by
  rw [FlowFieldG.eta2, FlowFieldG.wD, FlowFieldG.Ri, ← FlowFieldG.R, F.toG_R]; rfl

/-- **Sanity: the generalised torsion is the old one**. -/
theorem toG_Tor : F.toG.Tor ι u z = F.Tor ι u z := by
  rw [FlowFieldG.Tor, FlowFieldG.Talg, FlowFieldG.Wi, F.toG_W0, F.toG_V0R, F.toG_V0Z, F.toG_R]
  rfl

/-- **Sanity: the generalised remainder coefficient is the old one**. -/
theorem toG_Scoef : F.toG.Scoef ι u z = F.Scoef ι u z := by
  rw [FlowFieldG.Scoef, FlowFieldG.Wi, F.toG_W0, F.toG_V0R, F.toG_V0Z, FlowFieldG.Ri,
    ← FlowFieldG.R, F.toG_R]
  norm_num [FlowField.Scoef, Ri, Wi]
  rfl

end FlowField

end PlasmaLean.Design.KamNewton
