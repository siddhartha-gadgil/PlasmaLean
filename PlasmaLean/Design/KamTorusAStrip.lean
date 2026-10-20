/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamNewtonField
public import PlasmaLean.Design.KamTorusAWeighted

/-!
# Torus A in the strip algebra (KAM route, K3d)

The certified approximate torus A (`Design/KamTorusA`, weighted bounds `Design/KamTorusAWeighted`)
as elements `u₀ = R − 1`, `z₀` of the strip algebra `𝔸` (`Theory/KAM/StripAlgebra`), with

* the functions (`eval_u₀`, `eval_z₀`): `F_{u₀}(θ, ψ(φ)) = torusR(θ, φ) − 1`, `F_{z₀} = torusZ`;
* reality and analyticity (`isReal_u₀`, `ana_u₀`, …);
* the derivatives (`dTh_u₀`, `dψ_u₀`, …): the Fourier series of `∂_θ R`, `∂_ψ R = ∂_φ R / 2`, …
  certified in `KamTorusAWeighted`, identified with `∂_θ u₀`, `∂_ψ u₀` by uniqueness of Fourier
  coefficients;
* the strip bounds at `r_A = 0.1257` (`Bd_u₀`, …, `Bd_Lt_u₀`);
* the **residual** (`resR₀_eq`, `Bd_resR₀`): the residual `D·𝓛K − n` of the polynomial forms of
  `Design/KamNewtonField` at torus A (exact `ι`) is the certified residual, so
  `‖E_R‖_{r_A} ≤ 5.83 × 10⁻²²`, `‖E_z‖_{r_A} ≤ 3.465 × 10⁻²²`;
* the denominator (`Bd_D₀`): `‖D(K₀) − d₀‖_{r_A} ≤ 0.483` with `1 ≤ d₀ ≤ 1.007`.

**Sanity.** `eval_u₀` at the level of functions is the definition of torus A; `torusA_D_axis`:
the polynomial `D` evaluates to `Dfun` (the form of `Design/KamTorusA`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamTorusA WEll1Z2 Complex

/-! ## The real point of the variables and the polynomial forms of `Design/KamTorusA` -/

/-- The point `(u, z, c, s, w_R, w_z)` of `ℂ⁶` from real values. -/
def ptC (u z c s wR wZ : ℝ) : Fin 6 → ℂ := ![u, z, c, s, wR, wZ]

/-- `D` in the `u`-form is `Dfun` at `R = 1 + u`. -/
theorem eval_Dp_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) Dp = (Dfun (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, Dp, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Dfun, sfun, sgfun, eps]
  push_cast; ring

/-- `n_R = 2εR Ps` at `R = 1 + u`. -/
theorem eval_nRp_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nRp = (2 * eps * (1 + u) * Psfun (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nRp, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Psfun, s2fs, s2gs, eps]
  push_cast; ring

/-- `n_z = εR² Pz` at `R = 1 + u`. -/
theorem eval_nZp_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) nZp = (eps * (1 + u) ^ 2 * Pzfun (1 + u) z c s : ℂ) := by
  simp only [PolyExpr.eval, nZp, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Pzfun, sgz, eps]
  push_cast; ring

/-- The `R`-residual polynomial at a real point. -/
theorem eval_resRp_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) resRp =
      ((Dfun (1 + u) z c s * wR - 2 * eps * (1 + u) * Psfun (1 + u) z c s : ℝ) : ℂ) := by
  have h1 := eval_Dp_ptC u z c s wR wZ
  have h2 := eval_nRp_ptC u z c s wR wZ
  simp only [resRp, PolyExpr.eval] at *
  rw [h1, h2]; simp [ptC]

/-- The `z`-residual polynomial at a real point. -/
theorem eval_resZp_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) resZp =
      ((Dfun (1 + u) z c s * wZ - eps * (1 + u) ^ 2 * Pzfun (1 + u) z c s : ℝ) : ℂ) := by
  have h1 := eval_Dp_ptC u z c s wR wZ
  have h2 := eval_nZp_ptC u z c s wR wZ
  simp only [resZp, PolyExpr.eval] at *
  rw [h1, h2]; simp [ptC]

/-! ## The torus elements -/

/-- `r_A ≥ 0`. -/
theorem rA_nonneg : 0 ≤ rA := by norm_num [rA]

/-- `r_A > 0`. -/
theorem rA_pos : 0 < rA := by norm_num [rA]

/-- `φ` from `ψ = 2φ − π/2`. -/
def phiOf (ψ : ℝ) : ℝ := (ψ + Real.pi / 2) / 2

/-- `psi (phiOf ψ) = ψ`. -/
theorem psi_phiOf (ψ : ℝ) : psi (phiOf ψ) = ψ := by simp [psi, phiOf]; ring

/-- Element of `𝔸` from a coefficient function with a bound at `r_A`. -/
def ofA (f : ℤ × ℤ → ℂ) (hf : InWeighted rA f) : FA := ofCoeff f (hf.mono rA_nonneg)

/-- Coefficients of `ofA`. -/
@[simp] theorem coeff_ofA (f : ℤ × ℤ → ℂ) (hf : InWeighted rA f) : coeff (ofA f hf) = f := by
  funext n; simp [ofA]

/-- `Bd` of `ofA`. -/
theorem Bd_ofA {f : ℤ × ℤ → ℂ} (hf : InWeighted rA f) {B : ℝ} (hB : wnorm rA f ≤ B) :
    Bd rA (ofA f hf) B := by rw [Bd, coeff_ofA]; exact ⟨hf, hB⟩

/-- `ofA` is analytic. -/
theorem ana_ofA {f : ℤ × ℤ → ℂ} (hf : InWeighted rA f) : Ana (ofA f hf) :=
  ⟨rA, _, rA_pos, Bd_ofA hf le_rfl⟩

/-- The function of `ofA`. -/
theorem eval_ofA (f : ℤ × ℤ → ℂ) (hf : InWeighted rA f) (θ ψ : ℝ) :
    eval (ofA f hf) θ ψ = fourierSum f θ ψ := by rw [eval, coeff_ofA]

/-- `u₀ = R − 1` of torus A. -/
def u₀ : FA := ofA Rm1coef torusA_weighted_Rm1.2.1
/-- `z₀` of torus A. -/
def z₀ : FA := ofA Zcoef torusA_weighted_Z.2.1
/-- `∂_θ R` of torus A. -/
def Rθ₀ : FA := ofA Rθcoef torusA_weighted_Rθ.2.1
/-- `∂_θ z` of torus A. -/
def zθ₀ : FA := ofA Zθcoef torusA_weighted_Zθ.2.1
/-- `∂_ψ R = ∂_φ R / 2` of torus A. -/
def Rψ₀ : FA := ofA Rψcoef torusA_weighted_Rψ.2.1
/-- `∂_ψ z` of torus A. -/
def zψ₀ : FA := ofA Zψcoef torusA_weighted_Zψ.2.1

/-- The function of `u₀`. -/
theorem eval_u₀ (θ ψ : ℝ) : eval u₀ θ ψ = (torusR θ (phiOf ψ) - 1 : ℝ) := by
  rw [u₀, eval_ofA, torusA_weighted_Rm1.1, psi_phiOf]
/-- The function of `z₀`. -/
theorem eval_z₀ (θ ψ : ℝ) : eval z₀ θ ψ = (torusZ θ (phiOf ψ) : ℝ) := by
  rw [z₀, eval_ofA, torusA_weighted_Z.1, psi_phiOf]
/-- The function of `Rθ₀`. -/
theorem eval_Rθ₀ (θ ψ : ℝ) : eval Rθ₀ θ ψ = (torusRθ θ (phiOf ψ) : ℝ) := by
  rw [Rθ₀, eval_ofA, torusA_weighted_Rθ.1, psi_phiOf]
/-- The function of `zθ₀`. -/
theorem eval_zθ₀ (θ ψ : ℝ) : eval zθ₀ θ ψ = (torusZθ θ (phiOf ψ) : ℝ) := by
  rw [zθ₀, eval_ofA, torusA_weighted_Zθ.1, psi_phiOf]
/-- The function of `Rψ₀`. -/
theorem eval_Rψ₀ (θ ψ : ℝ) : eval Rψ₀ θ ψ = (torusRφ θ (phiOf ψ) / 2 : ℝ) := by
  rw [Rψ₀, eval_ofA, torusA_weighted_Rψ.1, psi_phiOf]
/-- The function of `zψ₀`. -/
theorem eval_zψ₀ (θ ψ : ℝ) : eval zψ₀ θ ψ = (torusZφ θ (phiOf ψ) / 2 : ℝ) := by
  rw [zψ₀, eval_ofA, torusA_weighted_Zψ.1, psi_phiOf]

/-- Analyticity of the torus elements. -/
theorem ana_u₀ : Ana u₀ := ana_ofA _
/-- Analyticity of `z₀`. -/
theorem ana_z₀ : Ana z₀ := ana_ofA _

/-- Reality from a real-valued function. -/
theorem isReal_of_eval_real {x : FA} {f : ℝ → ℝ → ℝ} (h : ∀ θ ψ, eval x θ ψ = (f θ ψ : ℂ)) :
    IsReal x := (isReal_iff_eval x).2 fun θ ψ => by rw [h, Complex.conj_ofReal]

/-- `u₀` is real. -/
theorem isReal_u₀ : IsReal u₀ := isReal_of_eval_real eval_u₀
/-- `z₀` is real. -/
theorem isReal_z₀ : IsReal z₀ := isReal_of_eval_real eval_z₀

/-! ## Derivatives -/

/-- `φ ↦ phiOf` has derivative `1/2`. -/
theorem hasDerivAt_phiOf (ψ : ℝ) : HasDerivAt phiOf (1 / 2) ψ :=
  ((hasDerivAt_id ψ).add_const (Real.pi / 2)).div_const 2

/-- `∂_θ u₀ = Rθ₀`. -/
theorem dTh_u₀ : dTh u₀ = Rθ₀ := ext_eval fun θ ψ => by
  have h1 := hasDerivAt_eval_θ ana_u₀ θ ψ
  have h2 : HasDerivAt (fun θ' => eval u₀ θ' ψ) ((torusRθ θ (phiOf ψ) : ℝ) : ℂ) θ := by
    have := ((hasDerivAt_torusR_θ θ (phiOf ψ)).sub_const 1).ofReal_comp
    convert this using 1; funext θ'; rw [eval_u₀]
  rw [dTh, h1.unique h2, eval_Rθ₀]

/-- `∂_θ z₀ = zθ₀`. -/
theorem dTh_z₀ : dTh z₀ = zθ₀ := ext_eval fun θ ψ => by
  have h1 := hasDerivAt_eval_θ ana_z₀ θ ψ
  have h2 : HasDerivAt (fun θ' => eval z₀ θ' ψ) ((torusZθ θ (phiOf ψ) : ℝ) : ℂ) θ := by
    have := (hasDerivAt_torusZ_θ θ (phiOf ψ)).ofReal_comp
    convert this using 1; funext θ'; rw [eval_z₀]
  rw [dTh, h1.unique h2, eval_zθ₀]

/-- `∂_ψ u₀ = Rψ₀`. -/
theorem dψ_u₀ : dS 0 1 u₀ = Rψ₀ := ext_eval fun θ ψ => by
  have h1 := hasDerivAt_eval_ψ ana_u₀ θ ψ
  have h2 : HasDerivAt (fun ψ' => eval u₀ θ ψ') ((torusRφ θ (phiOf ψ) / 2 : ℝ) : ℂ) ψ := by
    have := (((hasDerivAt_torusR_φ θ (phiOf ψ)).comp ψ (hasDerivAt_phiOf ψ)).sub_const
      1).ofReal_comp
    convert this using 1
    · funext ψ'; rw [eval_u₀]; rfl
    · push_cast; ring
  rw [h1.unique h2, eval_Rψ₀]

/-- `∂_ψ z₀ = zψ₀`. -/
theorem dψ_z₀ : dS 0 1 z₀ = zψ₀ := ext_eval fun θ ψ => by
  have h1 := hasDerivAt_eval_ψ ana_z₀ θ ψ
  have h2 : HasDerivAt (fun ψ' => eval z₀ θ ψ') ((torusZφ θ (phiOf ψ) / 2 : ℝ) : ℂ) ψ := by
    have := ((hasDerivAt_torusZ_φ θ (phiOf ψ)).comp ψ (hasDerivAt_phiOf ψ)).ofReal_comp
    convert this using 1
    · funext ψ'; rw [eval_z₀]; rfl
    · push_cast; ring
  rw [h1.unique h2, eval_zψ₀]

/-- `∂_φ = 2 ∂_ψ` on analytic elements. -/
theorem dPh_eq {x : FA} (hx : Ana x) : dPh x = (2 : ℂ) • dS 0 1 x := by
  rw [dPh, ← dS_smul_symbol _ _ _ hx]; norm_num

/-! ## Strip bounds at `r_A` -/

/-- `‖u₀‖ ≤ 0.228`. -/
theorem Bd_u₀ : Bd rA u₀ (228 / 1000) := Bd_ofA _ torusA_weighted_Rm1.2.2
/-- `‖z₀‖ ≤ 0.224`. -/
theorem Bd_z₀ : Bd rA z₀ (224 / 1000) := Bd_ofA _ torusA_weighted_Z.2.2
/-- `‖∂_θ u₀‖ ≤ 0.236`. -/
theorem Bd_Rθ₀ : Bd rA (dTh u₀) (236 / 1000) := dTh_u₀ ▸ Bd_ofA _ torusA_weighted_Rθ.2.2
/-- `‖∂_θ z₀‖ ≤ 0.231`. -/
theorem Bd_zθ₀ : Bd rA (dTh z₀) (231 / 1000) := dTh_z₀ ▸ Bd_ofA _ torusA_weighted_Zθ.2.2
/-- `‖∂_ψ u₀‖ ≤ 0.065`. -/
theorem Bd_Rψ₀ : Bd rA (dS 0 1 u₀) (65 / 1000) := dψ_u₀ ▸ Bd_ofA _ torusA_weighted_Rψ.2.2
/-- `‖∂_ψ z₀‖ ≤ 0.063`. -/
theorem Bd_zψ₀ : Bd rA (dS 0 1 z₀) (63 / 1000) := dψ_z₀ ▸ Bd_ofA _ torusA_weighted_Zψ.2.2

/-- `‖𝓛 u₀‖ ≤ ι ‖∂_θ u₀‖ + 2 ‖∂_ψ u₀‖`. -/
theorem Bd_Lt {ι : ℝ} (hι : 0 ≤ ι) {x : FA} (hx : Ana x) {a b : ℝ} (ha : Bd rA (dTh x) a)
    (hb : Bd rA (dS 0 1 x) b) : Bd rA (Lt ι x) (ι * a + 2 * b) := by
  rw [Lt_eq ι hx, dPh_eq hx]
  have h := (ha.smul (ι : ℂ)).add (hb.smul (2 : ℂ))
  simpa [Complex.norm_real, Real.norm_of_nonneg hι] using h


/-- `ι = (75 + √5)/562 ≥ 0`. -/
theorem iota_nonneg : 0 ≤ iota := by unfold iota; positivity

/-- The function of `𝓛 u₀ = ι ∂_θR + ∂_φR`. -/
theorem eval_Lt_u₀ (ι θ ψ : ℝ) :
    eval (Lt ι u₀) θ ψ = (torusRφ θ (phiOf ψ) + ι * torusRθ θ (phiOf ψ) : ℝ) := by
  rw [Lt_eq ι ana_u₀, dPh_eq ana_u₀, eval_add', eval_smul', eval_smul', dTh_u₀, dψ_u₀,
    eval_Rθ₀, eval_Rψ₀]
  push_cast; ring

/-- The function of `𝓛 z₀`. -/
theorem eval_Lt_z₀ (ι θ ψ : ℝ) :
    eval (Lt ι z₀) θ ψ = (torusZφ θ (phiOf ψ) + ι * torusZθ θ (phiOf ψ) : ℝ) := by
  rw [Lt_eq ι ana_z₀, dPh_eq ana_z₀, eval_add', eval_smul', eval_smul', dTh_z₀, dψ_z₀,
    eval_zθ₀, eval_zψ₀]
  push_cast; ring

/-- The values of the residual variables at torus A. -/
theorem eval_xK₀ (ι θ ψ : ℝ) :
    (fun j => eval (xK ι u₀ z₀ j) θ ψ) =
      ptC (torusR θ (phiOf ψ) - 1) (torusZ θ (phiOf ψ)) (Real.cos (2 * phiOf ψ))
        (Real.sin (2 * phiOf ψ)) (torusRφ θ (phiOf ψ) + ι * torusRθ θ (phiOf ψ))
        (torusZφ θ (phiOf ψ) + ι * torusZθ θ (phiOf ψ)) := by
  funext j
  fin_cases j
  · simp [xK, ptC, eval_u₀]
  · simp [xK, ptC, eval_z₀]
  · simp [xK, ptC, eval_cS, cos_two_mul_eq, psi_phiOf]
  · simp [xK, ptC, eval_sS, sin_two_mul_eq, psi_phiOf]
  · simp [xK, ptC, eval_Lt_u₀]
  · simp [xK, ptC, eval_Lt_z₀]

/-- **The residual at torus A is the certified residual** (`R` component). -/
theorem resR₀_eq : resR iota u₀ z₀ = ofA resRcoef torusA_weighted_error_le.2.2.1 :=
  ext_eval fun θ ψ => by
    rw [resR, eval_polyExpr, eval_xK₀, eval_resRp_ptC, eval_ofA, ← psi_phiOf ψ,
      ← torusA_weighted_error_le.1 θ (phiOf ψ), psi_phiOf, KamTorusA.resR, resRw]
    congr 1; ring_nf

/-- **The residual at torus A is the certified residual** (`z` component). -/
theorem resZ₀_eq : resZ iota u₀ z₀ = ofA resZcoef torusA_weighted_error_le.2.2.2.1 :=
  ext_eval fun θ ψ => by
    rw [resZ, eval_polyExpr, eval_xK₀, eval_resZp_ptC, eval_ofA, ← psi_phiOf ψ,
      ← torusA_weighted_error_le.2.1 θ (phiOf ψ), psi_phiOf, KamTorusA.resZ, resZw]
    congr 1; ring_nf

/-- **Residual bound** at torus A: `‖E_R‖_{r_A} ≤ 5.83 × 10⁻²²`. -/
theorem Bd_resR₀ : Bd rA (resR iota u₀ z₀) (583 / 10 ^ 24) :=
  resR₀_eq ▸ Bd_ofA _ torusA_weighted_error_le.2.2.2.2.1

/-- **Residual bound** at torus A: `‖E_z‖_{r_A} ≤ 3.465 × 10⁻²²`. -/
theorem Bd_resZ₀ : Bd rA (resZ iota u₀ z₀) (3465 / 10 ^ 25) :=
  resZ₀_eq ▸ Bd_ofA _ torusA_weighted_error_le.2.2.2.2.2

/-- `D(K₀) − d₀` is the certified series. -/
theorem D₀_eq : Dof u₀ z₀ - algebraMap ℂ FA (dA0 : ℂ) = ofA Dsubcoef torusA_weighted_D.2.2.2.1 :=
  ext_eval fun θ ψ => by
    rw [eval_sub', eval_algebraMap, Dof, eval_polyExpr, eval_ofA, ← psi_phiOf ψ,
      ← torusA_weighted_D.2.2.1 θ (phiOf ψ), psi_phiOf]
    have e : (fun j => eval (xB u₀ z₀ j) θ ψ) = ptC (torusR θ (phiOf ψ) - 1) (torusZ θ (phiOf ψ))
        (Real.cos (2 * phiOf ψ)) (Real.sin (2 * phiOf ψ)) 0 0 := by
      funext j
      fin_cases j
      · simp [xB, ptC, eval_u₀]
      · simp [xB, ptC, eval_z₀]
      · simp [xB, ptC, eval_cS, cos_two_mul_eq, psi_phiOf]
      · simp [xB, ptC, eval_sS, sin_two_mul_eq, psi_phiOf]
      · simp [xB, ptC]
      · simp [xB, ptC]
    rw [e, eval_Dp_ptC, Dval]
    push_cast; ring_nf

/-- **The denominator at torus A**: `‖D(K₀) − d₀‖_{r_A} ≤ 0.483`, `1 ≤ d₀ ≤ 1.007`. -/
theorem Bd_D₀ : Bd rA (Dof u₀ z₀ - algebraMap ℂ FA (dA0 : ℂ)) (483 / 1000) :=
  D₀_eq ▸ Bd_ofA _ torusA_weighted_D.2.2.2.2

end PlasmaLean.Design.KamNewton
