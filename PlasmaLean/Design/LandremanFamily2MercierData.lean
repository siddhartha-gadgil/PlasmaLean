/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Quad
public import PlasmaLean.Theory.Stability.MercierGeneral

/-!
# The Mercier surface data of Landreman's family 2 and their closed forms

For Landreman's family 2 (arXiv:2609.26742 v2, §3) with `ε = 1/4`, `S = 4` and any `λ > 0`,
this module defines the eight numbers entering the general Mercier index of
`PlasmaLean.Stability.MercierGeneral` (Landreman–Jorge 2020, eq. (3.1), a SUPPLIED formula) on
the flux surface `ψ = k²/2`, from the actual objects of `LandremanFamily2`:

* labels (`LandremanFamily2Labels`): toroidal flux `2π ψ_t` (`psiT`), poloidal flux
  (`psiP`), rotational transform `ι = dψ_p/dψ_t` (`iotaK`), volume `V` (`volK`) and Boozer
  current `I = μ₀ I_tor/2π` (`curK`), all as functions of `k`; every `'` is `d/dψ_t`, computed
  with Lean's `deriv` in `k` and the chain rule (`iotaPrimeK`, `VppK`, `IprimeK`);
* `μ₀ p'` from the actual pressure `LandremanFamily2.pressure` evaluated on the surface
  (`muPprimeK`);
* the surface integrals `∫ f dS/|∇ψ_t|³ = ∫∫ f Jac/(ψ_t'³ |∇ψ|²) dχ dζ` over the explicit
  parametrization `surfPt` of `LandremanFamily2Surface`, with `Jac = G/(λ h T cc)` the
  Jacobian of `(ψ, χ, ζ) ↦ x` (paper (3.18)), the actual field `field`, the actual current
  `current` (from the Fréchet derivative), the actual gradient `gradPsi`, and
  `Ξ = μ₀ J - I' B` (`intB2K`, `intBXiK`, `intXi2K`);
* signs `s_ψ = +1` (`ψ > 0`) and `s_G` a parameter (`±1`).

`mercierIndex_family2_eq` proves that `(2π)⁶ D_Merc` equals the closed form `D6R` of
`LandremanFamily2Quad`, the quantity enclosed by the validated checker `cellCheck`.

Scope: the identification of `ψ_t`, `ψ_p`, `V`, `I` (one-dimensional integrals of
`LandremanFamily2Labels`) and of `Jac dχ dζ` with the physical flux, volume, current and
area element rests on the change of variables to the coordinates `(ψ, χ, ζ)` of paper
(3.12)–(3.18); the pointwise closed forms of `B`, `∇ψ`, `J` are proved, but the
change-of-variables/covering step is not formalized.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2MercierData

open Real PlasmaLean.Fields PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanFamily2Surface PlasmaLean.Design.LandremanFamily2Rotated
open PlasmaLean.Design.LandremanFamily2Labels PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Stability.MercierGeneral
open Filter Topology

/-! ## Definitions -/

/-- `dψ_t/dψ = (dψ_t/dk)/k`. -/
@[expose] def tpK (lam k : ℝ) : ℝ := deriv (psiT lam (1 / 4) 4) k / k

/-- The surface weight `Jac/(ψ_t'³ |∇ψ|²)` (so that `∫ f dS/|∇ψ_t|³ = ∫∫ f · wSurf`). -/
@[expose] def wSurf (lam k χ ζ : ℝ) : ℝ :=
  JacR lam k (sin χ) (cos χ) (sin (2 * ζ)) (cos (2 * ζ)) /
    (tpK lam k ^ 3 * ‖gradPsi (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)‖ ^ 2)

/-- `I' = dI/dψ_t`. -/
@[expose] def IprimeK (lam k : ℝ) : ℝ :=
  deriv (curK lam (1 / 4) 4) k / deriv (psiT lam (1 / 4) 4) k

/-- `Ξ = μ₀ J - I' B` at the surface point. -/
@[expose] def XiS (μ₀ lam k χ ζ : ℝ) : Space :=
  μ₀ • current μ₀ (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ) -
    IprimeK lam k • field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)

/-- `∫ B² dS/|∇ψ_t|³`. -/
@[expose] def intB2K (lam k : ℝ) : ℝ :=
  ∫ ζ in (-π)..π, ∫ χ in (-π)..π,
    ‖field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)‖ ^ 2 * wSurf lam k χ ζ

/-- `∫ B·Ξ dS/|∇ψ_t|³`. -/
@[expose] def intBXiK (μ₀ lam k : ℝ) : ℝ :=
  ∫ ζ in (-π)..π, ∫ χ in (-π)..π,
    ⟪field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ), XiS μ₀ lam k χ ζ⟫ * wSurf lam k χ ζ

/-- `∫ |Ξ|² dS/|∇ψ_t|³`. -/
@[expose] def intXi2K (μ₀ lam k : ℝ) : ℝ :=
  ∫ ζ in (-π)..π, ∫ χ in (-π)..π, ‖XiS μ₀ lam k χ ζ‖ ^ 2 * wSurf lam k χ ζ

/-- `ι' = dι/dψ_t`. -/
@[expose] def iotaPrimeK (lam k : ℝ) : ℝ :=
  deriv (iotaK lam (1 / 4) 4) k / deriv (psiT lam (1 / 4) 4) k

/-- `μ₀ p' = μ₀ dp/dψ_t`, from the actual pressure `(p_a - ψ/λ²)/μ₀` on the surface. -/
@[expose] def muPprimeK (μ₀ pa lam k : ℝ) : ℝ :=
  deriv (fun κ => μ₀ * pressure μ₀ pa (1 / 4) 4 lam (surfPt (1 / 4) 4 lam κ 0 0)) k /
    deriv (psiT lam (1 / 4) 4) k

/-- `V'' = d²V/dψ_t²` (chain rule in `k`). -/
@[expose] def VppK (lam k : ℝ) : ℝ :=
  deriv (fun κ => deriv (volK lam (1 / 4)) κ / deriv (psiT lam (1 / 4) 4) κ) k /
    deriv (psiT lam (1 / 4) 4) k

/-- **The Mercier surface data of family 2** (`ε = 1/4`, `S = 4`) on the surface `ψ = k²/2`. -/
@[expose] def family2Data (μ₀ pa lam sG k : ℝ) : MercierSurfaceData where
  sG := sG
  sψ := 1
  iotaPrime := iotaPrimeK lam k
  muPprime := muPprimeK μ₀ pa lam k
  Vpp := VppK lam k
  intBXi := intBXiK μ₀ lam k
  intXi2 := intXi2K μ₀ lam k
  intB2 := intB2K lam k

/-! ## Closed forms -/

section ClosedForms
variable {lam k : ℝ}

/-- `ε = 1/4 ≠ 0`. -/
theorem eps_ne : (1 / 4 : ℝ) ≠ 0 := by norm_num

/-- Surfaces of the band have `|k| < 1`. -/
theorem mem_Ioo1 (hk0 : 0 < k) (hk1 : k < 19 / 20) : k ∈ Set.Ioo (-1 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

/-- `dψ_t/dk = k F₁/(4πλ)`. -/
theorem deriv_psiT_eq (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    deriv (psiT lam (1 / 4) 4) k = k * F1 (1 / 4) 4 k / (4 * π * lam) :=
  (hasDerivAt_psiT eps_ne (mem_Ioo1 hk0 hk1)).deriv

/-- `F₁ ≠ 0`. -/
theorem F1_ne (hk0 : 0 < k) (hk1 : k < 19 / 20) : F1 (1 / 4) 4 k ≠ 0 :=
  (F1_pos eps_ne (mem_Ioo1 hk0 hk1)).ne'

/-- `ψ_t'(ψ) = F₁/(4πλ)`. -/
theorem tpK_eq (hk0 : 0 < k) (hk1 : k < 19 / 20) : tpK lam k = tpR lam k := by
  unfold tpK tpR
  rw [deriv_psiT_eq hk0 hk1]
  field_simp [hk0.ne']

/-- `ι'` in closed form. -/
theorem iotaPrimeK_eq (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    iotaPrimeK lam k = iotapR lam k := by
  unfold iotaPrimeK iotapR tpR
  rw [deriv_iotaK eps_ne hl ⟨hk0, by linarith⟩, deriv_psiT_eq hk0 hk1]
  have := F1_ne hk0 hk1
  have := pi_pos.ne'
  field_simp [hk0.ne']

/-- `μ₀ p'` in closed form. -/
theorem muPprimeK_eq (hl : lam ≠ 0) (hμ : μ₀ ≠ 0) (pa : ℝ) (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    muPprimeK μ₀ pa lam k = -((4 * π) * (lam * F1 (1 / 4) 4 k)⁻¹) := by
  have hev : (fun κ => μ₀ * pressure μ₀ pa (1 / 4) 4 lam (surfPt (1 / 4) 4 lam κ 0 0)) =ᶠ[𝓝 k]
      fun κ => pa - κ ^ 2 / 2 / lam ^ 2 := by
    filter_upwards [Ioo_mem_nhds hk0 hk1] with κ hκ
    rw [pressure, psi_surfPt hl hκ.1 hκ.2.le]
    field_simp
  have hd : HasDerivAt (fun κ : ℝ => pa - κ ^ 2 / 2 / lam ^ 2) (-(k / lam ^ 2)) k := by
    have := ((hasDerivAt_pow 2 k).div_const 2).div_const (lam ^ 2) |>.const_sub pa
    convert this using 1; push_cast; ring
  unfold muPprimeK
  rw [hev.deriv_eq, hd.deriv, deriv_psiT_eq hk0 hk1]
  have := F1_ne hk0 hk1
  have := pi_pos.ne'
  field_simp [hk0.ne']

/-- `V''` in closed form. -/
theorem VppK_eq (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    VppK lam k = (((2 * π) * ((Zd (1 / 4) k * Eint k * F1 (1 / 4) 4 k +
      Zint (1 / 4) k * Ed k * F1 (1 / 4) 4 k) - Zint (1 / 4) k * Eint k * F1d (1 / 4) 4 k)) *
      (F1 (1 / 4) 4 k ^ 2)⁻¹) * (k * tpR lam k)⁻¹ := by
  unfold VppK tpR
  rw [deriv_volRatio eps_ne hl ⟨hk0, by linarith⟩, deriv_psiT_eq hk0 hk1]
  have := F1_ne hk0 hk1
  have := pi_pos.ne'
  field_simp [hk0.ne']

/-- `λ - I' = -2E/(λF₁)`. -/
theorem IprimeK_eq (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    lam - IprimeK lam k = dIR lam k := by
  unfold IprimeK dIR
  rw [(hasDerivAt_curK eps_ne (mem_Ioo1 hk0 hk1)).deriv, deriv_psiT_eq hk0 hk1]
  have := F1_ne hk0 hk1
  have := pi_pos.ne'
  field_simp [hk0.ne']
  ring

/-- Pull a constant out of a double interval integral after a pointwise rewrite. -/
theorem double_integral_eq {F G : ℝ → ℝ → ℝ} (c : ℝ) (h : ∀ χ ζ, F χ ζ = c * G χ ζ) :
    ∫ ζ in (-π)..π, ∫ χ in (-π)..π, F χ ζ = c * ∫ ζ in (-π)..π, ∫ χ in (-π)..π, G χ ζ := by
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext ζ
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext χ
  exact h χ ζ

/-- The pointwise identity behind all three surface integrals. -/
theorem weight_eq (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) (χ ζ X : ℝ) :
    X * wSurf lam k χ ζ = (1 / (lam ^ 4 * tpK lam k ^ 3)) *
      (lam ^ 2 * (X * JacR lam k (sin χ) (cos χ) (sin (2 * ζ)) (cos (2 * ζ))) /
        (gp2 (1 / 4) 4 lam k (sin χ) (cos χ) (sin (2 * ζ)) (cos (2 * ζ)) / lam ^ 2)) := by
  unfold wSurf
  rw [normSq_gradPsi_surfPt hl hk0 hk1]
  have hg := gp2_pos (ε := 1 / 4) (S := 4) (lam := lam) (k := k) (s1 := sin χ) (c1 := cos χ)
    (s2 := sin (2 * ζ)) (c2 := cos (2 * ζ)) (sin_sq_add_cos_sq χ) (by norm_num)
    (abs_cos_le_one _) hk0 (k_sq_lt_one hk0 hk1) hl
  by_cases ht : tpK lam k = 0
  · simp [ht]
  · field_simp

/-- `∫ B² dS/|∇ψ_t|³` in closed form. -/
theorem intB2K_eq (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k < 19 / 20) (dI : ℝ) :
    intB2K lam k = (1 / (lam ^ 4 * tpK lam k ^ 3)) * IntR 0 lam dI k := by
  unfold intB2K IntR
  refine double_integral_eq _ (fun χ ζ => ?_)
  rw [normSq_field_surfPt hl hk0 hk1.le, weight_eq hl hk0 hk1.le]
  simp [Hsel, HB]

/-- `∫ B·Ξ dS/|∇ψ_t|³` in closed form. -/
theorem intBXiK_eq (hl : lam ≠ 0) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    intBXiK μ₀ lam k = (1 / (lam ^ 4 * tpK lam k ^ 3)) * IntR 1 lam (dIR lam k) k := by
  unfold intBXiK IntR XiS
  refine double_integral_eq _ (fun χ ζ => ?_)
  rw [inner_field_Xi_surfPt hl hk0 hk1.le hμ, IprimeK_eq hl hk0 hk1, weight_eq hl hk0 hk1.le]
  simp [Hsel, HX]

/-- `∫ |Ξ|² dS/|∇ψ_t|³` in closed form. -/
theorem intXi2K_eq (hl : lam ≠ 0) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    intXi2K μ₀ lam k = (1 / (lam ^ 4 * tpK lam k ^ 3)) * IntR 2 lam (dIR lam k) k := by
  unfold intXi2K IntR XiS
  refine double_integral_eq _ (fun χ ζ => ?_)
  rw [normSq_Xi_surfPt hl hk0 hk1.le hμ, IprimeK_eq hl hk0 hk1, weight_eq hl hk0 hk1.le]
  simp only [Hsel, HZ, Fin.isValue, show (2 : Fin 3) ≠ 0 by simp, show (2 : Fin 3) ≠ 1 by simp,
    ite_false]
  ring

/-- **The Mercier index of family 2 equals the certified closed form**:
`(2π)⁶ D_Merc = D6R`. -/
theorem mercierIndex_family2_eq (hl : 0 < lam) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (pa sG : ℝ) (hk0 : 0 < k)
    (hk1 : k < 19 / 20) :
    mercierIndex (family2Data μ₀ pa lam sG k) = D6R lam k sG / (2 * π) ^ 6 := by
  have hl0 := hl.ne'
  have htp : tpK lam k = tpR lam k := tpK_eq hk0 hk1
  have hF := F1_ne hk0 hk1
  unfold mercierIndex MercierSurfaceData.shearBracket MercierSurfaceData.wellBracket family2Data
  simp only
  rw [iotaPrimeK_eq hl0 hk0 hk1, muPprimeK_eq hl0 hμ pa hk0 hk1, VppK_eq hl0 hk0 hk1,
    intB2K_eq hl0 hk0 hk1 (dIR lam k), intBXiK_eq hl0 hμ hk0 hk1, intXi2K_eq hl0 hμ hk0 hk1, htp]
  unfold D6R B2R BXiR Xi2R c3R itpR wellR tpR
  have := pi_pos.ne'
  field_simp

end ClosedForms

end PlasmaLean.Design.LandremanFamily2MercierData
