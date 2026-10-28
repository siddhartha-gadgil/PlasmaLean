/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.CauchyTwoVar
public import LeanTheory.Theory.KAM.FourierSumHolo

/-!
# Analytic fields along a complexified torus embedding

Glue between `Theory/KAM/CauchyTwoVar` (`AnaFieldAt.of_holomorphic`) and
`Theory/KAM/FourierSumHolo` (the complexified torus map `torusMapC`). A scalar field `F` on
complex space `CVec = ℂ³`, holomorphic and bounded by `M` on a set `U`, composed with the torus
map

`(θ, ψ, z₁, z₂) ↦ cylC (K₁(θ, ψ) + z₁, ψ, K₂(θ, ψ) + z₂)`,

`K_i = fourierSumC u_i` (absolutely convergent Fourier series in `ℓ¹_{ρ'}`), is an analytic field
along the torus as soon as the complexified torus neighbourhood `|Im θ|, |Im ψ| < ρ'`,
`|zᵢ| < d'` is mapped into `U`:

* `holoData_torus`: the `HoloData` hypotheses for `F ∘ torusMapC`;
* **`anaFieldAt_torus`**: `AnaFieldAt r (M ((1+q)/(1-q))²) d (F ∘ torusMapC)`.

For checking the mapping hypothesis, `norm_fourierSumC_sub_re_le` bounds the displacement of a
Fourier series under complexification: `|K(θ, ψ) − K(Re θ, Re ψ)| ≤ ‖u‖_ρ − ‖u‖_0` on
`|Im θ|, |Im ψ| ≤ ρ`; the cylindrical part is controlled by the exact identities
`norm_imV_cylC_sq`, `norm_reV_cylC_sub_sq` of `FourierSumHolo`.

**Sanity.** `norm_fourierSumC_sub_re_zero` (no displacement at real points) and
`anaFieldAt_torus_const` (a constant field, fixture for the interface).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM.TorusFieldAna

open Complex Set Metric WEll1Z2
open LeanTheory.Theory.KAM.PaleyWiener LeanTheory.Theory.KAM.AnalyticComposition
  LeanTheory.Theory.KAM.CauchyTwoVar LeanTheory.Theory.KAM.FourierSumHolo
  LeanTheory.Fields

/-- `|eˣ − 1| ≤ e^{|x|} − 1`. -/
theorem abs_exp_sub_one_le (x : ℝ) : |Real.exp x - 1| ≤ Real.exp |x| - 1 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [Real.add_one_le_exp x])]
  · rw [abs_of_neg hx, abs_of_nonpos (by linarith [Real.exp_lt_one_iff.2 hx])]
    have h1 := Real.exp_pos x
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [sq_nonneg (Real.exp x - 1), Real.exp_pos (-x)]

/-- A complex mode differs from the mode at the real parts by at most `e^{ρ(|k|+|m|)} − 1` on
`|Im θ|, |Im ψ| ≤ ρ`. -/
theorem norm_fourierModeC_sub_re_le {ρ : ℝ} {θ ψ : ℂ} (hθ : |θ.im| ≤ ρ) (hψ : |ψ.im| ≤ ρ)
    (km : ℤ × ℤ) :
    ‖fourierModeC km θ ψ - fourierModeC km θ.re ψ.re‖ ≤ weight ρ km - 1 := by
  set x : ℝ := -((km.1 : ℝ) * θ.im + (km.2 : ℝ) * ψ.im)
  have e : fourierModeC km θ ψ = fourierModeC km θ.re ψ.re * (Real.exp x : ℂ) := by
    unfold fourierModeC
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im θ, ← Complex.re_add_im ψ]
    simp only [x]; push_cast; ring_nf; rw [I_sq]; ring
  have hn : ‖fourierModeC km θ.re ψ.re‖ = 1 := by
    unfold fourierModeC
    rw [show I * ((km.1 : ℂ) * (θ.re : ℂ) + (km.2 : ℂ) * (ψ.re : ℂ)) =
      ((km.1 * θ.re + km.2 * ψ.re : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [e, ← mul_sub_one, norm_mul, hn, one_mul, show (Real.exp x : ℂ) - 1 =
    ((Real.exp x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_exp_sub_one_le x).trans ?_
  unfold weight modeSize
  gcongr
  simp only [x, abs_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := abs_nonneg (km.1 : ℝ)
  have h2 := abs_nonneg (km.2 : ℝ)
  nlinarith [mul_le_mul_of_nonneg_left hθ h1, mul_le_mul_of_nonneg_left hψ h2]

/-- **Displacement under complexification**: for `u ∈ ℓ¹_ρ`, `ρ ≥ 0`, and
`|Im θ|, |Im ψ| ≤ ρ`, `|K(θ, ψ) − K(Re θ, Re ψ)| ≤ ‖u‖_ρ − ‖u‖_0`. -/
theorem norm_fourierSumC_sub_re_le {ρ : ℝ} (hρ : 0 ≤ ρ) {u : ℤ × ℤ → ℂ} (hu : InWeighted ρ u)
    {θ ψ : ℂ} (hθ : |θ.im| ≤ ρ) (hψ : |ψ.im| ≤ ρ) :
    ‖fourierSumC u θ ψ - fourierSumC u θ.re ψ.re‖ ≤ wnorm ρ u - wnorm 0 u := by
  have h0 : InWeighted 0 u := hu.mono hρ
  have hre : |(θ.re : ℂ).im| ≤ ρ := by simpa using hρ
  have hre' : |(ψ.re : ℂ).im| ≤ ρ := by simpa using hρ
  have hs : ∀ {a b : ℂ}, |a.im| ≤ ρ → |b.im| ≤ ρ →
      Summable fun km => u km * fourierModeC km a b := fun ha hb =>
    Summable.of_norm_bounded hu fun km => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_fourierModeC_le ha hb km) (norm_nonneg _)
  unfold fourierSumC
  rw [← (hs hθ hψ).tsum_sub (hs hre hre')]
  have hb : ∀ km, ‖u km * fourierModeC km θ ψ - u km * fourierModeC km θ.re ψ.re‖ ≤
      ‖u km‖ * weight ρ km - ‖u km‖ * weight 0 km := fun km => by
    rw [← mul_sub, norm_mul, ← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [show weight 0 km = 1 by simp [weight]]
    exact norm_fourierModeC_sub_re_le hθ hψ km
  have hsum : Summable fun km => ‖u km‖ * weight ρ km - ‖u km‖ * weight 0 km := hu.sub h0
  refine (norm_tsum_le_tsum_norm (hsum.of_norm_bounded fun km => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_norm]; exact hb km
  · refine (Summable.tsum_le_tsum hb (hsum.of_norm_bounded fun km => ?_) hsum).trans ?_
    · rw [Real.norm_eq_abs, abs_norm]; exact hb km
    · rw [hu.tsum_sub h0]; rfl

/-- Sanity: no displacement at real points. -/
theorem norm_fourierSumC_sub_re_zero (u : ℤ × ℤ → ℂ) (θ ψ : ℝ) :
    ‖fourierSumC u (θ : ℂ) (ψ : ℂ) - fourierSumC u (θ : ℂ).re (ψ : ℂ).re‖ = 0 := by
  simp

/-- **The `HoloData` hypotheses for a field composed with the torus map.** If `F : ℂ³ → ℂ` is
holomorphic and bounded by `M` on `U`, `u₁, u₂ ∈ ℓ¹_{ρ'}`, and the torus neighbourhood
`|Im θ|, |Im ψ| < ρ'`, `|zᵢ| < d'` is mapped into `U`, then `F ∘ torusMapC u₁ u₂` satisfies
`HoloData` (for `0 ≤ r < ρ < ρ'`, `0 < d < d'`). -/
theorem holoData_torus {F : CVec → ℂ} {U : Set CVec} {u₁ u₂ : ℤ × ℤ → ℂ}
    {ρ' ρ r d d' M : ℝ} (hF : DifferentiableOn ℂ F U) (hFb : ∀ y ∈ U, ‖F y‖ ≤ M)
    (hu₁ : InWeighted ρ' u₁) (hu₂ : InWeighted ρ' u₂)
    (hmap : ∀ θ ψ z₁ z₂ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → ‖z₁‖ < d' → ‖z₂‖ < d' →
      torusMapC u₁ u₂ θ ψ z₁ z₂ ∈ U)
    (hr0 : 0 ≤ r) (hr : r < ρ) (hρ : ρ < ρ') (hd : 0 < d) (hdd : d < d') :
    HoloData (fun θ ψ z₁ z₂ => F (torusMapC u₁ u₂ θ ψ z₁ z₂)) ρ' ρ r d d' M where
  holo := by
    refine hF.comp ((differentiableOn_torusMapC hu₁ hu₂).mono
      (prod_mono subset_rfl (subset_univ _))) ?_
    intro p hp
    exact hmap _ _ _ _ hp.1.1 hp.1.2 (mem_ball_zero_iff.1 hp.2.1) (mem_ball_zero_iff.1 hp.2.2)
  per1 θ ψ z₁ z₂ := by simp only [torusMapC_add_two_pi_left]
  per2 θ ψ z₁ z₂ := by simp only [torusMapC_add_two_pi_right]
  bound θ ψ z₁ z₂ hθ hψ h₁ h₂ := hFb _ (hmap _ _ _ _ (hθ.trans_lt hρ) (hψ.trans_lt hρ)
    (h₁.trans_lt hdd) (h₂.trans_lt hdd))
  r_nonneg := hr0
  r_lt := hr
  ρ_lt := hρ
  d_pos := hd
  d_lt := hdd

/-- **Analytic field along a complexified torus** (`AnaFieldAt.of_holomorphic` for
`F ∘ torusMapC`): under the hypotheses of `holoData_torus`,
`X(θ, ψ, z₁, z₂) = F(cylC (K₁(θ, ψ) + z₁, ψ, K₂(θ, ψ) + z₂))` is an analytic field along the
torus with strip `r` and majorant constant `M ((1+q)/(1-q))²`, `q = e^{-(ρ-r)}`. -/
def anaFieldAt_torus {F : CVec → ℂ} {U : Set CVec} {u₁ u₂ : ℤ × ℤ → ℂ}
    {ρ' ρ r d d' M : ℝ} (hF : DifferentiableOn ℂ F U) (hFb : ∀ y ∈ U, ‖F y‖ ≤ M)
    (hu₁ : InWeighted ρ' u₁) (hu₂ : InWeighted ρ' u₂)
    (hmap : ∀ θ ψ z₁ z₂ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → ‖z₁‖ < d' → ‖z₂‖ < d' →
      torusMapC u₁ u₂ θ ψ z₁ z₂ ∈ U)
    (hr0 : 0 ≤ r) (hr : r < ρ) (hρ : ρ < ρ') (hd : 0 < d) (hdd : d < d') :
    AnaFieldAt r (M * geoZ (Real.exp (-(ρ - r))) ^ 2) d
      (fun θ ψ z₁ z₂ => F (torusMapC u₁ u₂ θ ψ z₁ z₂)) :=
  AnaFieldAt.of_holomorphic (holoData_torus hF hFb hu₁ hu₂ hmap hr0 hr hρ hd hdd)
    fun _ _ _ _ _ _ => rfl

/-- Sanity fixture: a constant field on all of `ℂ³` along any torus is an analytic field. -/
def anaFieldAt_torus_const (c : ℂ) {u₁ u₂ : ℤ × ℤ → ℂ} (hu₁ : InWeighted 1 u₁)
    (hu₂ : InWeighted 1 u₂) :
    AnaFieldAt (1 / 4) (‖c‖ * geoZ (Real.exp (-(1 / 2 - 1 / 4))) ^ 2) 1
      (fun θ ψ z₁ z₂ => (fun _ : CVec => c) (torusMapC u₁ u₂ θ ψ z₁ z₂)) :=
  anaFieldAt_torus (U := univ) (d' := 2) (differentiableOn_const c) (fun _ _ => le_rfl) hu₁ hu₂
    (fun _ _ _ _ _ _ _ _ => mem_univ _) (by norm_num) (by norm_num) (by norm_num) one_pos
    one_lt_two

end LeanTheory.Theory.KAM.TorusFieldAna
