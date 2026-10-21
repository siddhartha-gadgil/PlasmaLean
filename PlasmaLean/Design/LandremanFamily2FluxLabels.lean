/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Coords
public import PlasmaLean.Design.LandremanFamily2Labels
public import PlasmaLean.Certificates.ValidatedQuadratureArcs
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Landreman family 2: volume, fluxes and current DERIVED from the field

`LandremanFamily2Labels` defines the labels of family 2 (`ε = 1/4`, `S = 4`) as primitives
of hand-derived one-dimensional integrands: `volK` (volume), `psiT`, `psiP` (toroidal and
poloidal flux over `2π`) and `curK` (`μ₀ I_tor/2π`). Here each of them is proved equal to the
corresponding physical quantity of the actual field, for `λ > 0` and every surface
`ψ = k₀²/2`, `0 ≤ k₀ < 19/20`:

* `volume_plasma`: the **Lebesgue volume** of the plasma `{x ∈ R | ψ(x) ≤ k₀²/2}`
  (`LandremanFamily2Coords.plasma`) is `volK λ (1/4) k₀`. Proof: change of variables
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) with the coordinate map, injective with
  Jacobian `k JacR` (`LandremanFamily2Coords`), Tonelli, and the exact angular integral
  `∫∫ JacR dχ dζ = Z E/(2λ)` (`integral_JacR`: the `ε cos 2ζ/(2h)` part of `G/h` integrates to
  zero by the substitution `u = sin 2ζ`).
* `torFlux_eq`: the **toroidal flux** `Φ_t = ∫∫ B · (∂_k x × ∂_χ x) dk dχ` through the toroidal
  cross-section `ζ = 0` (the half-plane `y = 0`, `x > 0`, bounded by the surface `ψ = k₀²/2`;
  flux of the actual `field` through the parametrized surface `(k, χ) ↦ x(k, χ, 0)`, with the
  actual partial derivatives `fderiv`) is `2π psiT λ (1/4) 4 k₀` (Landreman–Jorge: `2π ψ_t` is the
  toroidal flux).
* `polFlux_eq`: the **poloidal flux** `Φ_p = ∫∫ B · (∂_ζ x × ∂_k x) dk dζ` through the ribbon
  `χ = 0` spanned between the magnetic axis and the surface is `2π psiP λ (1/4) k₀`.
* `torCurrent_eq`: the **toroidal current** through the cross-section `ζ = 0`,
  `I_tor = ∫∫ J · (∂_k x × ∂_χ x)` with `J = (∇ × B)/μ₀` the actual current, satisfies
  `μ₀ I_tor/(2π) = curK λ (1/4) 4 k₀` (the Boozer `I` of Landreman–Jorge).

The pointwise inputs: at `ζ = 0` the triple product with `∂_k x × ∂_χ x` is
`V_y · a_c' (z_k σ_χ - z_χ σ_k) = V_y a_c' k/(λ cos λz T)` (`section_density`), with
`B_y = T/(2 b_c)` and `(μ₀J)_y = λ B_y + ∂ₓ Re v/λ`, `∂ₓ Re v = T h/b_c`; at `χ = 0`, `z_k = 0`
and `σ_k = 1/T` (`implicit_eqs`), so `B · (∂_ζ x × ∂_k x) = k G/(λ h T)`.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2FluxLabels

open Real Set MeasureTheory WithLp Filter Topology
open PlasmaLean.Fields PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanFamily2Surface PlasmaLean.Design.LandremanFamily2Rotated
open PlasmaLean.Design.LandremanFamily2Coords PlasmaLean.Design.LandremanFamily2Labels
open PlasmaLean.Certificates.ValidatedQuadrature (integral_comp_two_mul_periodic
  integral_periodic_shift)
open PlasmaLean.Design.LandremanEquilibrium (pr hasFDerivAt_pr)

/-! ## The angular integral of the Jacobian -/

section Angular
variable {lam k : ℝ}

/-- `JacR = 1/(2λ T cos λz) + (ε/2) cos 2ζ/(λ h T cos λz)` (from `G/h = 1/2 + ε cos 2ζ/(2h)`). -/
theorem JacR_split (lam k s1 c1 s2 c2 : ℝ) (hl : lam ≠ 0) (hk : k ^ 2 < 1)
    (h1 : s1 ^ 2 + c1 ^ 2 = 1) :
    JacR lam k s1 c1 s2 c2 = 1 / (2 * lam * Tc (1 / 4) k s2 * cc k s1) +
      c2 * (1 / 8 / (lam * hc (1 / 4) 4 k s1 c1 s2 * Tc (1 / 4) k s2 * cc k s1)) := by
  have hh := hc_pos (ε := 1 / 4) (k := k) (s1 := s1) (c1 := c1) (s2 := s2)
    (by norm_num : (2 : ℝ) ≤ 4)
  have hT := T_pos (ε := 1 / 4) (s2 := s2) hk
  have hc := cc_pos (k := k) h1 hk
  unfold JacR Gc
  field_simp
  ring

/-- `1/T(sin t)` is the `Z` integrand. -/
theorem inv_Tc_eq (k y : ℝ) : (Tc (1 / 4) k y)⁻¹ = fZ (1 / 4) k y := by
  unfold Tc chc nuc fZ tZ
  congr 3
  ring_nf

/-- `1/cos λz` is the `E` integrand. -/
theorem inv_cc_eq (k y : ℝ) : (cc k y)⁻¹ = fE k y := by
  unfold cc Yc fE
  rw [mul_pow]

/-- Continuity of `y ↦ 1/T(y)` (`k² < 1`). -/
theorem continuous_invT (hk : k ^ 2 < 1) : Continuous fun y => (Tc (1 / 4) k y)⁻¹ := by
  have : Continuous fun y => Tc (1 / 4) k y := by unfold Tc chc nuc; fun_prop
  exact this.inv₀ fun y => (T_pos hk).ne'

/-- Continuity of `y ↦ 1/cos λz` (`k² < 1`). -/
theorem continuous_invcc (hk : k ^ 2 < 1) : Continuous fun y => (cc k (Real.sin y))⁻¹ := by
  have : Continuous fun y => cc k (Real.sin y) := by unfold cc Yc; fun_prop
  exact this.inv₀ fun y => (cc_pos (Real.sin_sq_add_cos_sq y) hk).ne'

/-- `∫_{-π}^{π} dζ / T(sin 2ζ) = Z(k)`. -/
theorem integral_invT (hk : k ^ 2 < 1) :
    ∫ ζ in (-π)..π, (Tc (1 / 4) k (Real.sin (2 * ζ)))⁻¹ = Zint (1 / 4) k := by
  have hg : Continuous fun t => (Tc (1 / 4) k (Real.sin t))⁻¹ :=
    (continuous_invT hk).comp Real.continuous_sin
  have hp : Function.Periodic (fun t => (Tc (1 / 4) k (Real.sin t))⁻¹) (2 * π) := fun t => by
    simp only [Real.sin_add_two_pi]
  rw [integral_comp_two_mul_periodic hg hp, Zint]
  simp only [inv_Tc_eq]

/-- `∫_{-π}^{π} dχ / cos λz = E(k)`. -/
theorem integral_invcc (k : ℝ) : ∫ χ in (-π)..π, (cc k (Real.sin χ))⁻¹ = Eint k := by
  simp only [inv_cc_eq, Eint]

/-- **Odd part**: `∫_{-π}^{π} cos 2ζ · g(sin 2ζ) dζ = 0` for continuous `g` (substitution
`u = sin 2ζ`). -/
theorem integral_cos_two_mul_comp {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ ζ in (-π)..π, Real.cos (2 * ζ) * g (Real.sin (2 * ζ)) = 0 := by
  have hd : ∀ x ∈ uIcc (-π) π, HasDerivAt (fun ζ => Real.sin (2 * ζ)) (Real.cos (2 * x) * 2) x :=
    fun x _ => by
      simpa using ((hasDerivAt_id x).const_mul 2).sin
  have hc : ContinuousOn (fun x => Real.cos (2 * x) * 2) (uIcc (-π) π) := by fun_prop
  have h := intervalIntegral.integral_comp_mul_deriv hd hc hg
  have e1 : Real.sin (2 * -π) = 0 := by rw [mul_neg, Real.sin_neg, Real.sin_two_pi, neg_zero]
  have e2 : Real.sin (2 * π) = 0 := Real.sin_two_pi
  rw [e1, e2, intervalIntegral.integral_same] at h
  have h2 : ∫ ζ in (-π)..π, Real.cos (2 * ζ) * g (Real.sin (2 * ζ)) =
      (1 / 2) * ∫ ζ in (-π)..π, (g ∘ fun ζ => Real.sin (2 * ζ)) ζ * (Real.cos (2 * ζ) * 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext ζ; simp only [Function.comp_apply]; ring
  rw [h2, h, mul_zero]

/-- **Toroidal angular integral of the area element**:
`∫ JacR dζ = Z(k)/(2λ cos λz)` (the `ε cos 2ζ/(2h)` part of `G/h` integrates to zero). -/
theorem integral_JacR_zeta (hl : lam ≠ 0) (hk0 : 0 < k) (hk : k ^ 2 < 1) (χ : ℝ) :
    ∫ ζ in (-π)..π,
      JacR lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) =
      Zint (1 / 4) k * ((2 * lam)⁻¹ * (cc k (Real.sin χ))⁻¹) := by
  have h1 := Real.sin_sq_add_cos_sq χ
  simp only [JacR_split lam k _ _ _ _ hl hk h1]
  have hP : ParamOK (X := ℝ) (fun _ => Real.sin χ) (fun _ => Real.cos χ) id (fun _ => 0) k :=
    ⟨continuous_const, continuous_const, continuous_id, continuous_const, fun _ => h1,
      fun _ => by simp, hk0, hk⟩
  have hgc : Continuous fun y => 1 / 8 / (lam * hc (1 / 4) 4 k (Real.sin χ) (Real.cos χ) y *
      Tc (1 / 4) k y * cc k (Real.sin χ)) := by
    have hh := cont_h hP
    have hT := (cont_basic (k := k) hP).2.2.2.2.2.1
    refine continuous_const.div ((((continuous_const.mul hh).mul hT).mul continuous_const))
      (fun y => ?_)
    have e1 := hc_pos (ε := 1 / 4) (k := k) (s1 := Real.sin χ) (c1 := Real.cos χ) (s2 := y)
      (by norm_num : (2 : ℝ) ≤ 4)
    have e2 := T_pos (ε := 1 / 4) (s2 := y) hk
    have e3 := cc_pos (k := k) h1 hk
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hl e1.ne') e2.ne') e3.ne'
  have hA : IntervalIntegrable (fun ζ => 1 / (2 * lam * Tc (1 / 4) k (Real.sin (2 * ζ)) *
      cc k (Real.sin χ))) volume (-π) π := by
    refine Continuous.intervalIntegrable ?_ _ _
    have := (continuous_invT hk).comp (by fun_prop : Continuous fun ζ : ℝ => Real.sin (2 * ζ))
    have e : (fun ζ => 1 / (2 * lam * Tc (1 / 4) k (Real.sin (2 * ζ)) * cc k (Real.sin χ))) =
        fun ζ => (2 * lam)⁻¹ * (cc k (Real.sin χ))⁻¹ *
          ((fun y => (Tc (1 / 4) k y)⁻¹) ∘ fun ζ => Real.sin (2 * ζ)) ζ := by
      funext ζ; simp only [Function.comp_apply]; field_simp
    rw [e]; exact continuous_const.mul this
  have hB : IntervalIntegrable (fun ζ => Real.cos (2 * ζ) * (1 / 8 / (lam *
      hc (1 / 4) 4 k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) *
      Tc (1 / 4) k (Real.sin (2 * ζ)) * cc k (Real.sin χ)))) volume (-π) π :=
    (by fun_prop : Continuous fun ζ : ℝ => Real.cos (2 * ζ)).mul
      (hgc.comp (by fun_prop : Continuous fun ζ : ℝ => Real.sin (2 * ζ))) |>.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hA hB, integral_cos_two_mul_comp hgc, add_zero]
  have e : (fun ζ => 1 / (2 * lam * Tc (1 / 4) k (Real.sin (2 * ζ)) * cc k (Real.sin χ))) =
      fun ζ => (2 * lam)⁻¹ * (cc k (Real.sin χ))⁻¹ * (Tc (1 / 4) k (Real.sin (2 * ζ)))⁻¹ := by
    funext ζ; field_simp
  rw [e, intervalIntegral.integral_const_mul, integral_invT hk]
  ring

/-- **Angular integral of the area element**: `∫∫ JacR dχ dζ = Z(k) E(k)/(2λ)`. -/
theorem integral_JacR (hl : lam ≠ 0) (hk0 : 0 < k) (hk : k ^ 2 < 1) :
    ∫ χ in (-π)..π, ∫ ζ in (-π)..π,
        JacR lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) =
      Zint (1 / 4) k * Eint k / (2 * lam) := by
  simp only [integral_JacR_zeta hl hk0 hk]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_invcc]
  field_simp

end Angular

/-! ## The Lebesgue volume of the plasma -/

section Volume
variable {lam k₀ : ℝ}

/-- The coordinate box is measurable. -/
theorem measurableSet_coordDom (k₀ : ℝ) : MeasurableSet (coordDom k₀) := by
  have hc : ∀ i : Fin 3, Measurable fun p : Space => p i := fun i =>
    (PiLp.continuous_apply 2 _ i).measurable
  exact ((hc 0) measurableSet_Ioc).inter
    (((hc 1) measurableSet_Ioc).inter ((hc 2) measurableSet_Ioc))

/-- The identification `Space ≃ ℝ × ℝ × ℝ`, `p ↦ (p 0, p 1, p 2)`. -/
@[expose] def toTriple : Space ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow))

/-- `toTriple p = (p 0, p 1, p 2)`. -/
theorem toTriple_apply (p : Space) : toTriple p = (p 0, p 1, p 2) := rfl

/-- `toTriple` maps Lebesgue measure on `Space` to Lebesgue measure on `ℝ × ℝ × ℝ`. -/
theorem measurePreserving_toTriple : MeasurePreserving toTriple := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  exact (h3.comp h2).comp h1

/-- The volume density `k JacR` in the coordinates `(k, χ, ζ)`. -/
@[expose] def jacK (lam : ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  q.1 * JacR lam q.1 (Real.sin q.2.1) (Real.cos q.2.1) (Real.sin (2 * q.2.2))
    (Real.cos (2 * q.2.2))

/-- Measurability of the volume density. -/
theorem measurable_jacK (lam : ℝ) : Measurable fun q => ENNReal.ofReal (jacK lam q) := by
  simp only [jacK, JacR, Gc, hc, Tc, cc, sigc, sA, chc, shc, T0c, Yc, Xc, nuc]
  fun_prop

/-- **Change of variables for the volume**: `vol(shell) = ∫_box k JacR`. -/
theorem volume_shell_eq (hl : 0 < lam) (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    volume (shell lam k₀) = ∫⁻ p in coordDom k₀, ENNReal.ofReal (jacK lam (toTriple p)) := by
  rw [← image_coordMap hl hk0 hk₀.le, ← setLIntegral_one,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_coordDom k₀)
      (fun p hp => (hasFDerivAt_coordMap (lam := lam) (good_of_mem hk₀.le hp)).hasFDerivWithinAt)
      (injOn_coordMap hl hk₀.le)]
  refine setLIntegral_congr_fun (measurableSet_coordDom k₀) fun p hp => ?_
  have hg := good_of_mem hk₀.le hp
  rw [coordDeriv_det hl hg (lt_of_le_of_lt hp.1.2 hk₀), mul_one,
    abs_of_nonneg (mul_nonneg hg.1.le (JacP_pos hl hg).le)]
  rfl

/-- The angular integral of the density, as a lower Lebesgue integral. -/
theorem lintegral_angles (hl : 0 < lam) {k : ℝ} (hk : k ∈ Ioc 0 k₀) (hk₀ : k₀ < 19 / 20) :
    ∫⁻ y in Ioc (-π) π ×ˢ Ioc (-π) π, ENNReal.ofReal (jacK lam (k, y)) =
      ENNReal.ofReal (k * (Zint (1 / 4) k * Eint k / (2 * lam))) := by
  have hk0 := hk.1
  have hk1 : k ^ 2 < 1 := by nlinarith [hk.2]
  have hP : ParamOK (X := ℝ × ℝ) (fun y => Real.sin y.1) (fun y => Real.cos y.1)
      (fun y => Real.sin (2 * y.2)) (fun y => Real.cos (2 * y.2)) k :=
    ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop, fun y => Real.sin_sq_add_cos_sq _,
      fun y => Real.abs_cos_le_one _, hk0, hk1⟩
  have hcont : Continuous fun y : ℝ × ℝ => jacK lam (k, y) :=
    continuous_const.mul (cont_JacR hP hl.ne')
  have hint : IntegrableOn (fun y : ℝ × ℝ => jacK lam (k, y)) (Ioc (-π) π ×ˢ Ioc (-π) π) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    have hint' := hint
    rw [Measure.volume_eq_prod] at hint' ⊢
    rw [setIntegral_prod _ hint']
    have hpi : -π ≤ π := by linarith [Real.pi_pos]
    rw [← intervalIntegral.integral_of_le hpi]
    have e : ∀ χ : ℝ, ∫ ζ in Ioc (-π) π, jacK lam (k, (χ, ζ)) =
        k * ∫ ζ in (-π)..π, JacR lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))
          (Real.cos (2 * ζ)) := fun χ => by
      rw [intervalIntegral.integral_of_le hpi, ← integral_const_mul]; rfl
    simp only [e]
    rw [intervalIntegral.integral_const_mul, integral_JacR hl.ne' hk0 hk1]
  · filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with y hy
    exact mul_nonneg hk0.le (JacP_pos (p := toLp 2 ![k, y.1, y.2]) hl
      ⟨by simpa using hk0, by simpa using hk.2.trans hk₀.le⟩).le |>.trans_eq (by
        simp [jacK, JacP])

/-- **The Lebesgue volume of the plasma shell is `volK`.** -/
theorem volume_shell (hl : 0 < lam) (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    volume (shell lam k₀) = ENNReal.ofReal (volK lam (1 / 4) k₀) := by
  rw [volume_shell_eq hl hk0 hk₀]
  have hD : coordDom k₀ = toTriple ⁻¹' (Ioc 0 k₀ ×ˢ (Ioc (-π) π ×ˢ Ioc (-π) π)) := by
    ext p; simp [coordDom, toTriple_apply]
  rw [hD, measurePreserving_toTriple.setLIntegral_comp_preimage_emb toTriple.measurableEmbedding
    (fun q => ENNReal.ofReal (jacK lam q)) _, Measure.volume_eq_prod,
    setLIntegral_prod _ (measurable_jacK lam).aemeasurable]
  rw [setLIntegral_congr_fun measurableSet_Ioc (fun k hk => lintegral_angles hl hk hk₀)]
  have hcont : ContinuousOn (fun k => k * (Zint (1 / 4) k * Eint k / (2 * lam))) (Icc 0 k₀) := by
    refine (continuousOn_id.mul ((continuousOn_Zint.mul continuousOn_Eint).div_const _)).mono ?_
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [← ofReal_integral_eq_lintegral_ofReal ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self)]
  · rw [volK, intervalIntegral.integral_of_le hk0]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have := Zint_pos (ε := 1 / 4) hx1
    have := Eint_pos hx1
    have := hx.1
    positivity

/-- `volK ≥ 0`. -/
theorem volK_nonneg (hl : 0 < lam) (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    0 ≤ volK lam (1 / 4) k₀ := by
  unfold volK
  refine intervalIntegral.integral_nonneg hk0 fun x hx => ?_
  have hx1 : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have := Zint_pos (ε := 1 / 4) hx1
  have := Eint_pos hx1
  have := hx.1
  positivity

/-- **The Lebesgue volume of the plasma `{x ∈ R | ψ(x) ≤ k₀²/2}` is `volK λ (1/4) k₀`**
(`0 ≤ k₀ < 19/20`, `λ > 0`): the volume label of `family2Data` is derived from the field. -/
theorem volume_plasma (hl : 0 < lam) (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    volume (plasma lam k₀) = ENNReal.ofReal (volK lam (1 / 4) k₀) := by
  rw [measure_congr (plasma_ae_eq_shell hl.ne' k₀), volume_shell hl hk0 hk₀]

/-- Real-valued form of `volume_plasma`. -/
theorem volumeReal_plasma (hl : 0 < lam) (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    (volume (plasma lam k₀)).toReal = volK lam (1 / 4) k₀ := by
  rw [volume_plasma hl hk0 hk₀, ENNReal.toReal_ofReal (volK_nonneg hl hk0 hk₀)]

end Volume

/-! ## Fluxes through parametrized surfaces -/

open Matrix in
/-- The flux density `V · (a × b)` of a vector field value `V` through the oriented area element
spanned by `a`, `b` (Mathlib's cross product `⨯₃`). -/
@[expose] def fluxDensity (V a b : Space) : ℝ := ofLp V ⬝ᵥ (ofLp a ⨯₃ ofLp b)

open Matrix in
/-- The triple product in coordinates. -/
theorem fluxDensity_eq (V a b : Space) : fluxDensity V a b =
    V 0 * (a 1 * b 2 - a 2 * b 1) + V 1 * (a 2 * b 0 - a 0 * b 2) +
      V 2 * (a 0 * b 1 - a 1 * b 0) := by
  simp [fluxDensity, cross_apply, dotProduct, Fin.sum_univ_three]

/-- The coordinate point `(k, χ, ζ)`. -/
@[expose] def pt (k χ ζ : ℝ) : Space := toLp 2 ![k, χ, ζ]

/-- Components of the coordinate point. -/
@[simp] theorem pt_0 (k χ ζ : ℝ) : pt k χ ζ 0 = k := by simp [pt]
/-- Components of the coordinate point. -/
@[simp] theorem pt_1 (k χ ζ : ℝ) : pt k χ ζ 1 = χ := by simp [pt]
/-- Components of the coordinate point. -/
@[simp] theorem pt_2 (k χ ζ : ℝ) : pt k χ ζ 2 = ζ := by simp [pt]

/-- The actual partial derivative `∂x/∂(k, χ, ζ)_j` of the coordinate map (`fderiv`). -/
@[expose] def dX (lam : ℝ) (j : Fin 3) (k χ ζ : ℝ) : Space :=
  fderiv ℝ (coordMap lam) (pt k χ ζ) (basis j)

/-- **Toroidal flux** through the toroidal cross-section `ζ = 0` (the half-plane `y = 0`,
`x > 0`) inside the surface `ψ = k₀²/2`: the flux of the actual field through the parametrized
surface `(k, χ) ↦ x(k, χ, 0)`, oriented by `∂_k x × ∂_χ x`. -/
@[expose] def torFlux (lam k₀ : ℝ) : ℝ :=
  ∫ k in (0 : ℝ)..k₀, ∫ χ in (-π)..π,
    fluxDensity (field (1 / 4) 4 lam (coordMap lam (pt k χ 0))) (dX lam 0 k χ 0) (dX lam 1 k χ 0)

/-- **Poloidal flux** through the ribbon `χ = 0` spanned between the magnetic axis (`k = 0`)
and the surface `ψ = k₀²/2`, oriented by `∂_ζ x × ∂_k x`. -/
@[expose] def polFlux (lam k₀ : ℝ) : ℝ :=
  ∫ k in (0 : ℝ)..k₀, ∫ ζ in (-π)..π,
    fluxDensity (field (1 / 4) 4 lam (coordMap lam (pt k 0 ζ))) (dX lam 2 k 0 ζ) (dX lam 0 k 0 ζ)

/-- **Toroidal current** through the cross-section `ζ = 0`: the flux of the actual current
density `J = (∇ × B)/μ₀`. -/
@[expose] def torCurrent (μ₀ lam k₀ : ℝ) : ℝ :=
  ∫ k in (0 : ℝ)..k₀, ∫ χ in (-π)..π,
    fluxDensity (current μ₀ (1 / 4) 4 lam (coordMap lam (pt k χ 0))) (dX lam 0 k χ 0)
      (dX lam 1 k χ 0)

section Flux
variable {lam : ℝ}

/-- Columns of the Jacobian matrix. -/
theorem coordDeriv_basis (lam : ℝ) (p : Space) (i j : Fin 3) :
    coordDeriv lam p (basis j) i = jacMatrix lam p i j := by
  rw [coordDeriv_apply]
  fin_cases j <;> simp

/-- The partial derivatives are the columns of `jacMatrix` (good range). -/
theorem dX_eq {k χ ζ : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) (j i : Fin 3) :
    dX lam j k χ ζ i = jacMatrix lam (pt k χ ζ) i j := by
  rw [dX, (hasFDerivAt_coordMap (lam := lam) (p := pt k χ ζ) ⟨by simpa using hk0,
    by simpa using hk1⟩).fderiv, coordDeriv_basis]

/-- Entries of the Jacobian matrix. -/
theorem jac_entries (lam : ℝ) (p : Space) :
    jacMatrix lam p 0 0 = daC (sigP p) * Real.cos (p 2) * fderiv ℝ sigP p (basis 0) ∧
    jacMatrix lam p 0 1 = daC (sigP p) * Real.cos (p 2) * fderiv ℝ sigP p (basis 1) ∧
    jacMatrix lam p 0 2 = daC (sigP p) * Real.cos (p 2) * fderiv ℝ sigP p (basis 2) -
      aC (1 / 4) (sigP p) * Real.sin (p 2) ∧
    jacMatrix lam p 1 0 = dbC (sigP p) * Real.sin (p 2) * fderiv ℝ sigP p (basis 0) ∧
    jacMatrix lam p 1 1 = dbC (sigP p) * Real.sin (p 2) * fderiv ℝ sigP p (basis 1) ∧
    jacMatrix lam p 1 2 = dbC (sigP p) * Real.sin (p 2) * fderiv ℝ sigP p (basis 2) +
      bC (1 / 4) (sigP p) * Real.cos (p 2) ∧
    jacMatrix lam p 2 0 = zk lam p ∧ jacMatrix lam p 2 1 = zchi lam p ∧ jacMatrix lam p 2 2 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Components of the field: `B_y = (Re u α - Im u β)/(2|P|²)`, `B_z = -Re v/λ`. -/
theorem field_12 (lam : ℝ) (x : Space) :
    field (1 / 4) 4 lam x 1 = (uR (1 / 4) 4 lam x * al (1 / 4) x -
      uI (1 / 4) 4 lam x * be (1 / 4) x) / (2 * Mq (1 / 4) x) ∧
    field (1 / 4) 4 lam x 2 = -vR (1 / 4) 4 lam x / lam := by
  constructor <;> simp [field]

/-- **Flux density through the section `ζ = 0`**:
`V · (∂_k x × ∂_χ x) = V_y a_c' k/(λ cos λz T)`. -/
theorem section_density (hl : 0 < lam) {k χ : ℝ} (hk0 : 0 < k) (hk1 : k < 19 / 20) (V : Space) :
    fluxDensity V (dX lam 0 k χ 0) (dX lam 1 k χ 0) =
      V 1 * daC (sigP (pt k χ 0)) * (k / (lam * ccP (pt k χ 0) * TP (pt k χ 0))) := by
  have hg : Good (pt k χ 0) := ⟨by simpa using hk0, by simpa using hk1.le⟩
  have key := zk_mul_sub hl.ne' hg (by simpa using hk1)
  obtain ⟨j00, j01, -, j10, j11, -, j20, j21, -⟩ := jac_entries lam (pt k χ 0)
  rw [fluxDensity_eq]
  simp only [dX_eq hk0 hk1.le, j00, j01, j10, j11, j20, j21, pt_2, Real.sin_zero, Real.cos_zero,
    mul_zero, mul_one, zero_mul, sub_zero, add_zero]
  rw [pt_0] at key
  rw [← key]
  ring

/-- Values at the point `x(k, χ, 0)`: `x = a_c(σ)`, `y = 0`, `ν = 0`. -/
theorem atoms_section (k χ : ℝ) :
    coordMap lam (pt k χ 0) 0 = aC (1 / 4) (sigP (pt k χ 0)) ∧ coordMap lam (pt k χ 0) 1 = 0 ∧
      nu (1 / 4) (coordMap lam (pt k χ 0)) = 0 ∧
      sg (1 / 4) (coordMap lam (pt k χ 0)) = sigP (pt k χ 0) := by
  refine ⟨by simp, by simp, ?_, sg_coordMap lam _⟩
  rw [nu_coordMap, nuc]; simp

/-- `B_y a_c' = T/(2h)` on the section `ζ = 0`. -/
theorem field_section (hl : 0 < lam) {k χ : ℝ} (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    field (1 / 4) 4 lam (coordMap lam (pt k χ 0)) 1 * daC (sigP (pt k χ 0)) =
      TP (pt k χ 0) / (2 * hC (1 / 4) (sigP (pt k χ 0))) := by
  have hg : Good (pt k χ 0) := ⟨by simpa using hk0, by simpa using hk1.le⟩
  obtain ⟨h0, h1, hn, hs⟩ := atoms_section (lam := lam) k χ
  have hT := (atoms_coordMap hl.ne' hg).1
  have hσ := sigP_pos (pt k χ 0)
  have ha := aC_pos (ε := 1 / 4) hσ
  have hh : 0 < hC (1 / 4) (sigP (pt k χ 0)) := lt_of_le_of_lt (abs_nonneg _) (hC_gt hσ)
  simp only [(field_12 lam _).1, al, be, Mq, hT, h0, h1, hn, hs, daC]
  field_simp
  ring

/-- `Δ_y a_c' = T/λ` on the section `ζ = 0` (`∂ₓ Re v = T h/b_c`). -/
theorem Delta_section (hl : 0 < lam) {k χ : ℝ} (hk0 : 0 < k) (hk1 : k < 19 / 20) :
    PlasmaLean.Design.LandremanFamily2Surface.Delta (1 / 4) 4 lam (coordMap lam (pt k χ 0)) 1 *
      daC (sigP (pt k χ 0)) = TP (pt k χ 0) / lam := by
  have hg : Good (pt k χ 0) := ⟨by simpa using hk0, by simpa using hk1.le⟩
  obtain ⟨h0, h1, hn, hs⟩ := atoms_section (lam := lam) k χ
  have hT := (atoms_coordMap hl.ne' hg).1
  have hσ := sigP_pos (pt k χ 0)
  have ha := aC_pos (ε := 1 / 4) hσ
  have hb := bC_pos (ε := 1 / 4) hσ
  have hab := aC_mul_bC (ε := 1 / 4) hσ
  have ha2 := aC_sq (ε := 1 / 4) hσ
  have hb2 := bC_sq (ε := 1 / 4) hσ
  have hh : 0 < hC (1 / 4) (sigP (pt k χ 0)) := lt_of_le_of_lt (abs_nonneg _) (hC_gt hσ)
  have hD : PlasmaLean.Design.LandremanFamily2Surface.Delta (1 / 4) 4 lam
      (coordMap lam (pt k χ 0)) 1 =
        lam⁻¹ * dvR (1 / 4) 4 lam (coordMap lam (pt k χ 0)) (basis 0) := by
    simp [PlasmaLean.Design.LandremanFamily2Surface.Delta]
  rw [hD, dvR_basis0]
  simp only [cp, cm, al, be, Mq, r2, hT, h0, h1, hn, hs, daC]
  have e : aC (1 / 4) (sigP (pt k χ 0)) ^ 2 + bC (1 / 4) (sigP (pt k χ 0)) ^ 2 =
      hC (1 / 4) (sigP (pt k χ 0)) := by rw [ha2, hb2]; ring
  generalize aC (1 / 4) (sigP (pt k χ 0)) = a at *
  generalize bC (1 / 4) (sigP (pt k χ 0)) = b at *
  generalize hC (1 / 4) (sigP (pt k χ 0)) = H at *
  generalize sigP (pt k χ 0) = σ at *
  subst hab e
  field_simp
  ring

/-- The `F₁` integrand in the angle `χ` of the section `ζ = 0` (shift `χ = t + π/2`). -/
theorem integral_section (k : ℝ) (hk : k ^ 2 < 1) :
    ∫ χ in (-π)..π, (hC (1 / 4) (sigP (pt k χ 0)) * ccP (pt k χ 0))⁻¹ = F1 (1 / 4) 4 k := by
  set f : ℝ → ℝ := fun χ => (hc (1 / 4) 4 k (Real.sin χ) (Real.cos χ) 0 * cc k (Real.sin χ))⁻¹
  have e1 : ∀ χ, (hC (1 / 4) (sigP (pt k χ 0)) * ccP (pt k χ 0))⁻¹ = f χ := fun χ => by
    simp [f, sigP, ccP, hc, hC]
  simp only [e1]
  have hp : Function.Periodic f (2 * π) := fun χ => by
    simp only [f, Real.sin_add_two_pi, Real.cos_add_two_pi]
  rw [← integral_periodic_shift hp (π / 2), F1]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [f, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two, fF1]
  have hcc : cc k (Real.cos t) = cK k (Real.sin t) := by
    unfold cc Yc cK; congr 1; have := Real.sin_sq_add_cos_sq t
    linear_combination (-k ^ 2) * this
  have hcpos : 0 < cK k (Real.sin t) := cK_pos hk
  have hsig : sigc (1 / 4) 4 k (Real.cos t) (-Real.sin t) 0 = sigF 4 k (Real.sin t) := by
    unfold sigc sigF sA
    have hT0 : T0c (1 / 4) k (Real.cos t) 0 = cc k (Real.cos t) ^ 2 := by
      unfold T0c chc nuc; rw [cc_sq (Real.cos_sq_add_sin_sq t) hk]; simp
    rw [hT0, hcc]
    simp only [chc, shc, nuc, mul_zero, Real.cosh_zero, Real.sinh_zero, Xc]
    have e : (cK k (Real.sin t) * 1 * (k * -Real.sin t) + 0 * Tc (1 / 4) k 0) /
        cK k (Real.sin t) ^ 2 = -(k * Real.sin t / cK k (Real.sin t)) := by
      field_simp; ring
    rw [e, Real.arcsin_neg]
    ring
  rw [hcc]
  unfold hc hfun
  rw [hsig]

/-- **The toroidal flux is `2π ψ_t`**: `Φ_t(k₀) = 2π psiT λ (1/4) 4 k₀` (`λ > 0`,
`0 ≤ k₀ < 19/20`). -/
theorem torFlux_eq (hl : 0 < lam) {k₀ : ℝ} (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    torFlux lam k₀ = 2 * π * psiT lam (1 / 4) 4 k₀ := by
  unfold torFlux psiT
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun k hk => ?_)
  rw [uIoc_of_le hk0] at hk
  have hk1 : k < 19 / 20 := lt_of_le_of_lt hk.2 hk₀
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1]
  have e : ∀ χ, fluxDensity (field (1 / 4) 4 lam (coordMap lam (pt k χ 0))) (dX lam 0 k χ 0)
      (dX lam 1 k χ 0) = k / (2 * lam) * (hC (1 / 4) (sigP (pt k χ 0)) * ccP (pt k χ 0))⁻¹ :=
    fun χ => by
      have hT : 0 < TP (pt k χ 0) := T_pos (by simpa using hk2)
      have hc := ccP_pos (p := pt k χ 0) (by simpa using hk2)
      have hσ := sigP_pos (pt k χ 0)
      have hh : 0 < hC (1 / 4) (sigP (pt k χ 0)) := lt_of_le_of_lt (abs_nonneg _) (hC_gt hσ)
      rw [section_density hl hk.1 hk1, field_section hl hk.1 hk1]
      field_simp
  simp only [e]
  rw [intervalIntegral.integral_const_mul, integral_section k hk2]
  field_simp
  ring

/-- **The poloidal flux is `2π ψ_p`**: `Φ_p(k₀) = 2π psiP λ (1/4) k₀`. -/
theorem polFlux_eq (hl : 0 < lam) {k₀ : ℝ} (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    polFlux lam k₀ = 2 * π * psiP lam (1 / 4) k₀ := by
  unfold polFlux psiP
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun k hk => ?_)
  rw [uIoc_of_le hk0] at hk
  have hk1 : k < 19 / 20 := lt_of_le_of_lt hk.2 hk₀
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1]
  have e : ∀ ζ, fluxDensity (field (1 / 4) 4 lam (coordMap lam (pt k 0 ζ))) (dX lam 2 k 0 ζ)
      (dX lam 0 k 0 ζ) = k * JacR lam k (Real.sin 0) (Real.cos 0) (Real.sin (2 * ζ))
        (Real.cos (2 * ζ)) := fun ζ => by
    have hg : Good (pt k 0 ζ) := ⟨by simpa using hk.1, by simpa using hk1.le⟩
    have hT := T_pos (ε := 1 / 4) (s2 := Real.sin (2 * ζ)) hk2
    have hσ := sigP_pos (pt k 0 ζ)
    have hh : 0 < hC (1 / 4) (sigP (pt k 0 ζ)) := lt_of_le_of_lt (abs_nonneg _) (hC_gt hσ)
    have hv := (atoms_coordMap hl.ne' hg).2
    have himp := (implicit_eqs hl.ne' hg (by simpa using hk1)).1
    have hzk : zk lam (pt k 0 ζ) = 0 := by simp [zk]
    rw [hzk, mul_zero, zero_add] at himp
    have hcomb := daC_comb (sigP (pt k 0 ζ)) ζ hσ
    have hcc1 : cc k (Real.sin 0) = 1 := by simp [cc, Yc]
    have hT' : 0 < TP (pt k 0 ζ) := T_pos (by simpa using hk2)
    have hL : fderiv ℝ sigP (pt k 0 ζ) (basis 0) = (TP (pt k 0 ζ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left; rw [mul_comm, himp]; simp
    obtain ⟨j00, -, j02, j10, -, j12, j20, -, j22⟩ := jac_entries lam (pt k 0 ζ)
    calc fluxDensity (field (1 / 4) 4 lam (coordMap lam (pt k 0 ζ))) (dX lam 2 k 0 ζ)
          (dX lam 0 k 0 ζ)
        = k / lam * fderiv ℝ sigP (pt k 0 ζ) (basis 0) *
          (daC (sigP (pt k 0 ζ)) * Real.cos ζ * (bC (1 / 4) (sigP (pt k 0 ζ)) * Real.cos ζ) +
            dbC (sigP (pt k 0 ζ)) * Real.sin ζ * (aC (1 / 4) (sigP (pt k 0 ζ)) * Real.sin ζ)) := by
          rw [fluxDensity_eq]
          simp only [dX_eq hk.1 hk1.le, j00, j02, j10, j12, j20, j22, hzk, pt_2,
            (field_12 lam _).2, hv, pt_0, pt_1, Real.cos_zero]
          ring
      _ = k * JacR lam k (Real.sin 0) (Real.cos 0) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
          rw [hcomb, hL]
          unfold JacR Gc
          rw [hcc1]
          change _ = k * ((hC (1 / 4) (sigP (pt k 0 ζ)) + 1 / 4 * Real.cos (2 * ζ)) / 2 /
            (lam * hC (1 / 4) (sigP (pt k 0 ζ)) * TP (pt k 0 ζ) * 1))
          field_simp
  simp only [e]
  rw [intervalIntegral.integral_const_mul, integral_JacR_zeta hl.ne' hk.1 hk2 0]
  simp only [Real.sin_zero, cc, Yc, mul_zero, zero_pow two_ne_zero, sub_zero, Real.sqrt_one,
    inv_one, mul_one]
  field_simp
  ring

/-- **The enclosed toroidal current gives the Boozer `I`**: `μ₀ I_tor(k₀)/(2π) = curK λ (1/4) 4 k₀`
(`μ₀ ≠ 0`, `λ > 0`, `0 ≤ k₀ < 19/20`). -/
theorem torCurrent_eq (hl : 0 < lam) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) {k₀ : ℝ} (hk0 : 0 ≤ k₀)
    (hk₀ : k₀ < 19 / 20) :
    μ₀ * torCurrent μ₀ lam k₀ / (2 * π) = curK lam (1 / 4) 4 k₀ := by
  unfold torCurrent curK
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun k hk => ?_)
  rw [uIoc_of_le hk0] at hk
  have hk1 : k < 19 / 20 := lt_of_le_of_lt hk.2 hk₀
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1]
  have e : ∀ χ, μ₀ * fluxDensity (current μ₀ (1 / 4) 4 lam (coordMap lam (pt k χ 0)))
      (dX lam 0 k χ 0) (dX lam 1 k χ 0) =
      k / 2 * (hC (1 / 4) (sigP (pt k χ 0)) * ccP (pt k χ 0))⁻¹ +
        k / lam ^ 2 * (cc k (Real.sin χ))⁻¹ := fun χ => by
    have hT : 0 < TP (pt k χ 0) := T_pos (by simpa using hk2)
    have hc := ccP_pos (p := pt k χ 0) (by simpa using hk2)
    have hσ := sigP_pos (pt k χ 0)
    have hh : 0 < hC (1 / 4) (sigP (pt k χ 0)) := lt_of_le_of_lt (abs_nonneg _) (hC_gt hσ)
    have hJ := smul_current (ε := 1 / 4) (S := 4) hl.ne' hμ (coordMap_mem_U lam (pt k χ 0))
    have hJ1 : μ₀ * current μ₀ (1 / 4) 4 lam (coordMap lam (pt k χ 0)) 1 =
        lam * field (1 / 4) 4 lam (coordMap lam (pt k χ 0)) 1 +
          PlasmaLean.Design.LandremanFamily2Surface.Delta (1 / 4) 4 lam
            (coordMap lam (pt k χ 0)) 1 := by
      have := congrArg (fun v : Space => v 1) hJ
      simpa using this
    rw [section_density hl hk.1 hk1, ← mul_assoc, ← mul_assoc, hJ1, add_mul, add_mul,
      mul_assoc lam, field_section hl hk.1 hk1, Delta_section hl hk.1 hk1]
    have hcc : ccP (pt k χ 0) = cc k (Real.sin χ) := by simp [ccP]
    rw [hcc] at hc ⊢
    field_simp
  have hint1 : IntervalIntegrable (fun χ => k / 2 * (hC (1 / 4) (sigP (pt k χ 0)) *
      ccP (pt k χ 0))⁻¹) volume (-π) π := by
    refine (continuous_const.mul ?_).intervalIntegrable _ _
    have hP : ParamOK (X := ℝ) Real.sin Real.cos (fun _ => 0) (fun _ => 1) k :=
      ⟨Real.continuous_sin, Real.continuous_cos, continuous_const, continuous_const,
        Real.sin_sq_add_cos_sq, fun _ => by simp, hk.1, hk2⟩
    have h1 := cont_h hP
    have h2 := (cont_basic (k := k) hP).2.2.1
    refine Continuous.congr ((h1.mul h2).inv₀ fun χ => ?_) fun χ => ?_
    · exact mul_ne_zero (hc_pos (ε := 1 / 4) (k := k) (s1 := Real.sin χ) (c1 := Real.cos χ)
        (s2 := 0) (by norm_num : (2 : ℝ) ≤ 4)).ne'
        (cc_pos (k := k) (Real.sin_sq_add_cos_sq χ) hk2).ne'
    · simp [sigP, ccP, hc, hC]
  have hint2 : IntervalIntegrable (fun χ => k / lam ^ 2 * (cc k (Real.sin χ))⁻¹) volume (-π) π :=
    (continuous_const.mul (continuous_invcc hk2)).intervalIntegrable _ _
  have e' : ∀ χ, (hC (1 / 4) (sigP (pt k χ 0)) * ccP (pt k χ 0))⁻¹ =
      (hc (1 / 4) 4 k (Real.sin χ) (Real.cos χ) 0 * cc k (Real.sin χ))⁻¹ := fun χ => by
    simp [sigP, ccP, hc, hC]
  rw [← intervalIntegral.integral_const_mul]
  simp only [e]
  rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_section k hk2, integral_invcc]
  ring

end Flux

end PlasmaLean.Design.LandremanFamily2FluxLabels
