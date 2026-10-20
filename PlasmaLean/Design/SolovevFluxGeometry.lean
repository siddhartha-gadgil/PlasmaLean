/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevFluxQuadrature
public import PlasmaLean.Design.SolovevMercierCertified
public import PlasmaLean.Design.SolovevBand
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The actual flux-surface geometry of the reactor Solov'ev field

`SolovevBand.solovev_one_plasma` was proved for every geometry in the SUPPLIED class
`SolovevBand.IsSolovevGeometry` (flux-geometry laws, `0.49 s ≤ g ≤ 0.525 s`,
`0.49 ≤ h ≤ 0.525`, `h` continuous), of which only a model instance existed. This module
constructs the geometry of the actual reactor Solov'ev field and proves it is an instance.

## Construction (`solovevFluxGeometry`)

Transport label `s = ψ̃/ψ̃_b` (`SolovevOnePlasma.label`, `ψ̃_b = (11/12) ψ̃_e`). The surface of
label `s` is the exact meridian curve `SolovevMercierCertified.surfPt σ t` with
`σ = √(ψ̃_b s)` (`sig`), on which `label = s` (`label_surfPt`). With
`surfInt f s = π √2 ψ̃_b ∫_{-π}^{π} f(x(t))/R(t) dt`:

* `V'(s) = surfInt 1` (`Vp`), `V' g = surfInt |∇s|²` (`VG`, actual gradient
  `Solovev.psiTGrad`), `V' h = surfInt Δs` (`VH`, `Δψ̃ = 2z² + 5R² - 2L²`, `lapPsiT`);
* `g = VG/V'`, `h = VH/V'`, `V'' = dVp` and `g' = dgS` in closed form.

Exact reductions (`Vp_eq`, `VG_eq`, `VH_eq`; `ε = σ/50`, `ε² = 11 s/48`):
`V' = (π√2 ψ̃_b/10) Pn(ε)`, `V'g = 10π√2 s IGn(ε)`, `V'h = 10π√2 IHn(ε)`, hence
`g = (48/275) s IGn/Pn`, `h = (48/275) IHn/Pn` (`gS_eq`, `hS_eq`).

## Laws (all proved: `solovevFluxGeometry_laws`)

* `V' > 0`; `g(0) = 0` (the factor `s`).
* `V'' = dVp`: differentiation under the integral sign (`hasDerivAt_integral_sin`, uniform
  bound by compactness), an integration by parts `∂_t(cos t · v^{-3/2})` (`dPn_eq`) removes
  the `1/ε` of the chain rule, so `dVp = π√2 ψ̃_b²/10⁵ · S3c(ε)` with `S3c` continuous at the
  axis.
* **Gauss identity** `(V' g)' = V' h` (`hasDerivAt_VG`): from `IGn + (ε/2) IGn' = IHn`
  (`gauss_eps`), which is `∫ ∂_t (cos t · φ(ε, sin t) · v^{-3/2}) dt = 0` for the explicit
  `φ = -ε - ((ε²+2)/2) y + (ε²/2) y³` (`gauss_pointwise`, an exact algebraic identity): the
  divergence theorem on the Solov'ev surfaces, proved, not supplied.
* **The axis** `s = 0`: `σ = √(ψ̃_b s)` is not differentiable at `0`, but the derivative
  formulas extend continuously, so the one-sided derivatives at `s = 0` exist and equal them
  (Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv`; `hasDerivWithinAt_Vp_zero`,
  `hasDerivWithinAt_VG_zero`). Nothing is singular in the label `s`.

## Enclosures (`solovevFluxGeometry_isSolovev`)

`SolovevFluxQuadrature.flux_ratio_bounds`: `539/192 ≤ IGn/Pn, IHn/Pn ≤ 385/128` for every
`ε ∈ [0, 12/25] ⊇ [0, √(11/48)]`, by pointwise polynomial enclosures of `v^{-3/2}` and exact
Wallis integration (all kernel-checked). The certified margins are thin but genuine: true
`g/s`, `h` range over `[0.4953, 0.5236]`, `[0.4914, 0.5236]`, axis value `144/275`
(`hS_zero`, `dgS_zero`).

## Main results

* `solovevFluxGeometry_isSolovev : IsSolovevGeometry solovevFluxGeometry`.
* `solovev_one_plasma_actual`: `solovev_one_plasma` with `G := solovevFluxGeometry`.

## Links to the field, and the remaining modelling link

Proved: `lapPsiT_eq_laplacian` (`lapPsiT` is the sum of the Cartesian second derivatives of
`ψ̃`); `surface_weight_eq` / `surfInt_eq_area` (the weight `π√2 ψ̃_b/R dt` IS `dS/|∇s|` with
`dS = 2π R |∂_t(R,z)| dt` of the actual curve and the actual `|∇s|`); `hasDerivAt_volume`
(`V'(s) = d/ds volS(σ(s))` for the coordinate volume `volS` of `SolovevMercierCertified`).

**Not formalized (stated modelling link):** the coarea formula `d/ds ∫_{s' ≤ s} f dV =
∮ f dS/|∇s|` (hence that `g`, `h` are the flux-surface averages entering the transport
equation `(1/V') ∂_s(V' χ ⟨|∇s|²⟩ ∂_s T)`), and the measure-theoretic identification of
`volS` with the Lebesgue volume (the 2-D change of variables with the proved Jacobian
`SolovevMercierCertified.jacobian_eq`), exactly as in `SolovevMercierCertified`. The
transport model itself (quasilinear `χ`, prescribed density and sources) is unchanged from
`SolovevBand`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevFluxGeometry

open Real Set MeasureTheory intervalIntegral Filter Topology PlasmaLean.Certificates
open PlasmaLean.Fields PlasmaLean.Transport PlasmaLean.Design.Solovev
open PlasmaLean.Design.SolovevMercier PlasmaLean.Design.SolovevAlpha
open PlasmaLean.Design.SolovevFluxQuadrature
open PlasmaLean.Design.SolovevMercierQuadrature (Gn Pn fP fQ Gn_pos)

/-! ## Calculus in the normalized radius `ε` -/

/-- The parameter box `|ε| ≤ 3/4`, `|y| ≤ 1` on which `v = 1 + εy ≥ 1/4`. -/
abbrev Box : Set (ℝ × ℝ) := Icc (-(3 / 4) : ℝ) (3 / 4) ×ˢ Icc (-1 : ℝ) 1

/-- `1 + εy ≥ 1/4` on the box. -/
theorem v_ge {ε y : ℝ} (hε : ε ∈ Icc (-(3 / 4) : ℝ) (3 / 4)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    1 / 4 ≤ 1 + ε * y := by
  obtain ⟨h1, h2⟩ := hε
  obtain ⟨h3, h4⟩ := hy
  nlinarith [mul_nonneg (show 0 ≤ ε + 3 / 4 by linarith) (show 0 ≤ 1 + y by linarith),
    mul_nonneg (show 0 ≤ 3 / 4 - ε by linarith) (show 0 ≤ 1 - y by linarith)]

/-- `v = 1 + εy > 0` for `|ε| < 3/4`, `|y| ≤ 1`. -/
theorem v_pos' {ε y : ℝ} (hε : ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    0 < 1 + ε * y := by
  have := v_ge (Ioo_subset_Icc_self hε) hy; linarith

/-- `(√v)^{-k}`, `v = 1 + εy`, is continuous on the box. -/
theorem contOn_invpow (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (√(1 + p.1 * p.2) ^ k)⁻¹) Box := by
  refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun p hp => ?_
  have := v_ge hp.1 hp.2
  exact (pow_pos (Real.sqrt_pos.2 (by linarith)) k).ne'

/-- Derivative of `(√u)^{-(n+1)}` along a positive differentiable `u`. -/
theorem hasDerivAt_invsqrtpow {u : ℝ → ℝ} {u' x : ℝ} (n : ℕ) (hu : HasDerivAt u u' x)
    (hpos : 0 < u x) :
    HasDerivAt (fun x => (√(u x) ^ (n + 1))⁻¹)
      (-((n + 1) / 2 * u' * (√(u x) ^ (n + 3))⁻¹)) x := by
  have ha := Real.sqrt_pos.2 hpos
  have h1 := hu.sqrt hpos.ne'
  have h2 : HasDerivAt (fun y => √(u y) ^ (n + 1))
      ((n + 1 : ℕ) * √(u x) ^ n * (u' / (2 * √(u x)))) x := by
    simpa using h1.fun_pow (n + 1)
  have h3 := h2.inv (pow_pos ha (n + 1)).ne'
  convert h3 using 1
  set a := √(u x)
  field_simp
  push_cast
  ring

/-- **Differentiation under the integral sign** for `∫_{-π}^{π} F(ε, sin t) dt` on
`|ε| < 3/4`, with a uniform bound from compactness of the box. -/
theorem hasDerivAt_integral_sin {F F' : ℝ → ℝ → ℝ} {ε₀ : ℝ}
    (hε₀ : ε₀ ∈ Ioo (-(3 / 4) : ℝ) (3 / 4))
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Box)
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) Box)
    (hd : ∀ ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4), ∀ y ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun e => F e y) (F' ε y) ε) :
    HasDerivAt (fun ε => ∫ t in (-π)..π, F ε (Real.sin t)) (∫ t in (-π)..π, F' ε₀ (Real.sin t))
      ε₀ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hsin : ∀ t, Real.sin t ∈ Icc (-1 : ℝ) 1 :=
    fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have slice : ∀ {G : ℝ → ℝ → ℝ}, ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) Box →
      ∀ ε ∈ Icc (-(3 / 4) : ℝ) (3 / 4), Continuous fun t => G ε (Real.sin t) := by
    intro G hG ε hε
    have : ContinuousOn (fun y => G ε y) (Icc (-1) 1) :=
      hG.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy => ⟨hε, hy⟩
    exact this.comp_continuous Real.continuous_sin hsin
  have hs : Ioo (-(3 / 4) : ℝ) (3 / 4) ∈ 𝓝 ε₀ := Ioo_mem_nhds hε₀.1 hε₀.2
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ε t => F ε (Real.sin t)) (F' := fun ε t => F' ε (Real.sin t))
    (bound := fun _ => M) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with ε hε using
      (slice hF ε (Ioo_subset_Icc_self hε)).aestronglyMeasurable
  · exact (slice hF ε₀ (Ioo_subset_Icc_self hε₀)).intervalIntegrable _ _
  · exact (slice hF' ε₀ (Ioo_subset_Icc_self hε₀)).aestronglyMeasurable
  · exact ae_of_all _ fun t _ ε hε => hM (ε, Real.sin t) ⟨Ioo_subset_Icc_self hε, hsin t⟩
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ ε hε => hd ε hε _ (hsin t)

/-- `v^{-5/2}`. -/
@[expose] def fQ5 (ε y : ℝ) : ℝ := (√(1 + ε * y) ^ 5)⁻¹

/-- `v^{-7/2}`. -/
@[expose] def fQ7 (ε y : ℝ) : ℝ := (√(1 + ε * y) ^ 7)⁻¹

/-- Derivative in `ε` of `(√(1+εy))^{-(n+1)}`. -/
theorem hasDerivAt_eps_invpow (n : ℕ) {ε y : ℝ} (hv : 0 < 1 + ε * y) :
    HasDerivAt (fun e => (√(1 + e * y) ^ (n + 1))⁻¹)
      (-((n + 1) / 2 * y * (√(1 + ε * y) ^ (n + 3))⁻¹)) ε := by
  have hu : HasDerivAt (fun e => 1 + e * y) y ε := by
    simpa using ((hasDerivAt_id ε).mul_const y).const_add 1
  exact hasDerivAt_invsqrtpow n hu hv

/-- `∂_ε v^{-1/2} = -(1/2) y v^{-3/2}`. -/
theorem hasDerivAt_fP_eps {ε y : ℝ} (hv : 0 < 1 + ε * y) :
    HasDerivAt (fun e => fP e y) (-(1 / 2 * y * fQ ε y)) ε := by
  have h := hasDerivAt_eps_invpow 0 hv
  simp only [zero_add, pow_one, Nat.cast_zero] at h
  exact h

/-- `∂_ε v^{-3/2} = -(3/2) y v^{-5/2}`. -/
theorem hasDerivAt_fQ_eps {ε y : ℝ} (hv : 0 < 1 + ε * y) :
    HasDerivAt (fun e => fQ e y) (-(3 / 2 * y * fQ5 ε y)) ε :=
  (hasDerivAt_eps_invpow 2 hv).congr_deriv (by unfold fQ5; norm_num)

/-- `∂_ε v^{-5/2} = -(5/2) y v^{-7/2}`. -/
theorem hasDerivAt_fQ5_eps {ε y : ℝ} (hv : 0 < 1 + ε * y) :
    HasDerivAt (fun e => fQ5 e y) (-(5 / 2 * y * fQ7 ε y)) ε :=
  (hasDerivAt_eps_invpow 4 hv).congr_deriv (by unfold fQ7; norm_num)

/-- `∂_t v^{-3/2} = -(3/2) ε cos t v^{-5/2}` along `y = sin t`. -/
theorem hasDerivAt_fQ_t {ε t : ℝ} (hv : 0 < 1 + ε * Real.sin t) :
    HasDerivAt (fun t => fQ ε (Real.sin t)) (-(3 / 2 * (ε * Real.cos t) * fQ5 ε (Real.sin t)))
      t := by
  have hu : HasDerivAt (fun t => 1 + ε * Real.sin t) (ε * Real.cos t) t := by
    simpa using ((Real.hasDerivAt_sin t).const_mul ε).const_add 1
  exact (hasDerivAt_invsqrtpow 2 hu hv).congr_deriv (by unfold fQ5; norm_num)

/-- `∂G/∂ε = 2(2y + ε(1+y²))(1+y²) + 4(1-y²)(1+εy)y`. -/
@[expose] def dGn (ε y : ℝ) : ℝ :=
  2 * (2 * y + ε * (1 + y ^ 2)) * (1 + y ^ 2) + 4 * (1 - y ^ 2) * (1 + ε * y) * y

/-- `∂H/∂ε = 8y + 2ε + 8εy²`. -/
@[expose] def dHn (ε y : ℝ) : ℝ := 8 * y + 2 * ε + 8 * ε * y ^ 2

/-- `G` has `ε`-derivative `dGn`. -/
theorem hasDerivAt_Gn (ε y : ℝ) : HasDerivAt (fun e => Gn e y) (dGn ε y) ε := by
  have h1 : HasDerivAt (fun e : ℝ => e) 1 ε := hasDerivAt_id ε
  have := ((((h1.mul_const (1 + y ^ 2)).const_add (2 * y)).fun_pow 2).fun_add
    ((((h1.mul_const y).const_add 1).fun_pow 2).const_mul (2 * (1 - y ^ 2))))
  convert this using 1
  · funext e; simp [Gn]
  · simp [dGn]; ring

/-- `H` has `ε`-derivative `dHn`. -/
theorem hasDerivAt_Hn (ε y : ℝ) : HasDerivAt (fun e => Hn e y) (dHn ε y) ε := by
  have h1 : HasDerivAt (fun e : ℝ => e) 1 ε := hasDerivAt_id ε
  have := (((h1.const_mul (8 * y)).const_add 3).fun_add (h1.fun_pow 2)).fun_add
    ((h1.fun_pow 2).const_mul (4 * y ^ 2))
  convert this using 1
  · funext e; simp [Hn]; ring
  · simp [dHn]; ring

/-- `S3c ε = (3/2) ∫ cos² t · v^{-5/2} dt` (equals `SolovevMercierQuadrature.S3n ε` for
`ε > 0`, but without the `1/ε`, so it is continuous at the axis). -/
@[expose] def S3c (ε : ℝ) : ℝ :=
  ∫ t in (-π)..π, 3 / 2 * (1 - Real.sin t ^ 2) * fQ5 ε (Real.sin t)

/-- `dPn/dε = -(1/2) ∫ sin t · v^{-3/2} dt`. -/
theorem hasDerivAt_Pn {ε : ℝ} (hε : ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4)) :
    HasDerivAt Pn (∫ t in (-π)..π, -(1 / 2 * Real.sin t * fQ ε (Real.sin t))) ε :=
  hasDerivAt_integral_sin (F := fP) (F' := fun ε y => -(1 / 2 * y * fQ ε y)) hε
    (by simpa [fP] using contOn_invpow 1)
    (ContinuousOn.neg (ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
      (contOn_invpow 3)))
    (fun _ hε _ hy => hasDerivAt_fP_eps (v_pos' hε hy))

/-- `dIGn/dε = ∫ (∂G/∂ε · v^{-3/2} - (3/2) y G v^{-5/2}) dt`. -/
theorem hasDerivAt_IGn {ε : ℝ} (hε : ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4)) :
    HasDerivAt IGn (∫ t in (-π)..π, (dGn ε (Real.sin t) * fQ ε (Real.sin t) +
      Gn ε (Real.sin t) * (-(3 / 2 * Real.sin t * fQ5 ε (Real.sin t))))) ε :=
  hasDerivAt_integral_sin (F := fun ε y => Gn ε y * fQ ε y)
    (F' := fun ε y => dGn ε y * fQ ε y + Gn ε y * (-(3 / 2 * y * fQ5 ε y))) hε
    (ContinuousOn.mul (Continuous.continuousOn (by unfold Gn; fun_prop)) (contOn_invpow 3))
    (ContinuousOn.add (ContinuousOn.mul (Continuous.continuousOn (by unfold dGn; fun_prop))
      (contOn_invpow 3)) (ContinuousOn.mul (Continuous.continuousOn (by unfold Gn; fun_prop))
        (ContinuousOn.neg (ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
          (contOn_invpow 5)))))
    (fun ε hε y hy => (hasDerivAt_Gn ε y).fun_mul (hasDerivAt_fQ_eps (v_pos' hε hy)))

/-- `dIHn/dε = ∫ (∂H/∂ε · v^{-3/2} - (3/2) y H v^{-5/2}) dt`. -/
theorem hasDerivAt_IHn {ε : ℝ} (hε : ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4)) :
    HasDerivAt IHn (∫ t in (-π)..π, (dHn ε (Real.sin t) * fQ ε (Real.sin t) +
      Hn ε (Real.sin t) * (-(3 / 2 * Real.sin t * fQ5 ε (Real.sin t))))) ε :=
  hasDerivAt_integral_sin (F := fun ε y => Hn ε y * fQ ε y)
    (F' := fun ε y => dHn ε y * fQ ε y + Hn ε y * (-(3 / 2 * y * fQ5 ε y))) hε
    (ContinuousOn.mul (Continuous.continuousOn (by unfold Hn; fun_prop)) (contOn_invpow 3))
    (ContinuousOn.add (ContinuousOn.mul (Continuous.continuousOn (by unfold dHn; fun_prop))
      (contOn_invpow 3)) (ContinuousOn.mul (Continuous.continuousOn (by unfold Hn; fun_prop))
        (ContinuousOn.neg (ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
          (contOn_invpow 5)))))
    (fun ε hε y hy => (hasDerivAt_Hn ε y).fun_mul (hasDerivAt_fQ_eps (v_pos' hε hy)))

/-- `S3c` is differentiable (hence continuous) on `|ε| < 3/4`. -/
theorem hasDerivAt_S3c {ε : ℝ} (hε : ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4)) :
    HasDerivAt S3c (∫ t in (-π)..π, 3 / 2 * (1 - Real.sin t ^ 2) *
      (-(5 / 2 * Real.sin t * fQ7 ε (Real.sin t)))) ε :=
  hasDerivAt_integral_sin (F := fun ε y => 3 / 2 * (1 - y ^ 2) * fQ5 ε y)
    (F' := fun ε y => 3 / 2 * (1 - y ^ 2) * (-(5 / 2 * y * fQ7 ε y))) hε
    (ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) (contOn_invpow 5))
    (ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
      (ContinuousOn.neg (ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
        (contOn_invpow 7))))
    (fun ε hε y hy => (hasDerivAt_fQ5_eps (v_pos' hε hy)).const_mul (3 / 2 * (1 - y ^ 2)))


/-! ## Two integrations by parts over the closed surface -/

/-- `t ↦ (√(1 + ε sin t))^{-k}` is continuous for `|ε| ≤ 3/4`. -/
theorem cont_t (k : ℕ) {ε : ℝ} (hε : ε ∈ Icc (-(3 / 4) : ℝ) (3 / 4)) :
    Continuous fun t => (√(1 + ε * Real.sin t) ^ k)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun t => ?_
  have := v_ge hε ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  exact (pow_pos (Real.sqrt_pos.2 (by linarith)) k).ne'

/-- `v^{-3/2} = v · v^{-5/2}`. -/
theorem fQ_eq_mul {ε y : ℝ} (hv : 0 < 1 + ε * y) : fQ ε y = (1 + ε * y) * fQ5 ε y := by
  unfold fQ fQ5
  have ha := Real.sqrt_pos.2 hv
  have ha2 := Real.sq_sqrt hv.le
  rw [show √(1 + ε * y) ^ 5 = (1 + ε * y) * √(1 + ε * y) ^ 3 by
    rw [show (5 : ℕ) = 2 + 3 by rfl, pow_add, ha2]]
  field_simp

/-- A derivative integrating to zero over a period (`Φ(-π) = Φ(π)`). -/
theorem integral_deriv_periodic {Φ Φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt Φ (Φ' t) t)
    (hc : Continuous Φ') (hper : Φ (-π) = Φ π) : ∫ t in (-π)..π, Φ' t = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable _ _), hper, sub_self]

/-- **First integration by parts**: `-(1/2) ∫ sin t v^{-3/2} dt = (ε/2) S3c ε`
(derivative of `cos t · v^{-3/2}`). -/
theorem dPn_eq {ε : ℝ} (hε : ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4)) :
    ∫ t in (-π)..π, -(1 / 2 * Real.sin t * fQ ε (Real.sin t)) = ε / 2 * S3c ε := by
  have hεc := Ioo_subset_Icc_self hε
  have hsin : ∀ t, Real.sin t ∈ Icc (-1 : ℝ) 1 :=
    fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have c3 : Continuous fun t => fQ ε (Real.sin t) := cont_t 3 hεc
  have c5 : Continuous fun t => fQ5 ε (Real.sin t) := cont_t 5 hεc
  have hd : ∀ t, HasDerivAt (fun t => Real.cos t * fQ ε (Real.sin t))
      (-Real.sin t * fQ ε (Real.sin t) +
        Real.cos t * (-(3 / 2 * (ε * Real.cos t) * fQ5 ε (Real.sin t)))) t :=
    fun t => (Real.hasDerivAt_cos t).mul (hasDerivAt_fQ_t (v_pos' hε (hsin t)))
  have h0 := integral_deriv_periodic hd (by fun_prop) (by simp)
  have e : ∀ t, -Real.sin t * fQ ε (Real.sin t) +
      Real.cos t * (-(3 / 2 * (ε * Real.cos t) * fQ5 ε (Real.sin t))) =
      2 * -(1 / 2 * Real.sin t * fQ ε (Real.sin t)) -
        ε * (3 / 2 * (1 - Real.sin t ^ 2) * fQ5 ε (Real.sin t)) := fun t => by
    have := Real.cos_sq' t
    linear_combination (-(3 / 2) * ε * fQ5 ε (Real.sin t)) * this
  simp only [e] at h0
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun t =>
      2 * -(1 / 2 * Real.sin t * fQ ε (Real.sin t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t =>
      ε * (3 / 2 * (1 - Real.sin t ^ 2) * fQ5 ε (Real.sin t))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
  unfold S3c
  linarith

/-- The poloidal "stream function" of the Gauss identity:
`φ(ε, y) = -ε - ((ε² + 2)/2) y + (ε²/2) y³`. -/
@[expose] def phiG (ε y : ℝ) : ℝ := -ε - (ε ^ 2 + 2) / 2 * y + ε ^ 2 / 2 * y ^ 3

/-- `∂φ/∂y`. -/
@[expose] def dphiG (ε y : ℝ) : ℝ := -((ε ^ 2 + 2) / 2) + 3 * ε ^ 2 / 2 * y ^ 2

/-- The pointwise identity behind the Gauss identity:
`G v^{-3/2} + (ε/2) ∂_ε(G v^{-3/2}) - H v^{-3/2} = ∂_t (cos t · φ · v^{-3/2})`. -/
theorem gauss_pointwise (ε y c fq fq5 : ℝ) (hfq : fq = (1 + ε * y) * fq5)
    (hc : c ^ 2 = 1 - y ^ 2) :
    (-y * phiG ε y + c * (dphiG ε y * c)) * fq + c * phiG ε y * (-(3 / 2 * (ε * c) * fq5)) =
      Gn ε y * fq + ε / 2 * (dGn ε y * fq + Gn ε y * (-(3 / 2 * y * fq5))) - Hn ε y * fq := by
  unfold phiG dphiG Gn dGn Hn
  linear_combination ((3 * c ^ 2 * ε ^ 2 * y ^ 2 - c ^ 2 * ε ^ 2 - 2 * c ^ 2 + 3 * ε ^ 2 * y ^ 4 -
      7 * ε ^ 2 * y ^ 2 - 2 * ε ^ 2 - 6 * ε * y - 2 * y ^ 2 + 2) / 2) * hfq +
    (fq5 * (3 * ε ^ 3 * y ^ 3 + ε ^ 3 * y + 6 * ε ^ 2 * y ^ 2 + 4 * ε ^ 2 + 2 * ε * y - 4) / 4) * hc

/-- **Gauss identity in normalized form**: `IGn + (ε/2) IGn' = IHn` on `|ε| < 3/4`
(the divergence theorem `d/dψ (V'⟨|∇ψ|²⟩) = V'⟨Δψ⟩` on the Solov'ev surfaces). -/
theorem gauss_eps {ε : ℝ} (hε : ε ∈ Ioo (-(3 / 4) : ℝ) (3 / 4)) :
    IGn ε + ε / 2 * (∫ t in (-π)..π, (dGn ε (Real.sin t) * fQ ε (Real.sin t) +
      Gn ε (Real.sin t) * (-(3 / 2 * Real.sin t * fQ5 ε (Real.sin t))))) = IHn ε := by
  have hεc := Ioo_subset_Icc_self hε
  have hsin : ∀ t, Real.sin t ∈ Icc (-1 : ℝ) 1 :=
    fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
  have c3 : Continuous fun t => fQ ε (Real.sin t) := cont_t 3 hεc
  have c5 : Continuous fun t => fQ5 ε (Real.sin t) := cont_t 5 hεc
  have hphi : ∀ t, HasDerivAt (fun t => phiG ε (Real.sin t))
      (dphiG ε (Real.sin t) * Real.cos t) t := fun t => by
    have hs := Real.hasDerivAt_sin t
    have := ((hs.const_mul ((ε ^ 2 + 2) / 2)).const_sub (-ε)).fun_add
      ((hs.fun_pow 3).const_mul (ε ^ 2 / 2))
    convert this using 1
    · funext t; unfold phiG; ring
    · simp [dphiG]; ring
  have hd : ∀ t, HasDerivAt (fun t => Real.cos t * phiG ε (Real.sin t) * fQ ε (Real.sin t))
      ((-Real.sin t * phiG ε (Real.sin t) + Real.cos t * (dphiG ε (Real.sin t) * Real.cos t)) *
        fQ ε (Real.sin t) +
        Real.cos t * phiG ε (Real.sin t) *
          (-(3 / 2 * (ε * Real.cos t) * fQ5 ε (Real.sin t)))) t :=
    fun t => ((Real.hasDerivAt_cos t).mul (hphi t)).mul (hasDerivAt_fQ_t (v_pos' hε (hsin t)))
  have h0 := integral_deriv_periodic hd (by unfold phiG dphiG; fun_prop) (by simp)
  rw [intervalIntegral.integral_congr (fun t _ => gauss_pointwise ε (Real.sin t) (Real.cos t)
    (fQ ε (Real.sin t)) (fQ5 ε (Real.sin t)) (fQ_eq_mul (v_pos' hε (hsin t)))
    (Real.cos_sq' t))] at h0
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul] at h0
  · unfold IGn IHn; linarith
  all_goals (apply Continuous.intervalIntegrable; simp only [Gn, dGn, Hn]; fun_prop)


/-! ## The flux surfaces of the transport label `s = ψ̃/ψ̃_b` -/

open PlasmaLean.Design.SolovevMercierCertified (surfPt surfPt_0 surfPt_1 surfPt_2 R2_surfPt RS_eq
  normsq_psiTGrad surfPt_on_surface Pint Pint_eq Pint_pos volS)
open PlasmaLean.Design.SolovevOnePlasma (psiB psiB_pos label)

/-- `ψ̃_b = 110000/192`. -/
theorem psiB_eq : psiB = 110000 / 192 := by norm_num [psiB]

/-- Mercier radius `σ = √ψ̃ = √(ψ̃_b s)` of the flux surface with transport label `s`. -/
@[expose] def sig (s : ℝ) : ℝ := √(psiB * s)

/-- Normalized radius `ε = σ/50` (`ε² = 11 s/48`). -/
@[expose] def eps (s : ℝ) : ℝ := sig s / 50

/-- `σ ≥ 0`. -/
theorem sig_nonneg (s : ℝ) : 0 ≤ sig s := Real.sqrt_nonneg _

/-- `σ² = ψ̃_b s`. -/
theorem sig_sq {s : ℝ} (hs : 0 ≤ s) : sig s ^ 2 = psiB * s :=
  Real.sq_sqrt (mul_nonneg psiB_pos.le hs)

/-- `σ > 0` off the axis. -/
theorem sig_pos {s : ℝ} (hs : 0 < s) : 0 < sig s :=
  Real.sqrt_pos.2 (mul_pos psiB_pos hs)

/-- `ε ≥ 0`. -/
theorem eps_nonneg (s : ℝ) : 0 ≤ eps s := div_nonneg (sig_nonneg s) (by norm_num)

/-- `ε² = 11 s/48`. -/
theorem eps_sq {s : ℝ} (hs : 0 ≤ s) : eps s ^ 2 = 11 * s / 48 := by
  unfold eps; rw [div_pow, sig_sq hs, psiB_eq]; ring

/-- On the transport domain `ε ≤ 12/25`. -/
theorem eps_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : eps s ≤ 12 / 25 := by
  have h := eps_sq hs.1
  have := eps_nonneg s
  nlinarith [hs.2]

/-- For `0 ≤ s < 2`, `ε < 3/4`. -/
theorem eps_lt {s : ℝ} (hs : 0 ≤ s) (hs' : s < 2) : eps s < 3 / 4 := by
  have h := eps_sq hs
  have := eps_nonneg s
  nlinarith

/-- For `0 ≤ s ≤ 2`, `σ < 34`. -/
theorem sig_lt {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) : sig s < 34 := by
  have h := sig_sq hs
  have := sig_nonneg s
  rw [psiB_eq] at h
  nlinarith

/-- `ε` lies in the differentiability range for `0 ≤ s < 2`. -/
theorem eps_mem {s : ℝ} (hs : 0 ≤ s) (hs' : s < 2) :
    eps s ∈ Ioo (-(3 / 4) : ℝ) (3 / 4) :=
  ⟨by linarith [eps_nonneg s], eps_lt hs hs'⟩

/-- `ε ∈ [0, 12/25]` on the transport domain. -/
theorem eps_mem_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : eps s ∈ Icc (0 : ℝ) (12 / 25) :=
  ⟨eps_nonneg s, eps_le hs⟩

/-- **The parametrized curve is the flux surface of label `s`**: `label (x(t)) = s`. -/
theorem label_surfPt {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) (t : ℝ) :
    label (surfPt (sig s) t) = s := by
  unfold label
  rw [surfPt_on_surface (sig_nonneg s) (by linarith [sig_lt hs hs']) t, sig_sq hs]
  field_simp [psiB_pos.ne']

/-- `|∇s|² = |∇ψ̃|²/ψ̃_b²` (actual gradient `Solovev.psiTGrad`). -/
@[expose] def gradSqS (x : Space) : ℝ := ‖psiTGrad 10 x‖ ^ 2 / psiB ^ 2

/-- `Δψ̃` in closed form: `∂²_R ψ̃ + ∂_R ψ̃ / R + ∂²_z ψ̃ = 2z² + 5R² - 2L²` (`L = 10`). -/
@[expose] def lapPsiT (x : Space) : ℝ := 2 * x 2 ^ 2 + 5 * R2 x - 2 * 10 ^ 2

/-- `Δs = Δψ̃/ψ̃_b`. -/
@[expose] def lapS (x : Space) : ℝ := lapPsiT x / psiB

/-- **Surface integral** `∮ f dS/|∇s|` over the flux surface of label `s`, in the surface
coordinate `t` of `SolovevMercierCertified.surfPt` (toroidal angle integrated):
`π √2 ψ̃_b ∫_{-π}^{π} f(x(t)) / R(t) dt` (`surface_weight_eq` identifies the weight). -/
@[expose] def surfInt (f : Space → ℝ) (s : ℝ) : ℝ :=
  π * √2 * psiB * ∫ t in (-π)..π, f (surfPt (sig s) t) / RS 10 (sig s) t

/-- `V'(s) = ∮ dS/|∇s|`. -/
@[expose] def Vp (s : ℝ) : ℝ := surfInt (fun _ => 1) s

/-- `V'(s) ⟨|∇s|²⟩ = ∮ |∇s| dS`. -/
@[expose] def VG (s : ℝ) : ℝ := surfInt gradSqS s

/-- `V'(s) ⟨Δs⟩ = ∮ Δs dS/|∇s|`. -/
@[expose] def VH (s : ℝ) : ℝ := surfInt lapS s

/-- `g(s) = ⟨|∇s|²⟩`. -/
@[expose] def gS (s : ℝ) : ℝ := VG s / Vp s

/-- `h(s) = ⟨Δs⟩`. -/
@[expose] def hS (s : ℝ) : ℝ := VH s / Vp s

/-- `V''(s) = π √2 ψ̃_b²/10⁵ · S3c(ε(s))` (proved to be the derivative, `Vp_deriv`). -/
@[expose] def dVp (s : ℝ) : ℝ := π * √2 * psiB ^ 2 / 100000 * S3c (eps s)

/-- `g'(s) = (V'h - V'' g)/V'` (proved to be the derivative, `gS_deriv`). -/
@[expose] def dgS (s : ℝ) : ℝ := (VH s - dVp s * gS s) / Vp s

/-! ### Exact reduction to the normalized integrals -/

/-- `|∇ψ̃|² = 10⁴ σ² G(σ/50, sin t)/R²` on the surface, for `0 ≤ σ < 50`. -/
theorem normsq_eq {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 50) (t : ℝ) :
    ‖psiTGrad 10 (surfPt σ t)‖ ^ 2 = 10000 * σ ^ 2 * Gn (σ / 50) (Real.sin t) / RS 10 σ t ^ 2 := by
  rw [normsq_psiTGrad]
  have hR := RS_pos h0 (by linarith : 2 * σ < 10 ^ 2) t
  have hRu : RS 10 σ t ^ 2 = 100 + 2 * σ * Real.sin t := by
    rw [RS_sq h0 (by linarith : 2 * σ < 10 ^ 2) t]; unfold uS; norm_num
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := Real.sin_sq_add_cos_sq t
  unfold zS Gn
  field_simp
  grind

/-- `R = 10 a`, `a = √(1 + ε sin t)`, `ε = σ/50`. -/
theorem RS_eq' (σ t : ℝ) : RS 10 σ t = 10 * √(1 + σ / 50 * Real.sin t) := RS_eq σ t

/-- `V'(s) = (π √2 ψ̃_b/10) Pn(ε)`. -/
theorem Vp_eq (s : ℝ) : Vp s = π * √2 * psiB / 10 * Pn (eps s) := by
  unfold Vp surfInt Pn
  have e : ∀ t, (fun _ => (1 : ℝ)) (surfPt (sig s) t) / RS 10 (sig s) t =
      1 / 10 * fP (eps s) (Real.sin t) := fun t => by
    rw [RS_eq', fP, eps]
    field_simp
  rw [intervalIntegral.integral_congr (fun t _ => e t), intervalIntegral.integral_const_mul]
  ring

/-- `V'(s) ⟨|∇s|²⟩ = 10 π √2 s IGn(ε)` for `0 ≤ s ≤ 2`. -/
theorem VG_eq {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) : VG s = 10 * π * √2 * s * IGn (eps s) := by
  unfold VG surfInt IGn
  have hσ := sig_lt hs hs'
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  have e : ∀ t, π * √2 * psiB * (gradSqS (surfPt (sig s) t) / RS 10 (sig s) t) =
      10 * π * √2 * s * (Gn (eps s) (Real.sin t) * fQ (eps s) (Real.sin t)) := fun t => by
    unfold gradSqS
    rw [normsq_eq (sig_nonneg s) (by linarith) t, RS_eq']
    have hv : 0 < 1 + sig s / 50 * Real.sin t := by
      have := v_ge (ε := sig s / 50) ⟨by linarith [sig_nonneg s], by linarith⟩
        ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
      linarith
    have ha := Real.sqrt_pos.2 hv
    have hσ2 := sig_sq hs
    have hp := psiB_pos
    unfold fQ eps
    field_simp
    rw [hσ2]
    ring
  simp only [e]


/-- The algebra of `Δψ̃/R` on the surface: `(2z² + 5R² - 2L²)/R = 10 H(ε, y) v^{-3/2}`. -/
theorem lap_algebra (σ a c y q : ℝ) (ha : 0 < a) (hq : q ^ 2 = 2)
    (ha2 : a ^ 2 = 1 + σ / 50 * y) (hc : c ^ 2 = 1 - y ^ 2) :
    (2 * (q * σ * c / (10 * a)) ^ 2 + 5 * (10 * a) ^ 2 - 2 * 10 ^ 2) / (10 * a) =
      10 * Hn (σ / 50) y * (a ^ 3)⁻¹ := by
  unfold Hn
  rw [div_pow, mul_pow, mul_pow, hq, hc]
  field_simp
  linear_combination (10 ^ 4 * 50 ^ 2 * (5 * (a ^ 2 + 1 + σ / 50 * y) - 2)) * ha2

/-- `V'(s) ⟨Δs⟩ = 10 π √2 IHn(ε)` for `0 ≤ s ≤ 2`. -/
theorem VH_eq {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) : VH s = 10 * π * √2 * IHn (eps s) := by
  unfold VH surfInt IHn
  have hσ := sig_lt hs hs'
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  have e : ∀ t, π * √2 * psiB * (lapS (surfPt (sig s) t) / RS 10 (sig s) t) =
      10 * π * √2 * (Hn (eps s) (Real.sin t) * fQ (eps s) (Real.sin t)) := fun t => by
    have hv : 0 < 1 + sig s / 50 * Real.sin t := by
      have := v_ge (ε := sig s / 50) ⟨by linarith [sig_nonneg s], by linarith⟩
        ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
      linarith
    have ha := Real.sqrt_pos.2 hv
    have key := lap_algebra (sig s) (√(1 + sig s / 50 * Real.sin t)) (Real.cos t) (Real.sin t)
      (√2) ha (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt hv.le) (Real.cos_sq' t)
    unfold lapS lapPsiT
    rw [surfPt_2, R2_surfPt, zS, RS_eq']
    unfold fQ eps
    rw [div_right_comm, key]
    have hp := psiB_pos
    field_simp
  simp only [e]

/-- `Pn > 0` on the plasma (`Pn(σ/50) = 10 ∫ R⁻¹ dt`). -/
theorem Pn_pos {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) : 0 < Pn (eps s) := by
  have := Pint_pos (s := sig s) ⟨by linarith [sig_nonneg s], by linarith [sig_lt hs hs']⟩
  rw [Pint_eq] at this
  unfold eps
  linarith

/-- `V' > 0`. -/
theorem Vp_pos {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) : 0 < Vp s := by
  rw [Vp_eq]
  have := Pn_pos hs hs'
  have := Real.pi_pos
  have := psiB_pos
  positivity

/-- `g(s) = (48/275) s IGn(ε)/Pn(ε)` (`100/ψ̃_b = 48/275`). -/
theorem gS_eq {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) :
    gS s = 48 / 275 * s * (IGn (eps s) / Pn (eps s)) := by
  unfold gS
  rw [VG_eq hs hs', Vp_eq, psiB_eq]
  have := Pn_pos hs hs'
  have := Real.pi_pos
  field_simp
  ring

/-- `h(s) = (48/275) IHn(ε)/Pn(ε)`. -/
theorem hS_eq {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 2) :
    hS s = 48 / 275 * (IHn (eps s) / Pn (eps s)) := by
  unfold hS
  rw [VH_eq hs hs', Vp_eq, psiB_eq]
  have := Pn_pos hs hs'
  have := Real.pi_pos
  field_simp
  ring


/-! ### Derivatives in the label `s` (the axis `s = 0` by the derivative-extension theorem) -/

/-- `ε` is continuous. -/
theorem continuous_eps : Continuous eps := by unfold eps sig; fun_prop

/-- `dε/ds = ψ̃_b/(100 σ)` for `s > 0`. -/
theorem hasDerivAt_eps {s : ℝ} (hs : 0 < s) : HasDerivAt eps (psiB / (100 * sig s)) s := by
  have h1 : HasDerivAt (fun s => psiB * s) psiB s := by
    simpa using (hasDerivAt_id s).const_mul psiB
  have h3 := (h1.sqrt (mul_pos psiB_pos hs).ne').div_const 50
  change HasDerivAt (fun s => √(psiB * s) / 50) _ s
  convert h3 using 1
  unfold sig
  have := sig_pos hs
  unfold sig at this
  field_simp
  ring

/-- `ε(0) = 0`. -/
theorem eps_zero : eps 0 = 0 := by simp [eps, sig]

/-- **`V'' = dVp`** on `0 < s < 2`. -/
theorem hasDerivAt_Vp {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) : HasDerivAt Vp (dVp s) s := by
  have hfun : Vp = fun s => π * √2 * psiB / 10 * Pn (eps s) := funext Vp_eq
  have hm := eps_mem hs.1.le hs.2
  have h := ((hasDerivAt_Pn hm).comp s (hasDerivAt_eps hs.1)).const_mul (π * √2 * psiB / 10)
  rw [hfun]
  refine h.congr_deriv ?_
  rw [dPn_eq hm]
  unfold dVp eps
  have := sig_pos hs.1
  field_simp
  ring

/-- **Gauss identity in the label**: `(V' g)' = V' h` on `0 < s < 2`, from `gauss_eps`. -/
theorem hasDerivAt_VG {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) : HasDerivAt VG (VH s) s := by
  have hm := eps_mem hs.1.le hs.2
  have hev : (fun s => 10 * π * √2 * s * IGn (eps s)) =ᶠ[𝓝 s] VG := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    rw [VG_eq hx.1.le hx.2.le]
  have h := (((hasDerivAt_id s).const_mul (10 * π * √2)).mul
    ((hasDerivAt_IGn hm).comp s (hasDerivAt_eps hs.1)))
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [VH_eq hs.1.le hs.2.le, ← gauss_eps hm]
  have hσ := sig_pos hs.1
  have hσ2 := sig_sq hs.1.le
  have key : s * (psiB / (100 * sig s)) = eps s / 2 := by
    unfold eps
    field_simp
    linarith
  have key2 : ∀ X : ℝ, 10 * π * √2 * 1 * IGn (eps s) + 10 * π * √2 * s * (X * (psiB /
      (100 * sig s))) = 10 * π * √2 * (IGn (eps s) + eps s / 2 * X) := fun X => by
    rw [← key]; ring
  simp only [Function.comp, id]
  exact key2 _

/-- `S3c ∘ ε` is continuous at every `s ∈ [0, 2)`. -/
theorem continuousAt_dVp {s : ℝ} (hs : 0 ≤ s) (hs' : s < 2) : ContinuousAt dVp s := by
  unfold dVp
  exact continuousAt_const.mul ((hasDerivAt_S3c (eps_mem hs hs')).continuousAt.comp
    continuous_eps.continuousAt)

/-- `V'` at the axis: one-sided derivative `dVp 0`. -/
theorem hasDerivWithinAt_Vp_zero : HasDerivWithinAt Vp (dVp 0) (Ici 0) 0 := by
  have hm := eps_mem (le_refl (0 : ℝ)) two_pos
  have hcont : ContinuousAt Vp 0 := by
    rw [show Vp = fun s => π * √2 * psiB / 10 * Pn (eps s) from funext Vp_eq]
    exact continuousAt_const.mul ((hasDerivAt_Pn hm).continuousAt.comp
      continuous_eps.continuousAt)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 2)
    (fun x hx => (hasDerivAt_Vp hx).differentiableAt.differentiableWithinAt)
    hcont.continuousWithinAt (Ioo_mem_nhdsGT two_pos) ?_
  refine ((continuousAt_dVp le_rfl two_pos).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (two_pos : (0 : ℝ) < 2)] with x hx
  exact (hasDerivAt_Vp hx).deriv.symm

/-- `V' g` at the axis: one-sided derivative `V'h(0)`. -/
theorem hasDerivWithinAt_VG_zero : HasDerivWithinAt VG (VH 0) (Ici 0) 0 := by
  have hm := eps_mem (le_refl (0 : ℝ)) two_pos
  have hG : ContinuousAt (fun s => 10 * π * √2 * s * IGn (eps s)) 0 :=
    (continuousAt_const.mul continuousAt_id).mul ((hasDerivAt_IGn hm).continuousAt.comp
      continuous_eps.continuousAt)
  have hH : ContinuousAt (fun s => 10 * π * √2 * IHn (eps s)) 0 :=
    continuousAt_const.mul ((hasDerivAt_IHn hm).continuousAt.comp continuous_eps.continuousAt)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 2)
    (fun x hx => (hasDerivAt_VG hx).differentiableAt.differentiableWithinAt)
    (hG.continuousWithinAt.congr (fun x hx => VG_eq hx.1.le hx.2.le)
      (VG_eq le_rfl zero_le_two)) (Ioo_mem_nhdsGT two_pos) ?_
  rw [VH_eq le_rfl zero_le_two]
  refine (hH.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (two_pos : (0 : ℝ) < 2)] with x hx
  rw [(hasDerivAt_VG hx).deriv, VH_eq hx.1.le hx.2.le]

/-- `V'' = dVp` within `[0,1]`, including the axis. -/
theorem Vp_deriv {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivWithinAt Vp (dVp s) (Icc 0 1) s := by
  rcases eq_or_lt_of_le hs.1 with h | h
  · subst h; exact hasDerivWithinAt_Vp_zero.mono Icc_subset_Ici_self
  · exact (hasDerivAt_Vp ⟨h, by linarith [hs.2]⟩).hasDerivWithinAt

/-- `(V' g)' = V' h` within `[0,1]`, including the axis. -/
theorem VG_deriv {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivWithinAt VG (VH s) (Icc 0 1) s := by
  rcases eq_or_lt_of_le hs.1 with h | h
  · subst h; exact hasDerivWithinAt_VG_zero.mono Icc_subset_Ici_self
  · exact (hasDerivAt_VG ⟨h, by linarith [hs.2]⟩).hasDerivWithinAt

/-- `g' = dgS` within `[0,1]` (quotient rule). -/
theorem gS_deriv {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivWithinAt gS (dgS s) (Icc 0 1) s := by
  have hV := (Vp_pos hs.1 (by linarith [hs.2])).ne'
  have h := (VG_deriv hs).div (Vp_deriv hs) hV
  change HasDerivWithinAt (fun x => VG x / Vp x) _ _ _
  refine h.congr_deriv ?_
  unfold dgS gS
  field_simp

/-! ## The Solov'ev flux geometry and its laws -/

/-- **The actual flux-surface geometry of the reactor Solov'ev field** for the transport
label `s = ψ̃/ψ̃_b`: `V' = ∮ dS/|∇s|`, `g = ⟨|∇s|²⟩`, `h = ⟨Δs⟩` (surface integrals over the
exact surfaces `SolovevMercierCertified.surfPt`), with `V''`, `g'` given in closed form. -/
@[expose] def solovevFluxGeometry : FluxGeometry := ⟨Vp, dVp, gS, dgS, hS⟩

/-- **The flux-geometry laws hold** (all proved): `V' > 0`, `V'' = dVp`, `g' = dgS` (one-sided
at the axis), `g(0) = 0`, and the Gauss identity `(V' g)' = V' h`. -/
instance solovevFluxGeometry_laws : solovevFluxGeometry.Laws where
  Vp_pos := fun s hs => Vp_pos hs.1 (by linarith [hs.2])
  Vp_deriv := fun s hs => Vp_deriv hs
  g_deriv := fun s hs => gS_deriv hs
  g_zero := by
    change VG 0 / Vp 0 = 0
    rw [VG_eq le_rfl zero_le_two]; simp
  gauss := fun s hs => by
    change dVp s * gS s + Vp s * dgS s = Vp s * hS s
    have hV := (Vp_pos hs.1 (by linarith [hs.2])).ne'
    unfold dgS hS gS
    field_simp
    ring

/-- `h` is continuous on `[0,1]`. -/
theorem hS_continuousOn : ContinuousOn hS (Icc 0 1) := by
  refine ContinuousOn.congr (f := fun s => 48 / 275 * (IHn (eps s) / Pn (eps s))) ?_
    (fun s hs => hS_eq hs.1 (by linarith [hs.2]))
  intro s hs
  have hm := eps_mem hs.1 (by linarith [hs.2])
  exact (continuousAt_const.mul (((hasDerivAt_IHn hm).continuousAt.comp
    continuous_eps.continuousAt).div ((hasDerivAt_Pn hm).continuousAt.comp
      continuous_eps.continuousAt) (Pn_pos hs.1 (by linarith [hs.2])).ne')).continuousWithinAt

/-- **The actual Solov'ev geometry satisfies `IsSolovevGeometry`**: the laws above and the
enclosures `0.49 s ≤ g ≤ 0.525 s`, `0.49 ≤ h ≤ 0.525`, from the certified polynomial
quadrature `SolovevFluxQuadrature.flux_ratio_bounds`. -/
instance solovevFluxGeometry_isSolovev : SolovevBand.IsSolovevGeometry solovevFluxGeometry where
  toLaws := solovevFluxGeometry_laws
  g_lower := fun s hs => by
    change 49 / 100 * s ≤ gS s
    have hP := Pn_pos hs.1 (by linarith [hs.2])
    obtain ⟨h1, -, -, -⟩ := flux_ratio_bounds (eps_mem_Icc hs)
    have : 49 / 100 ≤ 48 / 275 * (IGn (eps s) / Pn (eps s)) := by
      rw [mul_div_assoc', le_div_iff₀ hP]; linarith
    rw [gS_eq hs.1 (by linarith [hs.2])]
    nlinarith [hs.1]
  g_upper := fun s hs => by
    change gS s ≤ 21 / 40 * s
    have hP := Pn_pos hs.1 (by linarith [hs.2])
    obtain ⟨-, h2, -, -⟩ := flux_ratio_bounds (eps_mem_Icc hs)
    have : 48 / 275 * (IGn (eps s) / Pn (eps s)) ≤ 21 / 40 := by
      rw [mul_div_assoc', div_le_iff₀ hP]; linarith
    rw [gS_eq hs.1 (by linarith [hs.2])]
    nlinarith [hs.1]
  h_lower := fun s hs => by
    change 49 / 100 ≤ hS s
    have hP := Pn_pos hs.1 (by linarith [hs.2])
    obtain ⟨-, -, h3, -⟩ := flux_ratio_bounds (eps_mem_Icc hs)
    rw [hS_eq hs.1 (by linarith [hs.2]), mul_div_assoc', le_div_iff₀ hP]
    linarith
  h_upper := fun s hs => by
    change hS s ≤ 21 / 40
    have hP := Pn_pos hs.1 (by linarith [hs.2])
    obtain ⟨-, -, -, h4⟩ := flux_ratio_bounds (eps_mem_Icc hs)
    rw [hS_eq hs.1 (by linarith [hs.2]), mul_div_assoc', div_le_iff₀ hP]
    linarith
  h_cont := hS_continuousOn


/-! ## Sanity: axis values -/

/-- At the axis `⟨Δs⟩ = 3L²/ψ̃_b = 144/275` (`IHn(0) = 6π`, `Pn(0) = 2π`). -/
theorem hS_zero : hS 0 = 144 / 275 := by
  rw [hS_eq le_rfl zero_le_two, eps_zero]
  unfold IHn Pn Hn fQ fP
  simp
  have := Real.pi_pos
  field_simp
  ring

/-- At the axis `g'(0) = h(0) = 144/275` (Gauss identity with `g(0) = 0`): the slope of
`⟨|∇s|²⟩` at the axis lies inside the certified band `[0.49, 0.525]`. -/
theorem dgS_zero : dgS 0 = 144 / 275 := by
  have hg : gS 0 = 0 := solovevFluxGeometry_laws.g_zero
  unfold dgS
  rw [hg, mul_zero, sub_zero, ← hS_zero]
  rfl

/-! ## The links to the actual field: Laplacian, surface element, enclosed volume -/

/-- The second derivative at `0` of a quartic is twice its quadratic coefficient. -/
theorem quartic_dd {f : ℝ → ℝ} (a b c d e : ℝ)
    (hf : ∀ r, f r = a + b * r + c * r ^ 2 + d * r ^ 3 + e * r ^ 4) :
    deriv (deriv f) 0 = 2 * c := by
  have hfun : f = fun r => a + b * r + c * r ^ 2 + d * r ^ 3 + e * r ^ 4 := funext hf
  have h1 : deriv f = fun r => b + 2 * c * r + 3 * d * r ^ 2 + 4 * e * r ^ 3 := by
    funext r
    rw [hfun]
    have h := (((((hasDerivAt_id r).const_mul b).const_add a).fun_add
      ((hasDerivAt_pow 2 r).const_mul c)).fun_add ((hasDerivAt_pow 3 r).const_mul d)).fun_add
      ((hasDerivAt_pow 4 r).const_mul e)
    refine h.deriv.trans ?_
    simp; ring
  rw [h1]
  have h := ((((hasDerivAt_const (0 : ℝ) b).fun_add ((hasDerivAt_id (0 : ℝ)).const_mul
    (2 * c))).fun_add ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (3 * d))).fun_add
      ((hasDerivAt_pow 3 (0 : ℝ)).const_mul (4 * e)))
  rw [show (fun r : ℝ => b + 2 * c * r + 3 * d * r ^ 2 + 4 * e * r ^ 3) =
    fun r => b + 2 * c * id r + 3 * d * r ^ 2 + 4 * e * r ^ 3 from rfl, h.deriv]
  simp

/-- **`lapPsiT` is the Laplacian of `ψ̃`**: the sum over the three Cartesian directions of the
second derivatives of `ψ̃` along the coordinate lines through `x`. -/
theorem lapPsiT_eq_laplacian (x : Space) : lapPsiT x =
    ∑ i, deriv (deriv (fun r : ℝ => psiT 10 (x + r • EuclideanSpace.single i (1 : ℝ)))) 0 := by
  unfold lapPsiT
  rw [Fin.sum_univ_three,
    quartic_dd (R2 x * x 2 ^ 2 / 2 + (R2 x - 100) ^ 2 / 4) (x 0 * x 2 ^ 2 + x 0 * (R2 x - 100))
      (x 2 ^ 2 / 2 + x 0 ^ 2 + (R2 x - 100) / 2) (x 0) (1 / 4) (fun r => by
        simp [psiT, R2]; ring),
    quartic_dd (R2 x * x 2 ^ 2 / 2 + (R2 x - 100) ^ 2 / 4) (x 1 * x 2 ^ 2 + x 1 * (R2 x - 100))
      (x 2 ^ 2 / 2 + x 1 ^ 2 + (R2 x - 100) / 2) (x 1) (1 / 4) (fun r => by
        simp [psiT, R2]; ring),
    quartic_dd (R2 x * x 2 ^ 2 / 2 + (R2 x - 100) ^ 2 / 4) (R2 x * x 2) (R2 x / 2) 0 0
      (fun r => by simp [psiT, R2]; ring)]
  unfold R2; ring

/-- `σ ≤ 25` on the transport domain. -/
theorem sig_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : sig s ≤ 25 := by
  have h := sig_sq hs.1
  have := sig_nonneg s
  rw [psiB_eq] at h
  nlinarith [hs.2]

/-- **The surface weight is `dS/|∇s|`**: with the surface-of-revolution element
`dS = 2π R |∂_t(R, z)| dt` of the actual meridian curve and the actual `|∇s| = |∇ψ̃|/ψ̃_b`,
`dS/|∇s| = π √2 ψ̃_b / R dt` on every surface `0 < s ≤ 1`. -/
theorem surface_weight_eq {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (t : ℝ) :
    2 * π * RS 10 (sig s) t *
        √(deriv (RS 10 (sig s)) t ^ 2 + deriv (zS 10 (sig s)) t ^ 2) /
      (‖psiTGrad 10 (surfPt (sig s) t)‖ / psiB) = π * √2 * psiB / RS 10 (sig s) t := by
  have h0 := sig_pos hs.1
  have h25 := sig_le ⟨hs.1.le, hs.2⟩
  have hR := RS_pos h0.le (by linarith : 2 * sig s < 10 ^ 2) t
  have hG := SolovevMercierCertified.G2_pos h0 h25 t
  set G := ‖psiTGrad 10 (surfPt (sig s) t)‖ with hGdef
  have hG0 : 0 < G := by
    have hne : G ≠ 0 := by rintro h; rw [h] at hG; norm_num at hG
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h20 : 0 < √2 := by positivity
  have hsq : √(deriv (RS 10 (sig s)) t ^ 2 + deriv (zS 10 (sig s)) t ^ 2) =
      G / (√2 * RS 10 (sig s) t ^ 2) := by
    rw [SolovevMercierCertified.arclength_sq h0 h25 t, ← hGdef]
    rw [show G ^ 2 / (2 * RS 10 (sig s) t ^ 4) = (G / (√2 * RS 10 (sig s) t ^ 2)) ^ 2 by
      rw [div_pow, mul_pow, h2]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  have := psiB_pos
  field_simp
  rw [h2]

/-- **`surfInt` is the surface integral against `dS/|∇s|`** on every surface `0 < s ≤ 1`. -/
theorem surfInt_eq_area (f : Space → ℝ) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    surfInt f s = ∫ t in (-π)..π, f (surfPt (sig s) t) *
      (2 * π * RS 10 (sig s) t * √(deriv (RS 10 (sig s)) t ^ 2 + deriv (zS 10 (sig s)) t ^ 2) /
        (‖psiTGrad 10 (surfPt (sig s) t)‖ / psiB)) := by
  unfold surfInt
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [surface_weight_eq hs t]
  ring

/-- **`V'` is the derivative of the enclosed volume**: `d/ds volS(σ(s)) = V'(s)` for
`0 < s ≤ 1`, where `volS σ = 2π √2 ∫₀^σ σ' P(σ') dσ'` is the volume inside `ψ̃ = σ²` in the
coordinates `(σ, t)` of `SolovevMercierCertified` (Jacobian `jacobian_eq`). -/
theorem hasDerivAt_volume {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    HasDerivAt (fun s => volS (sig s)) (Vp s) s := by
  have h0 := sig_pos hs.1
  have h25 := sig_le ⟨hs.1.le, hs.2⟩
  have hV : HasDerivAt volS (2 * π * √2 * (sig s * Pint (sig s))) (sig s) :=
    (SolovevMercierCertified.hasDerivAt_primitive
      (continuousOn_id.mul SolovevMercierCertified.continuousOn_Pint) h0
      (by linarith)).const_mul _
  have hsig : HasDerivAt sig (psiB / (2 * sig s)) s := by
    have h1 : HasDerivAt (fun s => psiB * s) psiB s := by
      simpa using (hasDerivAt_id s).const_mul psiB
    exact h1.sqrt (mul_pos psiB_pos hs.1).ne'
  refine (hV.comp s hsig).congr_deriv ?_
  rw [Vp_eq, Pint_eq]
  unfold eps
  field_simp

/-! ## `solovev_one_plasma` on the actual geometry -/

section actual

open PlasmaLean.Fusion PlasmaLean.Kinetic PlasmaLean.Design.SolovevOnePlasma
  PlasmaLean.Design.SolovevBand WithLp

/-- **`solovev_one_plasma` for the actual Solov'ev flux geometry**: the third conjunct of
`SolovevBand.solovev_one_plasma` specialized to `solovevFluxGeometry` (the class
`IsSolovevGeometry` is no longer an assumption: `solovevFluxGeometry_isSolovev`). One field
`B` (reactor Solov'ev), kernel `ForceBalance` with pressure `p_eq + 40 kPa`; 3.5 MeV alphas
born at `s ≤ 3/11` stay in `s ≤ 1`; and every kernel solution of the quasilinear transport
equation on the actual flux-surface geometry with data in the band stays in the band, has a
hot core and pressure `≤ p_eq + 40 kPa` for all `t ≥ 0`. -/
theorem solovev_one_plasma_actual {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    (∀ x : Space, label x ≤ 1 →
      ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
        (ofLp (gradient (offsetPressure μ₀ 40000) x))) ∧
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
      e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → label (x 0) ≤ 3 / 11 →
      ∀ t, label (x t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ},
      8 / 5 ≤ χ₀ → χ₀ ≤ 33 / 20 → ∀ {Tedge : ℝ → ℝ} {u : RadialField},
      (∀ τ, 0 ≤ τ → ClassicalRadialSolution (solCoeffs solovevFluxGeometry sv χ₀) Tedge τ u) →
      (∀ s ∈ Icc (0 : ℝ) 1, Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ Tsup s) →
      (∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub s ≤ u.T s t ∧ u.T s t ≤ Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ x : Space, label x ≤ 1 → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤
          reactorPressure μ₀ x + 40000)) := by
  obtain ⟨h1, h2, h3⟩ := solovev_one_plasma hμ1 hμ2
  exact ⟨h1, h2, fun sv _ _ => h3 solovevFluxGeometry sv⟩

end actual

end PlasmaLean.Design.SolovevFluxGeometry
