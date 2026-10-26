/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.ValidatedQuadrature
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Validated quadrature for the reactor Solov'ev Mercier integrals (normalized form)

This module certifies, for EVERY `ε ∈ (0, 1/2]`, the normalized inequality

  `WellDominant ε :  Qn(ε) · IPhi(ε) < 3 · (3 Pn(ε) S5n(ε) - Qn(ε) S3n(ε))`,

which `PlasmaLean.Design.SolovevMercierCertified` shows to be exactly the dominant-well
hypothesis `∫|Ξ|²/|∇ψ|³ < s_ψ μ₀ p' V''` of `MercierGeneral.mercierIndex_pos_of_well` for the
reactor Solov'ev equilibrium on the flux surface `ψ̃ = s²`, `ε = 2s/L² = s/50`
(`ε ∈ (0, 1/2]` is the whole plasma `0 < ψ̃ ≤ L⁴/16`).

The quantities are one-dimensional integrals over the poloidal parameter `t` of the exact
surface parametrization (`v = 1 + ε sin t = R²/L²`):

* `Pn ε = ∫_{-π}^{π} v^{-1/2} dt`, `Qn ε = ∫ v^{-3/2} dt`,
* `S3n ε = -(1/ε) ∫ sin t · v^{-3/2} dt`, `S5n ε = -(1/ε) ∫ sin t · v^{-5/2} dt`,
* `IPhi ε = ∫ Phi(ρ, σ, ε, sin t) dt` with `ρ = Pn/Qn`, `σ = ε S3n/Qn` and
  `Phi = (κ₉ ρ² + 36 (y+σ)² v / G) / v^{3/2}`, `G = (2y + ε(1+y²))² + 2(1-y²) v²`,
  `κ₉ = 9 A² L²/F² = 441/400`.

**Method (all steps kernel-checked).**
1. `integral_sin_eq_rational` turns each `∫_{-π}^{π} f(sin t) dt` into
   `∫₀¹ (f(y)+f(-y)) · 4/(1+τ²) dτ`, `y = 2τ/(1+τ²)`.
2. The symmetric combinations `f(y)+f(-y)` are rewritten in closed forms of
   `p = √(1-ε²y²)` and `s = √(2+2p)` (`pairP` … `pairS5`); these have no cancellation, which
   keeps interval enclosures tight even on wide `ε`-cells. (`S3n`, `S5n` lose their `1/ε`.)
3. On each `ε`-cell `[e₀, e₁]` and each of `N` equal `τ`-cells, fixed-point interval
   arithmetic (`FIv`) encloses the integrand for ALL `ε` in the cell and ALL `τ` in the
   `τ`-cell; `integral_mem_sumIv` turns the cell enclosures into rigorous bounds on the
   integrals, uniformly in `ε ∈ [e₀, e₁]`. `ρ` and `σ` are enclosed from the scalar bounds and
   fed into the `Phi` quadrature.
4. `cellCheck N e₀ e₁` checks the resulting integer inequality; `cellCheck_sound` proves it
   implies `WellDominant ε` for every real `ε ∈ [e₀, e₁] ∩ (0, 1/2]`.
5. `wellDominant_cover`: 18 cells cover `[0, 1/2]` (each certified by its own explicit
   evaluation certificate of `cellCheck` with `N = 32`, `fiv_cert`; certified margins 3–6%, from
   the untrusted oracle `scripts/solovev_mercier_quadrature_oracle.py`, which mirrors the
   checker exactly and only proposes the cells).

Result: `normalized_well_dominance : ∀ ε, 0 < ε → ε ≤ 1/2 → WellDominant ε`.

Sanity: `cellCheck_rejects_wide` — one cell `[0, 1/2]` is NOT accepted at `N = 8` (the
checker is not vacuous); `cellCheck_rejects_axis_wide` — the near-axis cell `[0, 1/10]` fails
at `N = 32` (interval widening in `ε` is real, so the cover is genuinely refined); `Gn_pos`
(the denominator of `Phi` is positive on the plasma).
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevMercierQuadrature

open Real Set MeasureTheory intervalIntegral PlasmaLean.Certificates.ValidatedQuadrature
open PlasmaLean.Certificates.ValidatedQuadrature.FIv (Mem mem_add mem_sub mem_mul mem_sq mem_inv
  mem_sqrt mem_neg mem_ofInt mem_ofFrac)

/-! ## Normalized surface integrands -/

/-- `v^{-1/2}`, `v = 1 + ε y`. -/
@[expose] def fP (ε y : ℝ) : ℝ := (√(1 + ε * y))⁻¹

/-- `v^{-3/2}`. -/
@[expose] def fQ (ε y : ℝ) : ℝ := (√(1 + ε * y) ^ 3)⁻¹

/-- `-y v^{-3/2}`. -/
@[expose] def fS3 (ε y : ℝ) : ℝ := -(y * (√(1 + ε * y) ^ 3)⁻¹)

/-- `-y v^{-5/2}`. -/
@[expose] def fS5 (ε y : ℝ) : ℝ := -(y * (√(1 + ε * y) ^ 5)⁻¹)

/-- `Pn ε = ∫_{-π}^{π} (1 + ε sin t)^{-1/2} dt`. -/
@[expose] def Pn (ε : ℝ) : ℝ := ∫ t in (-π)..π, fP ε (Real.sin t)

/-- `Qn ε = ∫_{-π}^{π} (1 + ε sin t)^{-3/2} dt`. -/
@[expose] def Qn (ε : ℝ) : ℝ := ∫ t in (-π)..π, fQ ε (Real.sin t)

/-- `S3n ε = -(1/ε) ∫_{-π}^{π} sin t (1 + ε sin t)^{-3/2} dt`. -/
@[expose] def S3n (ε : ℝ) : ℝ := (∫ t in (-π)..π, fS3 ε (Real.sin t)) / ε

/-- `S5n ε = -(1/ε) ∫_{-π}^{π} sin t (1 + ε sin t)^{-5/2} dt`. -/
@[expose] def S5n (ε : ℝ) : ℝ := (∫ t in (-π)..π, fS5 ε (Real.sin t)) / ε

/-- The geometric denominator `G = (2y + ε(1+y²))² + 2(1-y²)(1+εy)²` (`= hn · v`). -/
@[expose] def Gn (ε y : ℝ) : ℝ := (2 * y + ε * (1 + y ^ 2)) ^ 2 + 2 * (1 - y ^ 2) * (1 + ε * y) ^ 2

/-- The normalized `|Ξ|²/|∇ψ|³` surface integrand
`Phi = (κ₉ ρ² + 36 (y+σ)² v/G) / v^{3/2}`, `κ₉ = 441/400`. -/
@[expose] def Phi (ρ σ ε y : ℝ) : ℝ :=
  (441 / 400 * ρ ^ 2 + 36 * (y + σ) ^ 2 * ((1 + ε * y) * (Gn ε y)⁻¹)) *
    ((1 + ε * y) * √(1 + ε * y))⁻¹

/-- `ρ = Pn/Qn`. -/
@[expose] def rhoN (ε : ℝ) : ℝ := Pn ε / Qn ε

/-- `σ = ε S3n/Qn`. -/
@[expose] def sigN (ε : ℝ) : ℝ := ε * (S3n ε / Qn ε)

/-- `IPhi ε = ∫_{-π}^{π} Phi(ρ, σ, ε, sin t) dt`. -/
@[expose] def IPhi (ε : ℝ) : ℝ := ∫ t in (-π)..π, Phi (rhoN ε) (sigN ε) ε (Real.sin t)

/-- The normalized dominant-well inequality. -/
@[expose] def WellDominant (ε : ℝ) : Prop :=
  Qn ε * IPhi ε < 3 * (3 * Pn ε * S5n ε - Qn ε * S3n ε)

/-! ## Symmetrized closed forms -/

/-- `p = √(1 - ε² y²) = √(1+εy) √(1-εy)`. -/
@[expose] def pN (ε y : ℝ) : ℝ := √(1 - (ε * y) ^ 2)

/-- `s = √(2 + 2p) = √(1+εy) + √(1-εy)`. -/
@[expose] def sN (ε y : ℝ) : ℝ := √(2 + 2 * pN ε y)

/-- `fP(y) + fP(-y) = s/p`. -/
@[expose] def pairP (ε y : ℝ) : ℝ := sN ε y * (pN ε y)⁻¹

/-- `fQ(y) + fQ(-y) = s (2 - p)/p³`. -/
@[expose] def pairQ (ε y : ℝ) : ℝ := sN ε y * (2 - pN ε y) * ((pN ε y)⁻¹ ^ 2 * (pN ε y)⁻¹)

/-- `(fS3(y) + fS3(-y))/ε = 2 y² (2 + p)/(s p³)`. -/
@[expose] def pairS3 (ε y : ℝ) : ℝ :=
  2 * y ^ 2 * (2 + pN ε y) * ((sN ε y)⁻¹ * ((pN ε y)⁻¹ ^ 2 * (pN ε y)⁻¹))

/-- `(fS5(y) + fS5(-y))/ε = 2 y² (4 + 2p - p²)/(s p⁵)`. -/
@[expose] def pairS5 (ε y : ℝ) : ℝ :=
  2 * y ^ 2 * (4 + 2 * pN ε y - pN ε y ^ 2) *
    ((sN ε y)⁻¹ * (((pN ε y)⁻¹ ^ 2 * (pN ε y)⁻¹) * (pN ε y)⁻¹ ^ 2))

section pairs

variable {ε y : ℝ}

/-- Common algebraic setting: `a = √(1+εy)`, `b = √(1-εy)`, `p = ab`, `s = a + b`. -/
theorem pair_setup (h1 : 0 < 1 + ε * y) (h2 : 0 < 1 - ε * y) :
    0 < √(1 + ε * y) ∧ 0 < √(1 - ε * y) ∧ √(1 + ε * y) ^ 2 = 1 + ε * y ∧
      √(1 - ε * y) ^ 2 = 1 - ε * y ∧ pN ε y = √(1 + ε * y) * √(1 - ε * y) ∧
      sN ε y = √(1 + ε * y) + √(1 - ε * y) := by
  have ha := Real.sqrt_pos.2 h1
  have hb := Real.sqrt_pos.2 h2
  have ha2 := Real.sq_sqrt h1.le
  have hb2 := Real.sq_sqrt h2.le
  have hp : pN ε y = √(1 + ε * y) * √(1 - ε * y) := by
    rw [pN, ← Real.sqrt_mul h1.le]; congr 1; ring
  refine ⟨ha, hb, ha2, hb2, hp, ?_⟩
  rw [sN, hp]
  rw [show 2 + 2 * (√(1 + ε * y) * √(1 - ε * y)) = (√(1 + ε * y) + √(1 - ε * y)) ^ 2 by
    nlinarith [ha2, hb2]]
  exact Real.sqrt_sq (by positivity)

/-- `1 + ε(-y) = 1 - εy`. -/
theorem neg_arg (ε y : ℝ) : 1 + ε * -y = 1 - ε * y := by ring

/-- Symmetrized `v^{-1/2}` in closed form. -/
theorem fP_pair (h1 : 0 < 1 + ε * y) (h2 : 0 < 1 - ε * y) :
    fP ε y + fP ε (-y) = pairP ε y := by
  obtain ⟨ha, hb, -, -, hp, hs⟩ := pair_setup h1 h2
  unfold fP pairP
  rw [neg_arg, hp, hs]
  field_simp
  ring

/-- Symmetrized `v^{-3/2}` in closed form. -/
theorem fQ_pair (h1 : 0 < 1 + ε * y) (h2 : 0 < 1 - ε * y) :
    fQ ε y + fQ ε (-y) = pairQ ε y := by
  obtain ⟨ha, hb, ha2, hb2, hp, hs⟩ := pair_setup h1 h2
  unfold fQ pairQ
  rw [neg_arg, hp, hs]
  set a := √(1 + ε * y)
  set b := √(1 - ε * y)
  have h2' : (2 : ℝ) - a * b = a ^ 2 + b ^ 2 - a * b := by rw [ha2, hb2]; ring
  rw [h2']
  field_simp
  ring

/-- Symmetrized `-y v^{-3/2}` in closed form (an explicit factor `ε` splits off). -/
theorem fS3_pair (h1 : 0 < 1 + ε * y) (h2 : 0 < 1 - ε * y) :
    fS3 ε y + fS3 ε (-y) = ε * pairS3 ε y := by
  obtain ⟨ha, hb, ha2, hb2, hp, hs⟩ := pair_setup h1 h2
  unfold fS3 pairS3
  rw [neg_arg, hp, hs]
  set a := √(1 + ε * y)
  set b := √(1 - ε * y)
  have key : ε * (2 * y ^ 2 * (2 + a * b)) = y * (a + b) * (a ^ 3 - b ^ 3) := by
    linear_combination (-(y * (2 + a * b)) - y * (a ^ 2 - b ^ 2)) * ha2 +
      (y * (2 + a * b) - y * (a ^ 2 - b ^ 2)) * hb2
  have hab : 0 < a + b := by positivity
  calc -(y * (a ^ 3)⁻¹) + -(-y * (b ^ 3)⁻¹)
      = y * (a + b) * (a ^ 3 - b ^ 3) / ((a + b) * (a * b) ^ 3) := by field_simp; ring
    _ = ε * (2 * y ^ 2 * (2 + a * b)) / ((a + b) * (a * b) ^ 3) := by rw [key]
    _ = _ := by field_simp

/-- Symmetrized `-y v^{-5/2}` in closed form (an explicit factor `ε` splits off). -/
theorem fS5_pair (h1 : 0 < 1 + ε * y) (h2 : 0 < 1 - ε * y) :
    fS5 ε y + fS5 ε (-y) = ε * pairS5 ε y := by
  obtain ⟨ha, hb, ha2, hb2, hp, hs⟩ := pair_setup h1 h2
  unfold fS5 pairS5
  rw [neg_arg, hp, hs]
  set a := √(1 + ε * y)
  set b := √(1 - ε * y)
  have key : ε * (2 * y ^ 2 * (4 + 2 * (a * b) - (a * b) ^ 2)) =
      y * (a + b) * (a ^ 5 - b ^ 5) := by
    have e1 : a ^ 2 - b ^ 2 = 2 * (ε * y) := by rw [ha2, hb2]; ring
    have e2 : a ^ 2 + b ^ 2 = 2 := by rw [ha2, hb2]; ring
    have e3 : a ^ 5 - b ^ 5 =
        (a - b) * ((a ^ 2 + b ^ 2) ^ 2 - (a * b) ^ 2 + a * b * (a ^ 2 + b ^ 2)) := by
      ring
    rw [e3, e2]
    have e4 : y * (a + b) * ((a - b) * (2 ^ 2 - (a * b) ^ 2 + a * b * 2)) =
        y * (a ^ 2 - b ^ 2) * (4 + 2 * (a * b) - (a * b) ^ 2) := by ring
    rw [e4, e1]
    ring
  have hab : 0 < a + b := by positivity
  calc -(y * (a ^ 5)⁻¹) + -(-y * (b ^ 5)⁻¹)
      = y * (a + b) * (a ^ 5 - b ^ 5) / ((a + b) * (a * b) ^ 5) := by field_simp; ring
    _ = ε * (2 * y ^ 2 * (4 + 2 * (a * b) - (a * b) ^ 2)) / ((a + b) * (a * b) ^ 5) := by
        rw [key]
    _ = _ := by field_simp

end pairs

/-! ## Positivity and continuity on the plasma range `0 < ε ≤ 1/2`, `|y| ≤ 1` -/

/-- `1 + εy ≥ 1/2` on the plasma range. -/
theorem one_add_pos {ε y : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (hy : y ∈ Icc (-1 : ℝ) 1) :
    1 / 2 ≤ 1 + ε * y := by
  nlinarith [hy.1, hy.2, mul_nonneg hε (show 0 ≤ y + 1 by linarith [hy.1])]

/-- `1 - εy ≥ 1/2` on the plasma range. -/
theorem one_sub_pos {ε y : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (hy : y ∈ Icc (-1 : ℝ) 1) :
    1 / 2 ≤ 1 - ε * y := by
  nlinarith [hy.1, hy.2, mul_nonneg hε (show 0 ≤ 1 - y by linarith [hy.2])]

/-- The denominator `G` of `Phi` is positive on the plasma range. -/
theorem Gn_pos {ε y : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (hy : y ∈ Icc (-1 : ℝ) 1) :
    0 < Gn ε y := by
  have hv := one_add_pos hε hε' hy
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have hsecond : 0 ≤ 2 * (1 - y ^ 2) * (1 + ε * y) ^ 2 := by
    have : 0 ≤ 1 - y ^ 2 := by linarith
    positivity
  unfold Gn
  rcases le_or_gt (y ^ 2) (3 / 4) with h | h
  · have h1 : 0 < 1 - y ^ 2 := by linarith
    have : 0 < 2 * (1 - y ^ 2) * (1 + ε * y) ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * y + ε * (1 + y ^ 2))]
  · rcases le_or_gt 0 y with hy0 | hy0
    · have hpos : 0 < y := by
        rcases hy0.lt_or_eq with h' | h'
        · exact h'
        · rw [← h'] at h; norm_num at h
      have : 0 < 2 * y + ε * (1 + y ^ 2) := by positivity
      nlinarith [sq_pos_of_pos this]
    · have hyle : y < -4 / 5 := by nlinarith
      have hneg : 2 * y + ε * (1 + y ^ 2) < 0 := by
        have : ε * (1 + y ^ 2) ≤ 1 / 2 * (1 + y ^ 2) :=
          mul_le_mul_of_nonneg_right hε' (by positivity)
        nlinarith
      nlinarith [sq_pos_of_neg hneg]

/-- Continuity of the `Pn` integrand on `[-1, 1]`. -/
theorem continuousOn_fP {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    ContinuousOn (fP ε) (Icc (-1) 1) := by
  unfold fP
  exact ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop))
    (fun y hy => (Real.sqrt_pos.2 (by linarith [one_add_pos hε hε' hy])).ne')

/-- Continuity of the `Qn` integrand on `[-1, 1]`. -/
theorem continuousOn_fQ {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    ContinuousOn (fQ ε) (Icc (-1) 1) := by
  unfold fQ
  exact ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop))
    (fun y hy => (pow_pos (Real.sqrt_pos.2 (by linarith [one_add_pos hε hε' hy])) 3).ne')

/-- Continuity of the `S3n` integrand on `[-1, 1]`. -/
theorem continuousOn_fS3 {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    ContinuousOn (fS3 ε) (Icc (-1) 1) := by
  unfold fS3
  refine (continuousOn_id.mul (ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop))
    (fun y hy => (pow_pos (Real.sqrt_pos.2 (by linarith [one_add_pos hε hε' hy])) 3).ne'))).neg

/-- Continuity of the `S5n` integrand on `[-1, 1]`. -/
theorem continuousOn_fS5 {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    ContinuousOn (fS5 ε) (Icc (-1) 1) := by
  unfold fS5
  refine (continuousOn_id.mul (ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop))
    (fun y hy => (pow_pos (Real.sqrt_pos.2 (by linarith [one_add_pos hε hε' hy])) 5).ne'))).neg

/-- Continuity of `Phi` in `y` on `[-1, 1]` (uses `Gn_pos`). -/
theorem continuousOn_Phi (ρ σ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    ContinuousOn (Phi ρ σ ε) (Icc (-1) 1) := by
  unfold Phi
  refine ContinuousOn.mul ?_ ?_
  · refine continuousOn_const.add (ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
      (ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
        (ContinuousOn.inv₀ (Continuous.continuousOn (by unfold Gn; fun_prop))
          (fun y hy => (Gn_pos hε hε' hy).ne'))))
  · refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) (fun y hy => ?_)
    have h := one_add_pos hε hε' hy
    have : 0 < (1 + ε * y) * √(1 + ε * y) := mul_pos (by linarith) (Real.sqrt_pos.2 (by linarith))
    exact this.ne'

/-! ## From `∫ f(sin t)` to `∫₀¹ pair(y(τ)) · 4/(1+τ²)` -/

/-- The quadrature weight `4/(1+τ²)`. -/
@[expose] def wt (τ : ℝ) : ℝ := 4 / (1 + τ ^ 2)

/-- Representation of a `sin`-integral through a symmetrized closed form `g`, together with
integrability of the new integrand. -/
theorem rep_sin {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hg : ∀ y ∈ Icc (-1 : ℝ) 1, f y + f (-y) = g y) :
    ∫ t in (-π)..π, f (Real.sin t) = ∫ τ in (0 : ℝ)..1, g (wy τ) * wt τ ∧
      IntervalIntegrable (fun τ => g (wy τ) * wt τ) volume 0 1 := by
  have hfun : (fun τ => g (wy τ) * wt τ) = fun τ => (f (wy τ) + f (-wy τ)) * wt τ :=
    funext fun τ => by rw [hg _ (wy_mem τ)]
  have hfw : Continuous (fun τ => f (wy τ)) := hf.comp_continuous continuous_wy wy_mem
  have hfw' : Continuous (fun τ => f (-wy τ)) :=
    hf.comp_continuous continuous_wy.neg (fun τ => by
      have := wy_mem τ; constructor <;> linarith [this.1, this.2])
  have hwt : Continuous wt := by
    unfold wt; exact Continuous.div continuous_const (by fun_prop) (fun x => by positivity)
  refine ⟨?_, ?_⟩
  · rw [integral_sin_eq_rational hf, hfun, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro τ _
    simp only [wt]
    have : 0 < 1 + τ ^ 2 := by positivity
    field_simp
  · rw [hfun]
    exact ((hfw.add hfw').mul hwt).intervalIntegrable 0 1

section reps

variable {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
include hε hε'

/-- `Pn` as a `[0,1]` integral of the symmetrized closed form, with integrability. -/
theorem Pn_rep : Pn ε = ∫ τ in (0 : ℝ)..1, pairP ε (wy τ) * wt τ ∧
    IntervalIntegrable (fun τ => pairP ε (wy τ) * wt τ) volume 0 1 :=
  rep_sin (continuousOn_fP hε.le hε') (fun y hy =>
    fP_pair (by linarith [one_add_pos hε.le hε' hy]) (by linarith [one_sub_pos hε.le hε' hy]))

/-- `Qn` as a `[0,1]` integral of the symmetrized closed form, with integrability. -/
theorem Qn_rep : Qn ε = ∫ τ in (0 : ℝ)..1, pairQ ε (wy τ) * wt τ ∧
    IntervalIntegrable (fun τ => pairQ ε (wy τ) * wt τ) volume 0 1 :=
  rep_sin (continuousOn_fQ hε.le hε') (fun y hy =>
    fQ_pair (by linarith [one_add_pos hε.le hε' hy]) (by linarith [one_sub_pos hε.le hε' hy]))

/-- `S3n` as a `[0,1]` integral of the symmetrized closed form (the `1/ε` cancels). -/
theorem S3n_rep : S3n ε = ∫ τ in (0 : ℝ)..1, pairS3 ε (wy τ) * wt τ ∧
    IntervalIntegrable (fun τ => pairS3 ε (wy τ) * wt τ) volume 0 1 := by
  have h := rep_sin (g := fun y => ε * pairS3 ε y) (continuousOn_fS3 hε.le hε') (fun y hy =>
    fS3_pair (by linarith [one_add_pos hε.le hε' hy]) (by linarith [one_sub_pos hε.le hε' hy]))
  have e : (fun τ => ε * pairS3 ε (wy τ) * wt τ) = fun τ => ε * (pairS3 ε (wy τ) * wt τ) :=
    funext fun τ => by ring
  simp only [e] at h
  refine ⟨?_, ?_⟩
  · unfold S3n
    rw [h.1, intervalIntegral.integral_const_mul]
    field_simp
  · have := h.2.const_mul ε⁻¹
    refine this.congr (fun τ _ => ?_)
    field_simp

/-- `S5n` as a `[0,1]` integral of the symmetrized closed form (the `1/ε` cancels). -/
theorem S5n_rep : S5n ε = ∫ τ in (0 : ℝ)..1, pairS5 ε (wy τ) * wt τ ∧
    IntervalIntegrable (fun τ => pairS5 ε (wy τ) * wt τ) volume 0 1 := by
  have h := rep_sin (g := fun y => ε * pairS5 ε y) (continuousOn_fS5 hε.le hε') (fun y hy =>
    fS5_pair (by linarith [one_add_pos hε.le hε' hy]) (by linarith [one_sub_pos hε.le hε' hy]))
  have e : (fun τ => ε * pairS5 ε (wy τ) * wt τ) = fun τ => ε * (pairS5 ε (wy τ) * wt τ) :=
    funext fun τ => by ring
  simp only [e] at h
  refine ⟨?_, ?_⟩
  · unfold S5n
    rw [h.1, intervalIntegral.integral_const_mul]
    field_simp
  · have := h.2.const_mul ε⁻¹
    refine this.congr (fun τ _ => ?_)
    field_simp

/-- The `Phi` integral as a `[0,1]` integral of `Phi(y) + Phi(-y)`, with integrability. -/
theorem IPhi_rep (ρ σ : ℝ) :
    ∫ t in (-π)..π, Phi ρ σ ε (Real.sin t) =
      ∫ τ in (0 : ℝ)..1, (Phi ρ σ ε (wy τ) + Phi ρ σ ε (-wy τ)) * wt τ ∧
    IntervalIntegrable (fun τ => (Phi ρ σ ε (wy τ) + Phi ρ σ ε (-wy τ)) * wt τ) volume 0 1 :=
  rep_sin (g := fun y => Phi ρ σ ε y + Phi ρ σ ε (-y)) (continuousOn_Phi ρ σ hε.le hε')
    (fun _ _ => rfl)

end reps

/-! ## Interval evaluators (mirroring the real expressions operation by operation) -/

/-- The constant `1`. -/
@[expose] def one : FIv := FIv.ofInt 1
/-- The constant `2`. -/
@[expose] def two : FIv := FIv.ofInt 2
/-- The constant `4`. -/
@[expose] def four : FIv := FIv.ofInt 4
/-- The constant `36`. -/
@[expose] def c36 : FIv := FIv.ofInt 36
/-- The constant `κ₉ = 441/400`. -/
@[expose] def k9 : FIv := FIv.ofFrac 441 400

/-- Soundness of the constant `1`. -/
theorem mem_one : one.Mem 1 := by unfold one; simpa using mem_ofInt 1
/-- Soundness of the constant `2`. -/
theorem mem_two : two.Mem 2 := by unfold two; simpa using mem_ofInt 2
/-- Soundness of the constant `4`. -/
theorem mem_four : four.Mem 4 := by unfold four; simpa using mem_ofInt 4
/-- Soundness of the constant `36`. -/
theorem mem_c36 : c36.Mem 36 := by unfold c36; simpa using mem_ofInt 36
/-- Soundness of the constant `441/400`. -/
theorem mem_k9 : k9.Mem (441 / 400) := by
  unfold k9
  have := mem_ofFrac 441 400
  norm_num at this
  exact this

/-- Enclosure of `p`. -/
@[expose] def evp (E Y : FIv) : FIv := (one.sub (E.mul Y).sq).sqrt
/-- Enclosure of `s`. -/
@[expose] def evs (E Y : FIv) : FIv := (two.add (two.mul (evp E Y))).sqrt
/-- Enclosure of `pairP · wt`. -/
@[expose] def evP (E Y W : FIv) : FIv := ((evs E Y).mul (evp E Y).inv).mul W
/-- Enclosure of `pairQ · wt`. -/
@[expose] def evQ (E Y W : FIv) : FIv :=
  (((evs E Y).mul (two.sub (evp E Y))).mul ((evp E Y).inv.sq.mul (evp E Y).inv)).mul W
/-- Enclosure of `pairS3 · wt`. -/
@[expose] def evS3 (E Y W : FIv) : FIv :=
  (((two.mul Y.sq).mul (two.add (evp E Y))).mul
    ((evs E Y).inv.mul ((evp E Y).inv.sq.mul (evp E Y).inv))).mul W
/-- Enclosure of `pairS5 · wt`. -/
@[expose] def evS5 (E Y W : FIv) : FIv :=
  (((two.mul Y.sq).mul ((four.add (two.mul (evp E Y))).sub (evp E Y).sq)).mul
    ((evs E Y).inv.mul (((evp E Y).inv.sq.mul (evp E Y).inv).mul (evp E Y).inv.sq))).mul W
/-- Enclosure of `Phi ρ σ ε y` from enclosures of `ρ²`, `σ`, `ε`, `y`. -/
@[expose] def evPhi (R2 Sg E Y : FIv) : FIv :=
  ((k9.mul R2).add ((c36.mul (Y.add Sg).sq).mul ((one.add (E.mul Y)).mul
    ((((two.mul Y).add (E.mul (one.add Y.sq))).sq.add
      ((two.mul (one.sub Y.sq)).mul (one.add (E.mul Y)).sq)).inv)))).mul
    ((one.add (E.mul Y)).mul (one.add (E.mul Y)).sqrt).inv

section evals

variable {E Y W R2 Sg : FIv} {ε y w ρ2 σ : ℝ}

/-- Soundness of the `p` enclosure. -/
theorem mem_evp (hE : E.Mem ε) (hY : Y.Mem y) : (evp E Y).Mem (pN ε y) :=
  mem_sqrt (mem_sub mem_one (mem_sq (mem_mul hE hY)))

/-- Soundness of the `s` enclosure. -/
theorem mem_evs (hE : E.Mem ε) (hY : Y.Mem y) : (evs E Y).Mem (sN ε y) :=
  mem_sqrt (mem_add mem_two (mem_mul mem_two (mem_evp hE hY)))

/-- Soundness of the `Pn` cell enclosure. -/
theorem mem_evP (hE : E.Mem ε) (hY : Y.Mem y) (hW : W.Mem w) :
    (evP E Y W).Mem (pairP ε y * w) :=
  mem_mul (mem_mul (mem_evs hE hY) (mem_inv (mem_evp hE hY))) hW

/-- Soundness of the `Qn` cell enclosure. -/
theorem mem_evQ (hE : E.Mem ε) (hY : Y.Mem y) (hW : W.Mem w) :
    (evQ E Y W).Mem (pairQ ε y * w) :=
  have hp := mem_evp hE hY
  mem_mul (mem_mul (mem_mul (mem_evs hE hY) (mem_sub mem_two hp))
    (mem_mul (mem_sq (mem_inv hp)) (mem_inv hp))) hW

/-- Soundness of the `S3n` cell enclosure. -/
theorem mem_evS3 (hE : E.Mem ε) (hY : Y.Mem y) (hW : W.Mem w) :
    (evS3 E Y W).Mem (pairS3 ε y * w) :=
  have hp := mem_evp hE hY
  mem_mul (mem_mul (mem_mul (mem_mul mem_two (mem_sq hY)) (mem_add mem_two hp))
    (mem_mul (mem_inv (mem_evs hE hY)) (mem_mul (mem_sq (mem_inv hp)) (mem_inv hp)))) hW

/-- Soundness of the `S5n` cell enclosure. -/
theorem mem_evS5 (hE : E.Mem ε) (hY : Y.Mem y) (hW : W.Mem w) :
    (evS5 E Y W).Mem (pairS5 ε y * w) :=
  have hp := mem_evp hE hY
  mem_mul (mem_mul (mem_mul (mem_mul mem_two (mem_sq hY))
      (mem_sub (mem_add mem_four (mem_mul mem_two hp)) (mem_sq hp)))
    (mem_mul (mem_inv (mem_evs hE hY))
      (mem_mul (mem_mul (mem_sq (mem_inv hp)) (mem_inv hp)) (mem_sq (mem_inv hp))))) hW

/-- Soundness of the `Phi` enclosure. -/
theorem mem_evPhi (hR : R2.Mem ρ2) (hS : Sg.Mem σ) (hE : E.Mem ε) (hY : Y.Mem y) (ρ : ℝ)
    (hρ : ρ2 = ρ ^ 2) : (evPhi R2 Sg E Y).Mem (Phi ρ σ ε y) := by
  subst hρ
  have hv : (one.add (E.mul Y)).Mem (1 + ε * y) := mem_add mem_one (mem_mul hE hY)
  exact mem_mul (mem_add (mem_mul mem_k9 hR) (mem_mul (mem_mul mem_c36 (mem_sq (mem_add hY hS)))
    (mem_mul hv (mem_inv (mem_add (mem_sq (mem_add (mem_mul mem_two hY)
      (mem_mul hE (mem_add mem_one (mem_sq hY)))))
      (mem_mul (mem_mul mem_two (mem_sub mem_one (mem_sq hY))) (mem_sq hv)))))))
    (mem_inv (mem_mul hv (mem_sqrt hv)))

end evals

/-! ## `τ`-cell tables -/

/-- Enclosure of `y(τ) = 2τ/(1+τ²)` on the cell `[i/N, (i+1)/N]` (monotone there). -/
@[expose] def Ycell (N i : ℕ) : FIv :=
  ⟨(2 * (i : ℤ) * N * fxScale) / ((N : ℤ) ^ 2 + (i : ℤ) ^ 2),
    -((-(2 * ((i : ℤ) + 1) * N * fxScale)) / ((N : ℤ) ^ 2 + ((i : ℤ) + 1) ^ 2)), true⟩

/-- Enclosure of the weight `4/(1+τ²)` on the cell `[i/N, (i+1)/N]` (decreasing there). -/
@[expose] def Wcell (N i : ℕ) : FIv :=
  ⟨(4 * (N : ℤ) ^ 2 * fxScale) / ((N : ℤ) ^ 2 + ((i : ℤ) + 1) ^ 2),
    -((-(4 * (N : ℤ) ^ 2 * fxScale)) / ((N : ℤ) ^ 2 + (i : ℤ) ^ 2)), true⟩

/-- `y(j/N) = 2jN/(N² + j²)`. -/
theorem wy_frac {N : ℕ} (hN : 0 < N) (j : ℝ) :
    wy (j / N) = 2 * j * N / ((N : ℝ) ^ 2 + j ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold wy
  field_simp

/-- `4/(1 + (j/N)²) = 4N²/(N² + j²)`. -/
theorem wt_frac {N : ℕ} (hN : 0 < N) (j : ℝ) : wt (j / N) = 4 * N ^ 2 / ((N : ℝ) ^ 2 + j ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold wt
  field_simp

/-- The tables `Ycell`, `Wcell` enclose `y(τ)` and `4/(1+τ²)` on the whole `τ`-cell. -/
theorem mem_cells {N i : ℕ} (hN : 0 < N) (hi : i < N) {τ : ℝ}
    (hτ : τ ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :
    (Ycell N i).Mem (wy τ) ∧ (Wcell N i).Mem (wt τ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hS := fxScale_pos
  have hi1 : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  have ht0 : 0 ≤ (i : ℝ) / N := by positivity
  have ht1 : ((i : ℝ) + 1) / N ≤ 1 := by rw [div_le_one hN']; exact hi1
  have hτ0 : 0 ≤ τ := le_trans ht0 hτ.1
  have hd1 : (0 : ℤ) < (N : ℤ) ^ 2 + (i : ℤ) ^ 2 := by positivity
  have hd2 : (0 : ℤ) < (N : ℤ) ^ 2 + ((i : ℤ) + 1) ^ 2 := by positivity
  constructor
  · rw [FIv.mem_iff]
    intro _
    dsimp only [Ycell]
    have l1 := fdiv_le (2 * (i : ℤ) * N * fxScale) _ hd1
    have l2 := le_cdiv (2 * ((i : ℤ) + 1) * N * fxScale) _ hd2
    have m1 := wy_mono ht0 hτ.1 (le_trans hτ.2 ht1)
    have m2 := wy_mono hτ0 hτ.2 ht1
    rw [wy_frac hN] at m1 m2
    push_cast at l1 l2 ⊢
    constructor
    · calc _ ≤ _ := l1
        _ = fxScale * (2 * i * N / ((N : ℝ) ^ 2 + (i : ℝ) ^ 2)) := by ring
        _ ≤ _ := by gcongr
    · calc fxScale * wy τ ≤
            fxScale * (2 * ((i : ℝ) + 1) * N / ((N : ℝ) ^ 2 + ((i : ℝ) + 1) ^ 2)) := by
            gcongr
        _ = _ := by ring
        _ ≤ _ := l2
  · rw [FIv.mem_iff]
    intro _
    dsimp only [Wcell]
    have l1 := fdiv_le (4 * (N : ℤ) ^ 2 * fxScale) _ hd2
    have l2 := le_cdiv (4 * (N : ℤ) ^ 2 * fxScale) _ hd1
    have m1 : wt (((i : ℝ) + 1) / N) ≤ wt τ := by
      unfold wt
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have := hτ.2
      nlinarith
    have m2 : wt τ ≤ wt ((i : ℝ) / N) := by
      unfold wt
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have := hτ.1
      nlinarith
    rw [wt_frac hN] at m1 m2
    push_cast at l1 l2 ⊢
    constructor
    · calc _ ≤ _ := l1
        _ = fxScale * (4 * (N : ℝ) ^ 2 / ((N : ℝ) ^ 2 + ((i : ℝ) + 1) ^ 2)) := by ring
        _ ≤ _ := by gcongr
    · calc fxScale * wt τ ≤ fxScale * (4 * (N : ℝ) ^ 2 / ((N : ℝ) ^ 2 + (i : ℝ) ^ 2)) := by gcongr
        _ = _ := by ring
        _ ≤ _ := l2

/-! ## The per-cell checker -/

/-- Lower fixed-point rounding of a rational. -/
@[expose] def ofQlo (q : ℚ) : ℤ := (q.num * fxScale) / q.den

/-- Upper fixed-point rounding of a rational. -/
@[expose] def ofQhi (q : ℚ) : ℤ := -((-(q.num * fxScale)) / q.den)

/-- The `ε`-cell enclosure `[e₀, e₁]`. -/
@[expose] def Ecell (e0 e1 : ℚ) : FIv := ⟨ofQlo e0, ofQhi e1, true⟩

/-- The `ε`-cell enclosure contains every `ε ∈ [e₀, e₁]`. -/
theorem mem_Ecell {e0 e1 : ℚ} {ε : ℝ} (h0 : (e0 : ℝ) ≤ ε) (h1 : ε ≤ e1) :
    (Ecell e0 e1).Mem ε := by
  rw [FIv.mem_iff]
  intro _
  have hS := fxScale_pos
  have hd0 : (0 : ℤ) < e0.den := by exact_mod_cast e0.pos
  have hd1 : (0 : ℤ) < e1.den := by exact_mod_cast e1.pos
  have l1 := fdiv_le (e0.num * fxScale) _ hd0
  have l2 := le_cdiv (e1.num * fxScale) _ hd1
  dsimp only [Ecell, ofQlo, ofQhi]
  rw [Rat.cast_def] at h0 h1
  push_cast at l1 l2 h0 h1 ⊢
  constructor
  · calc _ ≤ _ := l1
      _ = fxScale * ((e0.num : ℝ) / e0.den) := by ring
      _ ≤ _ := by gcongr
  · calc fxScale * ε ≤ fxScale * ((e1.num : ℝ) / e1.den) := by gcongr
      _ = _ := by ring
      _ ≤ _ := l2

/-- Scalar quadrature sums. -/
@[expose] def sumP (E : FIv) (N : ℕ) : FIv := sumIv (fun i => evP E (Ycell N i) (Wcell N i)) N
/-- Scalar quadrature sums. -/
@[expose] def sumQ (E : FIv) (N : ℕ) : FIv := sumIv (fun i => evQ E (Ycell N i) (Wcell N i)) N
/-- Scalar quadrature sums. -/
@[expose] def sumS3 (E : FIv) (N : ℕ) : FIv := sumIv (fun i => evS3 E (Ycell N i) (Wcell N i)) N
/-- Scalar quadrature sums. -/
@[expose] def sumS5 (E : FIv) (N : ℕ) : FIv := sumIv (fun i => evS5 E (Ycell N i) (Wcell N i)) N

/-- Enclosure of a quotient `a/b` of two quadrature sums (`[a.lo/b.hi, a.hi/b.lo]`, valid for
nonnegative `a` and positive `b`). -/
@[expose] def ratio (a b : FIv) : FIv :=
  ⟨(a.lo * fxScale) / b.hi, -((-(a.hi * fxScale)) / b.lo), true⟩

/-- The `Phi` quadrature sum, given enclosures of `ρ²` and `σ`. -/
@[expose] def sumPhi (R2 Sg E : FIv) (N : ℕ) : FIv :=
  sumIv (fun i => ((evPhi R2 Sg E (Ycell N i)).add (evPhi R2 Sg E (Ycell N i).neg)).mul
    (Wcell N i)) N

/-- Final integer comparison for given sums. -/
@[expose] def finalCheck (N : ℕ) (sP sQ s3 s5 sF : FIv) : Bool :=
  decide (0 < N) && sP.ok && sQ.ok && s3.ok && s5.ok && sF.ok && decide (0 ≤ sP.lo) &&
    decide (0 < sQ.lo) && decide (0 ≤ s3.lo) && decide (0 ≤ s5.lo) && decide (0 ≤ sF.hi) &&
    decide (sQ.hi * sF.hi < 3 * (3 * sP.lo * s5.lo - sQ.hi * s3.hi))

/-- **The per-cell checker** for `ε ∈ [e₀, e₁]` with `N` `τ`-cells. -/
@[expose] def cellCheck (N : ℕ) (e0 e1 : ℚ) : Bool :=
  finalCheck N (sumP (Ecell e0 e1) N) (sumQ (Ecell e0 e1) N) (sumS3 (Ecell e0 e1) N)
    (sumS5 (Ecell e0 e1) N)
    (sumPhi (ratio (sumP (Ecell e0 e1) N) (sumQ (Ecell e0 e1) N)).sq
      ((Ecell e0 e1).mul (ratio (sumS3 (Ecell e0 e1) N) (sumQ (Ecell e0 e1) N)))
      (Ecell e0 e1) N)

/-! ## Soundness -/

/-- Generic: a validated `[0,1]` quadrature of `g` from enclosures `c i` valid on every cell. -/
theorem quad_bounds {g : ℝ → ℝ} {N : ℕ} (hN : 0 < N) (c : ℕ → FIv)
    (hg : IntervalIntegrable g volume 0 1)
    (hc : ∀ i < N, ∀ τ ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N), (c i).Mem (g τ))
    (hok : (sumIv c N).ok = true) :
    ((sumIv c N).lo : ℝ) / (fxScale * N) ≤ ∫ τ in (0 : ℝ)..1, g τ ∧
      ∫ τ in (0 : ℝ)..1, g τ ≤ ((sumIv c N).hi : ℝ) / (fxScale * N) :=
  integral_mem_sumIv hN c hg hc hok

/-- Enclosure of a quotient from enclosures of numerator and denominator. -/
theorem mem_ratio {a b : FIv} {D x z : ℝ} (hD : 0 < D) (hx : (a.lo : ℝ) / D ≤ x)
    (hx' : x ≤ (a.hi : ℝ) / D) (hz : (b.lo : ℝ) / D ≤ z) (hz' : z ≤ (b.hi : ℝ) / D)
    (ha : 0 ≤ a.lo) (hb : 0 < b.lo) : (ratio a b).Mem (x / z) := by
  rw [FIv.mem_iff]
  intro _
  have hS := fxScale_pos
  have hb' : (0 : ℝ) < b.lo := by exact_mod_cast hb
  have hbhi : (0 : ℤ) < b.hi := by
    have : (b.lo : ℝ) ≤ b.hi := by
      have := le_trans hz hz'
      rwa [div_le_div_iff_of_pos_right hD] at this
    exact_mod_cast lt_of_lt_of_le hb' this
  have hbhi' : (0 : ℝ) < b.hi := by exact_mod_cast hbhi
  have ha' : (0 : ℝ) ≤ a.lo := by exact_mod_cast ha
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hz
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have l1 := fdiv_le (a.lo * fxScale) b.hi hbhi
  have l2 := le_cdiv (a.hi * fxScale) b.lo hb
  dsimp only [ratio]
  push_cast at l1 l2 ⊢
  -- x / z ≥ (a.lo/D)/(b.hi/D) = a.lo / b.hi, and ≤ a.hi / b.lo
  have e1 : (a.lo : ℝ) / b.hi = ((a.lo : ℝ) / D) / ((b.hi : ℝ) / D) := by field_simp
  have e2 : (a.hi : ℝ) / b.lo = ((a.hi : ℝ) / D) / ((b.lo : ℝ) / D) := by field_simp
  have b1 : (a.lo : ℝ) / b.hi ≤ x / z := by
    rw [e1]
    calc ((a.lo : ℝ) / D) / ((b.hi : ℝ) / D) ≤ x / ((b.hi : ℝ) / D) := by gcongr
      _ ≤ x / z := by gcongr
  have b2 : x / z ≤ (a.hi : ℝ) / b.lo := by
    rw [e2]
    calc x / z ≤ x / ((b.lo : ℝ) / D) := by gcongr
      _ ≤ ((a.hi : ℝ) / D) / ((b.lo : ℝ) / D) := by gcongr
  constructor
  · calc _ ≤ _ := l1
      _ = fxScale * ((a.lo : ℝ) / b.hi) := by ring
      _ ≤ _ := by gcongr
  · calc fxScale * (x / z) ≤ fxScale * ((a.hi : ℝ) / b.lo) := by gcongr
      _ = _ := by ring
      _ ≤ _ := l2

/-- **Soundness of the per-cell checker**: acceptance proves `WellDominant ε` for every real
`ε ∈ [e₀, e₁]` with `0 < ε ≤ 1/2`. -/
theorem cellCheck_sound {N : ℕ} {e0 e1 : ℚ} (h : cellCheck N e0 e1 = true) {ε : ℝ}
    (h0 : (e0 : ℝ) ≤ ε) (h1 : ε ≤ e1) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) : WellDominant ε := by
  set E := Ecell e0 e1 with hEdef
  have hE : E.Mem ε := mem_Ecell h0 h1
  unfold cellCheck finalCheck at h
  simp only [← hEdef, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, okP⟩, okQ⟩, ok3⟩, ok5⟩, okF⟩, hPlo⟩, hQlo⟩, h3lo⟩, h5lo⟩, hFhi⟩, hfin⟩ :=
    h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hS := fxScale_pos
  set D : ℝ := fxScale * N with hD
  have hDpos : 0 < D := by positivity
  have cells := fun i (hi : i < N) τ (hτ : τ ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) =>
    mem_cells hN hi hτ
  -- scalar bounds
  obtain ⟨Pe, Pi⟩ := Pn_rep hε hε'
  obtain ⟨Qe, Qi⟩ := Qn_rep hε hε'
  obtain ⟨S3e, S3i⟩ := S3n_rep hε hε'
  obtain ⟨S5e, S5i⟩ := S5n_rep hε hε'
  have bP := quad_bounds hN _ Pi (fun i hi τ hτ =>
    mem_evP hE (cells i hi τ hτ).1 (cells i hi τ hτ).2) okP
  have bQ := quad_bounds hN _ Qi (fun i hi τ hτ =>
    mem_evQ hE (cells i hi τ hτ).1 (cells i hi τ hτ).2) okQ
  have b3 := quad_bounds hN _ S3i (fun i hi τ hτ =>
    mem_evS3 hE (cells i hi τ hτ).1 (cells i hi τ hτ).2) ok3
  have b5 := quad_bounds hN _ S5i (fun i hi τ hτ =>
    mem_evS5 hE (cells i hi τ hτ).1 (cells i hi τ hτ).2) ok5
  rw [← Pe] at bP
  rw [← Qe] at bQ
  rw [← S3e] at b3
  rw [← S5e] at b5
  change ((sumP E N).lo : ℝ) / D ≤ Pn ε ∧ Pn ε ≤ ((sumP E N).hi : ℝ) / D at bP
  change ((sumQ E N).lo : ℝ) / D ≤ Qn ε ∧ Qn ε ≤ ((sumQ E N).hi : ℝ) / D at bQ
  change ((sumS3 E N).lo : ℝ) / D ≤ S3n ε ∧ S3n ε ≤ ((sumS3 E N).hi : ℝ) / D at b3
  change ((sumS5 E N).lo : ℝ) / D ≤ S5n ε ∧ S5n ε ≤ ((sumS5 E N).hi : ℝ) / D at b5
  -- ρ and σ
  have hR : (ratio (sumP E N) (sumQ E N)).Mem (rhoN ε) :=
    mem_ratio hDpos bP.1 bP.2 bQ.1 bQ.2 hPlo hQlo
  have hK : (ratio (sumS3 E N) (sumQ E N)).Mem (S3n ε / Qn ε) :=
    mem_ratio hDpos b3.1 b3.2 bQ.1 bQ.2 h3lo hQlo
  have hSg : (E.mul (ratio (sumS3 E N) (sumQ E N))).Mem (sigN ε) := mem_mul hE hK
  have hR2 := mem_sq hR
  -- the Phi quadrature
  obtain ⟨Fe, Fi⟩ := IPhi_rep hε hε' (rhoN ε) (sigN ε)
  have bF := quad_bounds hN _ Fi (fun i hi τ hτ => mem_mul
    (mem_add (mem_evPhi hR2 hSg hE (cells i hi τ hτ).1 (rhoN ε) rfl)
      (mem_evPhi hR2 hSg hE (mem_neg (cells i hi τ hτ).1) (rhoN ε) rfl))
    (cells i hi τ hτ).2) okF
  rw [← Fe] at bF
  change _ ≤ IPhi ε ∧ IPhi ε ≤ ((sumPhi _ _ E N).hi : ℝ) / D at bF
  -- final algebra
  set PL := ((sumP E N).lo : ℝ) / D
  set QL := ((sumQ E N).lo : ℝ) / D
  set QU := ((sumQ E N).hi : ℝ) / D
  set S3U := ((sumS3 E N).hi : ℝ) / D
  set S5L := ((sumS5 E N).lo : ℝ) / D
  set IU := ((sumPhi (ratio (sumP E N) (sumQ E N)).sq (E.mul (ratio (sumS3 E N) (sumQ E N)))
    E N).hi : ℝ) / D
  have hPL : 0 ≤ PL := div_nonneg (by exact_mod_cast hPlo) hDpos.le
  have hQL : 0 < QL := div_pos (by exact_mod_cast hQlo) hDpos
  have hS3L : 0 ≤ S3n ε := le_trans (div_nonneg (by exact_mod_cast h3lo) hDpos.le) b3.1
  have hS5L : 0 ≤ S5L := div_nonneg (by exact_mod_cast h5lo) hDpos.le
  have hIU : 0 ≤ IU := div_nonneg (by exact_mod_cast hFhi) hDpos.le
  have hQn : 0 < Qn ε := lt_of_lt_of_le hQL bQ.1
  have hfin' : QU * IU < 3 * (3 * PL * S5L - QU * S3U) := by
    have hcast : ((sumQ E N).hi : ℝ) * ((sumPhi (ratio (sumP E N) (sumQ E N)).sq
        (E.mul (ratio (sumS3 E N) (sumQ E N))) E N).hi : ℝ) <
        3 * (3 * ((sumP E N).lo : ℝ) * ((sumS5 E N).lo : ℝ) -
          ((sumQ E N).hi : ℝ) * ((sumS3 E N).hi : ℝ)) := by exact_mod_cast hfin
    have hd : 0 < D⁻¹ := inv_pos.2 hDpos
    have hcast' := mul_lt_mul_of_pos_right hcast (mul_pos hd hd)
    simp only [PL, QU, S3U, S5L, IU, div_eq_mul_inv]
    nlinarith [hcast']
  unfold WellDominant
  have l1 : Qn ε * IPhi ε ≤ QU * IU := by
    calc Qn ε * IPhi ε ≤ Qn ε * IU := mul_le_mul_of_nonneg_left bF.2 hQn.le
      _ ≤ QU * IU := mul_le_mul_of_nonneg_right bQ.2 hIU
  have l2 : PL * S5L ≤ Pn ε * S5n ε := mul_le_mul bP.1 b5.1 hS5L (le_trans hPL bP.1)
  have l3 : Qn ε * S3n ε ≤ QU * S3U :=
    mul_le_mul bQ.2 b3.2 hS3L (le_trans hQn.le bQ.2)
  linarith

/-! ## Covering `ε ∈ (0, 1/2]` -/

/-- A chain of accepted cells covering `[a, b]`. -/
inductive Covered : ℚ → ℚ → Prop where
  | single (N : ℕ) (a b : ℚ) : cellCheck N a b = true → Covered a b
  | step (N : ℕ) (a m b : ℚ) : cellCheck N a m = true → Covered m b → Covered a b

/-- A chain of accepted cells proves `WellDominant` on its whole range. -/
theorem Covered.sound {a b : ℚ} (h : Covered a b) :
    ∀ ε : ℝ, (a : ℝ) ≤ ε → ε ≤ b → 0 < ε → ε ≤ 1 / 2 → WellDominant ε := by
  induction h with
  | single N a b hc => exact fun ε h0 h1 hε hε' => cellCheck_sound hc h0 h1 hε hε'
  | step N a m b hc _ ih =>
    intro ε h0 h1 hε hε'
    rcases le_total ε m with hm | hm
    · exact cellCheck_sound hc h0 hm hε hε'
    · exact ih ε hm h1 hε hε'

set_option maxRecDepth 100000 in
/-- **The cover**: 18 accepted cells (`N = 32` `τ`-cells each) chain from `0` to `1/2`. Each
`fiv_cert` certifies one `cellCheck` evaluation (one kernel leaf per interval operation). -/
theorem wellDominant_cover : Covered 0 (1 / 2) :=
  .step 32 (0) (1 / 20) (1 / 2) (by fiv_cert) <|
  .step 32 (1 / 20) (9 / 100) (1 / 2) (by fiv_cert) <|
  .step 32 (9 / 100) (61 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (61 / 500) (77 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (77 / 500) (93 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (93 / 500) (109 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (109 / 500) (243 / 1000) (1 / 2) (by fiv_cert) <|
  .step 32 (243 / 1000) (67 / 250) (1 / 2) (by fiv_cert) <|
  .step 32 (67 / 250) (293 / 1000) (1 / 2) (by fiv_cert) <|
  .step 32 (293 / 1000) (159 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (159 / 500) (343 / 1000) (1 / 2) (by fiv_cert) <|
  .step 32 (343 / 1000) (46 / 125) (1 / 2) (by fiv_cert) <|
  .step 32 (46 / 125) (393 / 1000) (1 / 2) (by fiv_cert) <|
  .step 32 (393 / 1000) (209 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (209 / 500) (219 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (219 / 500) (229 / 500) (1 / 2) (by fiv_cert) <|
  .step 32 (229 / 500) (239 / 500) (1 / 2) (by fiv_cert) <|
  .single 32 (239 / 500) (1 / 2) (by fiv_cert)

/-- **Main numerical theorem**: the normalized dominant-well inequality holds for every
`ε ∈ (0, 1/2]`, i.e. on every flux surface of the reactor plasma. -/
theorem normalized_well_dominance (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) : WellDominant ε :=
  wellDominant_cover.sound ε (by simpa using hε.le) (by simpa using hε') hε hε'

set_option maxRecDepth 100000 in
/-- Rejected fixture: a single cell `[0, 1/2]` with only `N = 8` `τ`-cells is NOT accepted, so
the checker does not accept everything. -/
theorem cellCheck_rejects_wide : cellCheck 8 0 (1 / 2) = false := by fiv_cert

set_option maxRecDepth 100000 in
/-- Rejected fixture: the near-axis cell `[0, 1/10]` (twice the accepted width) fails at
`N = 32` — the interval widening in `ε` is real, and the cover had to be refined. -/
theorem cellCheck_rejects_axis_wide : cellCheck 32 0 (1 / 10) = false := by fiv_cert

end PlasmaLean.Design.SolovevMercierQuadrature
