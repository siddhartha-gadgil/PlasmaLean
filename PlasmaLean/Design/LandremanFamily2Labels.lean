/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Flux, volume and current labels of Landreman's family 2 (one-dimensional reductions)

Source: M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with
invariant surfaces*, arXiv:2609.26742 **v2** (28 Sep 2026), §3, eqs. (3.12)–(3.24)
(coordinates `(χ, ζ)` on the surface `ψ = k²/2`, Jacobian (3.18), `B·∇χ = √(1-Y²)` (3.21),
`B·∇ζ = T/(2G)` (3.23)).

On the flux surface `ψ = k²/2` of family 2 (parameters `ε`, `S`, `λ`) the flux-surface
derivatives of the toroidal flux `2π ψ_t`, the poloidal flux `2π ψ_p`, the enclosed volume `V`
and the Boozer poloidal current `I = μ₀ I_tor/(2π)` reduce to one-dimensional integrals
(derived by hand from the Jacobian (3.18), the toroidal section `ζ = 0` and the
`ζ ↦ π/2 - ζ` symmetry; cross-checked numerically against the two-dimensional surface
integrals by `scripts/landreman_mercier_oracle.py` and `scripts/landreman_family2_map.py`):

* `dψ_t/dψ = F₁/(4πλ)`, `F₁(k) = ∫_{-π}^{π} dt / (h(S - arcsin(k sin t / c)) c)`,
  `c = √(1 - k² + k² sin² t)`, `h(σ) = √(4σ² + ε²)` (the section `ζ = 0`, `χ = t + π/2`);
* `dψ_p/dψ = Z/(4πλ)`, `Z(k) = ∫_{-π}^{π} dt / √(cosh²(ε sin t/2) - k²)`;
* `dV/dψ = Z E/(2λ)`, `E(k) = ∫_{-π}^{π} dt / √(1 - k² sin² t)` (`= 4K(k)`);
* `dI_tor/dψ = F₁/2 + E/λ²` (from `μ₀ J = λ B + ∇B_z × ẑ`, `LandremanFamily2Surface`).

This module defines these integrands, proves their derivatives in `k` and differentiation
under the integral sign (`hasDerivAt_F1`, `hasDerivAt_Zint`, `hasDerivAt_Eint`), and defines
the labels as primitives in `k` (`ψ = k²/2`, `dψ = k dk`): `psiT`, `psiP`, `volK`, `curK`,
with their exact `k`-derivatives (`deriv_psiT`, ...). The rotational transform is
`ι = dψ_p/dψ_t = Z/F₁` (`iotaK_eq`).

Scope: the identification of `F₁`, `Z`, `E` with the flux, volume and current derivatives of
the actual field is the hand derivation quoted above (change of variables not formalized);
everything stated here about the defined functions is proved.
-/

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2Labels

open Real Set MeasureTheory intervalIntegral Filter Topology

/-! ## Integrands -/

/-- `h(σ) = √(4σ² + ε²)`. -/
@[expose] def hfun (ε σ : ℝ) : ℝ := √(4 * σ ^ 2 + ε ^ 2)

/-- `c(k, y) = √(1 - k² + k² y²)` (`y = sin t`). -/
@[expose] def cK (k y : ℝ) : ℝ := √(1 - k ^ 2 + k ^ 2 * y ^ 2)

/-- `σ(k, y) = S - arcsin(k y / c)` on the toroidal section `ζ = 0`. -/
@[expose] def sigF (S k y : ℝ) : ℝ := S - arcsin (k * y / cK k y)

/-- Integrand of `F₁`: `1/(h(σ) c)`. -/
@[expose] def fF1 (ε S k y : ℝ) : ℝ := (hfun ε (sigF S k y) * cK k y)⁻¹

/-- `∂_k` of the `F₁` integrand: `(4σ y/(h² √(1-k²)) + k(1-y²))/(h c³)`. -/
@[expose] def fF1k (ε S k y : ℝ) : ℝ :=
  (4 * sigF S k y * y / (hfun ε (sigF S k y) ^ 2 * √(1 - k ^ 2)) + k * (1 - y ^ 2)) /
    (hfun ε (sigF S k y) * cK k y ^ 3)

/-- `cosh²(ε y/2) - k²`. -/
@[expose] def tZ (ε k y : ℝ) : ℝ := cosh (ε * y / 2) ^ 2 - k ^ 2

/-- Integrand of `Z`: `1/√(cosh²(εy/2) - k²)`. -/
@[expose] def fZ (ε k y : ℝ) : ℝ := (√(tZ ε k y))⁻¹

/-- `∂_k` of the `Z` integrand: `k/(cosh² - k²)^{3/2}`. -/
@[expose] def fZk (ε k y : ℝ) : ℝ := k / √(tZ ε k y) ^ 3

/-- Integrand of `E`: `1/√(1 - k² y²)`. -/
@[expose] def fE (k y : ℝ) : ℝ := (√(1 - k ^ 2 * y ^ 2))⁻¹

/-- `∂_k` of the `E` integrand: `k y²/(1 - k²y²)^{3/2}`. -/
@[expose] def fEk (k y : ℝ) : ℝ := k * y ^ 2 / √(1 - k ^ 2 * y ^ 2) ^ 3

/-! ## Positivity of the radicands -/

section Pos
variable {k y : ℝ}

/-- `c² ≥ 1 - k² > 0`. -/
theorem cK_sq_pos (hk : k ^ 2 < 1) : 0 < 1 - k ^ 2 + k ^ 2 * y ^ 2 := by
  have : 0 ≤ k ^ 2 * y ^ 2 := by positivity
  linarith

/-- `c > 0`. -/
theorem cK_pos (hk : k ^ 2 < 1) : 0 < cK k y := Real.sqrt_pos.2 (cK_sq_pos hk)

/-- `c² = 1 - k² + k² y²`. -/
theorem cK_sq (hk : k ^ 2 < 1) : cK k y ^ 2 = 1 - k ^ 2 + k ^ 2 * y ^ 2 :=
  Real.sq_sqrt (cK_sq_pos hk).le

/-- `|k y / c| < 1`. -/
theorem arg_sq_lt (hk : k ^ 2 < 1) : (k * y / cK k y) ^ 2 < 1 := by
  have hc := cK_pos (y := y) hk
  rw [div_pow, div_lt_one (by positivity), cK_sq hk]
  nlinarith

/-- `-1 < k y / c`. -/
theorem arg_gt (hk : k ^ 2 < 1) : -1 < k * y / cK k y := by
  have := arg_sq_lt (y := y) hk
  nlinarith [sq_nonneg (k * y / cK k y + 1)]

/-- `k y / c < 1`. -/
theorem arg_lt (hk : k ^ 2 < 1) : k * y / cK k y < 1 := by
  have := arg_sq_lt (y := y) hk
  nlinarith [sq_nonneg (k * y / cK k y - 1)]

/-- `h > 0` for `ε ≠ 0`. -/
theorem hfun_pos {ε : ℝ} (hε : ε ≠ 0) (σ : ℝ) : 0 < hfun ε σ :=
  Real.sqrt_pos.2 (by positivity)

/-- `h² = 4σ² + ε²`. -/
theorem hfun_sq (ε σ : ℝ) : hfun ε σ ^ 2 = 4 * σ ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `cosh² - k² ≥ 1 - k² > 0`. -/
theorem tZ_pos {ε : ℝ} (hk : k ^ 2 < 1) : 0 < tZ ε k y := by
  unfold tZ
  have := Real.one_le_cosh (ε * y / 2)
  nlinarith

/-- `1 - k² y² > 0` for `|y| ≤ 1`. -/
theorem tE_pos (hk : k ^ 2 < 1) (hy : y ∈ Icc (-1 : ℝ) 1) : 0 < 1 - k ^ 2 * y ^ 2 := by
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  nlinarith [sq_nonneg k]

end Pos

/-! ## Derivatives of the integrands in `k` -/

section Deriv
variable {ε S k y : ℝ}

/-- `∂_k c = -k(1-y²)/c`. -/
theorem hasDerivAt_cK (hk : k ^ 2 < 1) :
    HasDerivAt (fun k => cK k y) (-(k * (1 - y ^ 2)) / cK k y) k := by
  have h1 : HasDerivAt (fun k : ℝ => 1 - k ^ 2 + k ^ 2 * y ^ 2) (-(2 * k) + 2 * k * y ^ 2) k := by
    have := ((hasDerivAt_pow 2 k).const_sub 1).add ((hasDerivAt_pow 2 k).mul_const (y ^ 2))
    convert this using 1; push_cast; ring
  have h2 : HasDerivAt (fun k => cK k y) ((-(2 * k) + 2 * k * y ^ 2) / (2 * cK k y)) k :=
    h1.sqrt (cK_sq_pos hk).ne'
  have hc := (cK_pos (y := y) hk).ne'
  refine h2.congr_deriv ?_
  field_simp
  ring

/-- `∂_k (k y/c) = y/c³`. -/
theorem hasDerivAt_arg (hk : k ^ 2 < 1) :
    HasDerivAt (fun k => k * y / cK k y) (y / cK k y ^ 3) k := by
  have hc := cK_pos (y := y) hk
  have h : HasDerivAt (fun k => k * y / cK k y)
      ((1 * y * cK k y - k * y * (-(k * (1 - y ^ 2)) / cK k y)) / cK k y ^ 2) k :=
    ((hasDerivAt_id k).mul_const y).div (hasDerivAt_cK (y := y) hk) hc.ne'
  refine h.congr_deriv ?_
  have hc2 := cK_sq (y := y) hk
  field_simp
  linear_combination y * hc2

/-- `1 - (k y/c)² = (1-k²)/c²`. -/
theorem one_sub_arg_sq (hk : k ^ 2 < 1) :
    1 - (k * y / cK k y) ^ 2 = (1 - k ^ 2) / cK k y ^ 2 := by
  have hc := (cK_pos (y := y) hk).ne'
  have hc2 := cK_sq (y := y) hk
  field_simp
  linear_combination hc2

/-- `√(1 - (k y/c)²) = √(1-k²)/c`. -/
theorem sqrt_one_sub_arg_sq (hk : k ^ 2 < 1) :
    √(1 - (k * y / cK k y) ^ 2) = √(1 - k ^ 2) / cK k y := by
  rw [one_sub_arg_sq hk, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (cK_pos hk).le]

/-- `∂_k σ = -y/(c² √(1-k²))`. -/
theorem hasDerivAt_sigF (hk : k ^ 2 < 1) :
    HasDerivAt (fun k => sigF S k y) (-(y / (cK k y ^ 2 * √(1 - k ^ 2)))) k := by
  have hc := cK_pos (y := y) hk
  have hs : 0 < √(1 - k ^ 2) := Real.sqrt_pos.2 (by linarith)
  have h := ((Real.hasDerivAt_arcsin (arg_gt (y := y) hk).ne' (arg_lt (y := y) hk).ne).comp k
    (hasDerivAt_arg (y := y) hk)).const_sub S
  refine h.congr_deriv ?_
  rw [sqrt_one_sub_arg_sq hk]
  field_simp

/-- `∂_k h(σ) = 4σ σ'/h`. -/
theorem hasDerivAt_hfun_sig (hε : ε ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt (fun k => hfun ε (sigF S k y))
      (4 * sigF S k y * (-(y / (cK k y ^ 2 * √(1 - k ^ 2)))) / hfun ε (sigF S k y)) k := by
  have hσ := hasDerivAt_sigF (S := S) (y := y) hk
  have h1 : HasDerivAt (fun k => 4 * sigF S k y ^ 2 + ε ^ 2)
      (4 * (2 * sigF S k y * (-(y / (cK k y ^ 2 * √(1 - k ^ 2)))))) k := by
    have := ((hσ.pow 2).const_mul 4).add_const (ε ^ 2)
    convert this using 1; push_cast; ring
  have h2 : HasDerivAt (fun k => hfun ε (sigF S k y))
      (4 * (2 * sigF S k y * (-(y / (cK k y ^ 2 * √(1 - k ^ 2))))) /
        (2 * hfun ε (sigF S k y))) k := h1.sqrt (by
          have := sq_nonneg (sigF S k y)
          have h2 : 0 < ε ^ 2 := lt_of_le_of_ne (sq_nonneg ε) (Ne.symm (pow_ne_zero 2 hε))
          linarith)
  have hh := (hfun_pos hε (sigF S k y)).ne'
  refine h2.congr_deriv ?_
  field_simp

/-- **Derivative of the `F₁` integrand.** -/
theorem hasDerivAt_fF1 (hε : ε ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt (fun k => fF1 ε S k y) (fF1k ε S k y) k := by
  have hc := cK_pos (y := y) hk
  have hh := hfun_pos hε (sigF S k y)
  have hs : 0 < √(1 - k ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hm : HasDerivAt (fun k => hfun ε (sigF S k y) * cK k y)
      (4 * sigF S k y * (-(y / (cK k y ^ 2 * √(1 - k ^ 2)))) / hfun ε (sigF S k y) * cK k y +
        hfun ε (sigF S k y) * (-(k * (1 - y ^ 2)) / cK k y)) k :=
    (hasDerivAt_hfun_sig (S := S) (y := y) hε hk).mul (hasDerivAt_cK (y := y) hk)
  have h := hm.inv (mul_pos hh hc).ne'
  refine h.congr_deriv ?_
  unfold fF1k
  field_simp
  ring

/-- **Derivative of the `Z` integrand.** -/
theorem hasDerivAt_fZ (hk : k ^ 2 < 1) :
    HasDerivAt (fun k => fZ ε k y) (fZk ε k y) k := by
  have ht := tZ_pos (ε := ε) (y := y) hk
  have h1 : HasDerivAt (fun k => tZ ε k y) (-(2 * k)) k := by
    have := (hasDerivAt_pow 2 k).const_sub (cosh (ε * y / 2) ^ 2)
    unfold tZ; convert this using 1; push_cast; ring
  have h2 := (h1.sqrt ht.ne').inv (Real.sqrt_pos.2 ht).ne'
  refine h2.congr_deriv ?_
  unfold fZk
  have hs := Real.sqrt_pos.2 ht
  field_simp

/-- **Derivative of the `E` integrand** (`|y| ≤ 1`). -/
theorem hasDerivAt_fE (hk : k ^ 2 < 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (fun k => fE k y) (fEk k y) k := by
  have ht := tE_pos hk hy
  have h1 : HasDerivAt (fun k : ℝ => 1 - k ^ 2 * y ^ 2) (-(2 * k * y ^ 2)) k := by
    have := ((hasDerivAt_pow 2 k).mul_const (y ^ 2)).const_sub 1
    convert this using 1; push_cast; ring
  have h2 := (h1.sqrt ht.ne').inv (Real.sqrt_pos.2 ht).ne'
  refine h2.congr_deriv ?_
  unfold fEk
  have hs := Real.sqrt_pos.2 ht
  field_simp

end Deriv

/-! ## Joint continuity of the integrands on `|k| < 1` -/

/-- The parameter region `{(k, y) | k² < 1}`. -/
@[expose] def Kreg : Set (ℝ × ℝ) := {p | p.1 ^ 2 < 1}

section Cont
variable {ε S : ℝ}

/-- Continuity of `c`. -/
theorem continuous_cK : Continuous (fun p : ℝ × ℝ => cK p.1 p.2) := by
  unfold cK; fun_prop

/-- Continuity of `σ` on `k² < 1`. -/
theorem continuousOn_sigF : ContinuousOn (fun p : ℝ × ℝ => sigF S p.1 p.2) Kreg := by
  have h : ContinuousOn (fun p : ℝ × ℝ => p.1 * p.2 / cK p.1 p.2) Kreg :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1 * p.2)).continuousOn.div
      continuous_cK.continuousOn (fun p hp => (cK_pos hp).ne')
  exact continuousOn_const.sub (Real.continuous_arcsin.comp_continuousOn h)

/-- Continuity of `h(σ)` on `k² < 1`. -/
theorem continuousOn_hfun_sig :
    ContinuousOn (fun p : ℝ × ℝ => hfun ε (sigF S p.1 p.2)) Kreg := by
  have h : ContinuousOn (fun p : ℝ × ℝ => 4 * sigF S p.1 p.2 ^ 2 + ε ^ 2) Kreg :=
    (continuousOn_const.mul (continuousOn_sigF.pow 2)).add continuousOn_const
  exact Real.continuous_sqrt.comp_continuousOn h

/-- Continuity of the `F₁` integrand. -/
theorem continuousOn_fF1 (hε : ε ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => fF1 ε S p.1 p.2) Kreg :=
  ((continuousOn_hfun_sig (ε := ε) (S := S)).mul continuous_cK.continuousOn).inv₀
    (fun _ hp => (mul_pos (hfun_pos hε _) (cK_pos hp)).ne')

/-- Continuity of `∂_k` of the `F₁` integrand. -/
theorem continuousOn_fF1k (hε : ε ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => fF1k ε S p.1 p.2) Kreg := by
  have hs : ContinuousOn (fun p : ℝ × ℝ => √(1 - p.1 ^ 2)) Kreg :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => √(1 - p.1 ^ 2))).continuousOn
  have hnum : ContinuousOn (fun p : ℝ × ℝ => 4 * sigF S p.1 p.2 * p.2 /
      (hfun ε (sigF S p.1 p.2) ^ 2 * √(1 - p.1 ^ 2)) + p.1 * (1 - p.2 ^ 2)) Kreg := by
    refine ContinuousOn.add ?_ (by fun_prop)
    refine ContinuousOn.div ((continuousOn_const.mul continuousOn_sigF).mul
      (by fun_prop)) ((continuousOn_hfun_sig.pow 2).mul hs) (fun p hp => ?_)
    have hp' : p.1 ^ 2 < 1 := hp
    have : 0 < √(1 - p.1 ^ 2) := Real.sqrt_pos.2 (by linarith)
    exact (mul_pos (pow_pos (hfun_pos hε _) 2) this).ne'
  exact hnum.div (continuousOn_hfun_sig.mul (continuous_cK.continuousOn.pow 3))
    (fun p hp => (mul_pos (hfun_pos hε _) (pow_pos (cK_pos hp) 3)).ne')

/-- Continuity of the `Z` integrand. -/
theorem continuousOn_fZ : ContinuousOn (fun p : ℝ × ℝ => fZ ε p.1 p.2) Kreg := by
  have h : Continuous (fun p : ℝ × ℝ => √(tZ ε p.1 p.2)) := by unfold tZ; fun_prop
  exact h.continuousOn.inv₀ (fun p hp => (Real.sqrt_pos.2 (tZ_pos hp)).ne')

/-- Continuity of `∂_k` of the `Z` integrand. -/
theorem continuousOn_fZk : ContinuousOn (fun p : ℝ × ℝ => fZk ε p.1 p.2) Kreg := by
  have h : Continuous (fun p : ℝ × ℝ => √(tZ ε p.1 p.2)) := by unfold tZ; fun_prop
  exact continuous_fst.continuousOn.div (h.continuousOn.pow 3)
    (fun p hp => (pow_pos (Real.sqrt_pos.2 (tZ_pos hp)) 3).ne')

/-- The region `{(k, y) | k² < 1, |y| ≤ 1}`. -/
@[expose] def Ereg : Set (ℝ × ℝ) := {p | p.1 ^ 2 < 1 ∧ p.2 ∈ Icc (-1 : ℝ) 1}

/-- Continuity of the `E` integrand. -/
theorem continuousOn_fE : ContinuousOn (fun p : ℝ × ℝ => fE p.1 p.2) Ereg := by
  have h : Continuous (fun p : ℝ × ℝ => √(1 - p.1 ^ 2 * p.2 ^ 2)) := by fun_prop
  exact h.continuousOn.inv₀ (fun p hp => (Real.sqrt_pos.2 (tE_pos hp.1 hp.2)).ne')

/-- Continuity of `∂_k` of the `E` integrand. -/
theorem continuousOn_fEk : ContinuousOn (fun p : ℝ × ℝ => fEk p.1 p.2) Ereg := by
  have h : Continuous (fun p : ℝ × ℝ => √(1 - p.1 ^ 2 * p.2 ^ 2)) := by fun_prop
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1 * p.2 ^ 2)).continuousOn.div
    (h.continuousOn.pow 3) (fun p hp => (pow_pos (Real.sqrt_pos.2 (tE_pos hp.1 hp.2)) 3).ne')

end Cont

/-! ## Differentiation under the integral sign -/

/-- **Differentiation under the integral sign** for `k ↦ ∫_{-π}^{π} f(k, sin t) dt`, with `f`
and `∂_k f = f'` jointly continuous on `[a, b] × [-1, 1]` and `HasDerivAt` in `k` on `(a, b)`. -/
theorem hasDerivAt_integral_sin {f f' : ℝ → ℝ → ℝ} {a b k₀ : ℝ} (ha : a < k₀) (hb : k₀ < b)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc a b ×ˢ Icc (-1 : ℝ) 1))
    (hf' : ContinuousOn (fun p : ℝ × ℝ => f' p.1 p.2) (Icc a b ×ˢ Icc (-1 : ℝ) 1))
    (hd : ∀ k ∈ Ioo a b, ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun k => f k y) (f' k y) k) :
    HasDerivAt (fun k => ∫ t in (-π)..π, f k (sin t)) (∫ t in (-π)..π, f' k₀ (sin t)) k₀ := by
  have hsin : ∀ t, sin t ∈ Icc (-1 : ℝ) 1 := fun t => ⟨neg_one_le_sin t, sin_le_one t⟩
  have hcomp : ∀ {g : ℝ → ℝ → ℝ},
      ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc a b ×ˢ Icc (-1 : ℝ) 1) →
      ∀ k ∈ Icc a b, Continuous (fun t => g k (sin t)) := by
    intro g hg k hk
    exact hg.comp_continuous (by fun_prop : Continuous (fun t => (k, sin t)))
      (fun t => ⟨hk, hsin t⟩)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf'
  have hs : Ioo a b ∈ 𝓝 k₀ := Ioo_mem_nhds ha hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun k t => f k (sin t)) (F' := fun k t => f' k (sin t))
    (bound := fun _ => M) hs ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [hs] with k hk using
      (hcomp hf k (Ioo_subset_Icc_self hk)).aestronglyMeasurable
  · exact (hcomp hf k₀ ⟨ha.le, hb.le⟩).intervalIntegrable (μ := volume) _ _
  · exact (hcomp hf' k₀ ⟨ha.le, hb.le⟩).aestronglyMeasurable
  · exact ae_of_all _ (fun t _ k hk => hM (k, sin t) ⟨Ioo_subset_Icc_self hk, hsin t⟩)
  · exact ae_of_all _ (fun t _ k hk => hd k hk (sin t) (hsin t))

/-! ## The one-dimensional integrals and their `k`-derivatives -/

/-- `F₁(k) = ∫_{-π}^{π} dt/(h(S - arcsin(k sin t/c)) c)`. -/
@[expose] def F1 (ε S k : ℝ) : ℝ := ∫ t in (-π)..π, fF1 ε S k (sin t)

/-- `F₁'(k) = ∫_{-π}^{π} ∂_k(…) dt`. -/
@[expose] def F1d (ε S k : ℝ) : ℝ := ∫ t in (-π)..π, fF1k ε S k (sin t)

/-- `Z(k) = ∫_{-π}^{π} dt/√(cosh²(ε sin t/2) - k²)`. -/
@[expose] def Zint (ε k : ℝ) : ℝ := ∫ t in (-π)..π, fZ ε k (sin t)

/-- `Z'(k)`. -/
@[expose] def Zd (ε k : ℝ) : ℝ := ∫ t in (-π)..π, fZk ε k (sin t)

/-- `E(k) = ∫_{-π}^{π} dt/√(1 - k² sin² t)`. -/
@[expose] def Eint (k : ℝ) : ℝ := ∫ t in (-π)..π, fE k (sin t)

/-- `E'(k)`. -/
@[expose] def Ed (k : ℝ) : ℝ := ∫ t in (-π)..π, fEk k (sin t)

section OneD
variable {ε S k : ℝ}

/-- A closed neighbourhood `[a, b] × [-1, 1]` of `k ∈ (-1, 1)` inside the region `k² < 1`. -/
theorem box_sub (hk : k ∈ Ioo (-1 : ℝ) 1) :
    Icc ((k - 1) / 2) ((k + 1) / 2) ×ˢ Icc (-1 : ℝ) 1 ⊆ Ereg := by
  intro p hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  refine ⟨?_, h3⟩
  have : -1 < p.1 := by linarith [hk.1]
  have : p.1 < 1 := by linarith [hk.2]
  nlinarith

/-- `Ereg ⊆ Kreg`. -/
theorem Ereg_sub : Ereg ⊆ Kreg := fun _ hp => hp.1

/-- `|k| < 1 → k² < 1`. -/
theorem sq_lt_one_of_mem (hk : k ∈ Ioo (-1 : ℝ) 1) : k ^ 2 < 1 := by
  nlinarith [hk.1, hk.2]

/-- **`dF₁/dk = F₁'`** on `|k| < 1`. -/
theorem hasDerivAt_F1 (hε : ε ≠ 0) (hk : k ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (F1 ε S) (F1d ε S k) k := by
  have hb := box_sub hk
  exact hasDerivAt_integral_sin (by linarith [hk.1]) (by linarith [hk.2])
    ((continuousOn_fF1 hε).mono (hb.trans Ereg_sub))
    ((continuousOn_fF1k hε).mono (hb.trans Ereg_sub))
    (fun k' hk' y _ => hasDerivAt_fF1 hε (by
      have := hb (show (k', (0 : ℝ)) ∈ _ from
        ⟨Ioo_subset_Icc_self hk', by norm_num, by norm_num⟩)
      exact this.1))

/-- **`dZ/dk = Z'`** on `|k| < 1`. -/
theorem hasDerivAt_Zint (hk : k ∈ Ioo (-1 : ℝ) 1) : HasDerivAt (Zint ε) (Zd ε k) k := by
  have hb := box_sub hk
  exact hasDerivAt_integral_sin (by linarith [hk.1]) (by linarith [hk.2])
    (continuousOn_fZ.mono (hb.trans Ereg_sub)) (continuousOn_fZk.mono (hb.trans Ereg_sub))
    (fun k' hk' y _ => hasDerivAt_fZ (by
      have := hb (show (k', (0 : ℝ)) ∈ _ from
        ⟨Ioo_subset_Icc_self hk', by norm_num, by norm_num⟩)
      exact this.1))

/-- **`dE/dk = E'`** on `|k| < 1`. -/
theorem hasDerivAt_Eint (hk : k ∈ Ioo (-1 : ℝ) 1) : HasDerivAt Eint (Ed k) k := by
  have hb := box_sub hk
  exact hasDerivAt_integral_sin (by linarith [hk.1]) (by linarith [hk.2])
    (continuousOn_fE.mono hb) (continuousOn_fEk.mono hb)
    (fun k' hk' y hy => hasDerivAt_fE (by
      have := hb (show (k', y) ∈ _ from ⟨Ioo_subset_Icc_self hk', hy⟩)
      exact this.1) hy)

/-- `F₁` is continuous on `(-1, 1)`. -/
theorem continuousOn_F1 (hε : ε ≠ 0) : ContinuousOn (F1 ε S) (Ioo (-1 : ℝ) 1) :=
  fun _ hk => (hasDerivAt_F1 hε hk).continuousAt.continuousWithinAt

/-- `Z` is continuous on `(-1, 1)`. -/
theorem continuousOn_Zint : ContinuousOn (Zint ε) (Ioo (-1 : ℝ) 1) :=
  fun _ hk => (hasDerivAt_Zint hk).continuousAt.continuousWithinAt

/-- `E` is continuous on `(-1, 1)`. -/
theorem continuousOn_Eint : ContinuousOn Eint (Ioo (-1 : ℝ) 1) :=
  fun _ hk => (hasDerivAt_Eint hk).continuousAt.continuousWithinAt

/-- Positivity of an integral over `[-π, π]` of a positive continuous function of `sin t`. -/
theorem integral_sin_pos {g : ℝ → ℝ} (hg : Continuous (fun t => g (sin t)))
    (hpos : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < g y) : 0 < ∫ t in (-π)..π, g (sin t) :=
  intervalIntegral_pos_of_pos_on (hg.intervalIntegrable _ _)
    (fun t _ => hpos _ ⟨neg_one_le_sin t, sin_le_one t⟩) (by linarith [pi_pos])

/-- `F₁ > 0`. -/
theorem F1_pos (hε : ε ≠ 0) (hk : k ∈ Ioo (-1 : ℝ) 1) : 0 < F1 ε S k := by
  have hk2 := sq_lt_one_of_mem hk
  have hm : ∀ t : ℝ, (k, sin t) ∈ Kreg := fun t => by rw [Kreg, Set.mem_ofPred_eq]; exact hk2
  have h0 : Continuous (fun t : ℝ => (k, sin t)) := by fun_prop
  have h1 := (continuousOn_fF1 (S := S) hε).comp_continuous h0 hm
  have hc : Continuous (fun t => fF1 ε S k (sin t)) := h1
  have hp : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < fF1 ε S k y := fun y _ =>
    inv_pos.2 (mul_pos (hfun_pos hε _) (cK_pos hk2))
  exact integral_sin_pos hc hp

/-- `Z > 0`. -/
theorem Zint_pos (hk : k ∈ Ioo (-1 : ℝ) 1) : 0 < Zint ε k := by
  have hk2 := sq_lt_one_of_mem hk
  have hm : ∀ t : ℝ, (k, sin t) ∈ Kreg := fun t => by rw [Kreg, Set.mem_ofPred_eq]; exact hk2
  have h0 : Continuous (fun t : ℝ => (k, sin t)) := by fun_prop
  have h1 := (continuousOn_fZ (ε := ε)).comp_continuous h0 hm
  have hc : Continuous (fun t => fZ ε k (sin t)) := h1
  have hp : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < fZ ε k y := fun y _ =>
    inv_pos.2 (Real.sqrt_pos.2 (tZ_pos hk2))
  exact integral_sin_pos hc hp

/-- `E > 0`. -/
theorem Eint_pos (hk : k ∈ Ioo (-1 : ℝ) 1) : 0 < Eint k := by
  have hk2 := sq_lt_one_of_mem hk
  unfold Eint
  exact integral_sin_pos (g := fE k)
    (continuousOn_fE.comp_continuous (by fun_prop : Continuous (fun t => (k, sin t)))
      (fun t => ⟨hk2, neg_one_le_sin t, sin_le_one t⟩))
    (fun y hy => inv_pos.2 (Real.sqrt_pos.2 (tE_pos hk2 hy)))

end OneD

/-! ## Labels as functions of `k` (`ψ = k²/2`) -/

/-- Toroidal-flux label `ψ_t(k) = Φ_t/(2π) = ∫₀^k κ F₁(κ)/(4πλ) dκ`
(`dψ_t/dψ = F₁/(4πλ)`, `dψ = κ dκ`). -/
@[expose] def psiT (lam ε S k : ℝ) : ℝ := ∫ κ in (0 : ℝ)..k, κ * F1 ε S κ / (4 * π * lam)

/-- Poloidal-flux label `ψ_p(k) = ∫₀^k κ Z(κ)/(4πλ) dκ`. -/
@[expose] def psiP (lam ε k : ℝ) : ℝ := ∫ κ in (0 : ℝ)..k, κ * Zint ε κ / (4 * π * lam)

/-- Enclosed volume `V(k) = ∫₀^k κ Z(κ) E(κ)/(2λ) dκ`. -/
@[expose] def volK (lam ε k : ℝ) : ℝ := ∫ κ in (0 : ℝ)..k, κ * (Zint ε κ * Eint κ) / (2 * lam)

/-- Boozer poloidal current `I(k) = μ₀ I_tor/(2π) = (1/2π) ∫₀^k κ (F₁/2 + E/λ²) dκ`. -/
@[expose] def curK (lam ε S k : ℝ) : ℝ :=
  ∫ κ in (0 : ℝ)..k, κ * (F1 ε S κ / 2 + Eint κ / lam ^ 2) / (2 * π)

/-- Rotational transform `ι = dψ_p/dψ_t` as a function of `k`. -/
@[expose] def iotaK (lam ε S k : ℝ) : ℝ := deriv (psiP lam ε) k / deriv (psiT lam ε S) k

section LabelDerivs
variable {lam ε S k : ℝ}

/-- FTC for primitives of functions continuous on `(-1, 1)`. -/
theorem hasDerivAt_primitive {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-1 : ℝ) 1))
    (hk : k ∈ Ioo (-1 : ℝ) 1) : HasDerivAt (fun u => ∫ σ in (0 : ℝ)..u, f σ) (f k) k := by
  have hsub : uIcc 0 k ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    rcases le_total 0 k with h | h
    · rw [uIcc_of_le h] at hx; exact ⟨by linarith [hx.1], by linarith [hx.2, hk.2]⟩
    · rw [uIcc_of_ge h] at hx; exact ⟨by linarith [hx.1, hk.1], by linarith [hx.2]⟩
  exact intervalIntegral.integral_hasDerivAt_right ((hf.mono hsub).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter isOpen_Ioo k hk) (hf.continuousAt (Ioo_mem_nhds hk.1 hk.2))

/-- `dψ_t/dk = k F₁/(4πλ)`. -/
theorem hasDerivAt_psiT (hε : ε ≠ 0) (hk : k ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (psiT lam ε S) (k * F1 ε S k / (4 * π * lam)) k :=
  hasDerivAt_primitive ((continuousOn_id.mul (continuousOn_F1 hε)).div_const _) hk

/-- `dψ_p/dk = k Z/(4πλ)`. -/
theorem hasDerivAt_psiP (hk : k ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (psiP lam ε) (k * Zint ε k / (4 * π * lam)) k :=
  hasDerivAt_primitive ((continuousOn_id.mul continuousOn_Zint).div_const _) hk

/-- `dV/dk = k Z E/(2λ)`. -/
theorem hasDerivAt_volK (hk : k ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (volK lam ε) (k * (Zint ε k * Eint k) / (2 * lam)) k :=
  hasDerivAt_primitive ((continuousOn_id.mul (continuousOn_Zint.mul continuousOn_Eint)).div_const
    _) hk

/-- `dI/dk = k (F₁/2 + E/λ²)/(2π)`. -/
theorem hasDerivAt_curK (hε : ε ≠ 0) (hk : k ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (curK lam ε S) (k * (F1 ε S k / 2 + Eint k / lam ^ 2) / (2 * π)) k :=
  hasDerivAt_primitive ((continuousOn_id.mul (((continuousOn_F1 hε).div_const _).add
    (continuousOn_Eint.div_const _))).div_const _) hk

/-- `ι = Z/F₁` on `0 < k < 1`. -/
theorem iotaK_eq (hε : ε ≠ 0) (hlam : lam ≠ 0) (hk : k ∈ Ioo (0 : ℝ) 1) :
    iotaK lam ε S k = Zint ε k / F1 ε S k := by
  have hk' : k ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hk.1], hk.2⟩
  unfold iotaK
  rw [(hasDerivAt_psiP hk').deriv, (hasDerivAt_psiT hε hk').deriv]
  have := F1_pos (S := S) hε hk'
  have := hk.1.ne'
  have := pi_pos.ne'
  field_simp

/-- `ι'(k) = (Z' F₁ - Z F₁')/F₁²` on `0 < k < 1`. -/
theorem deriv_iotaK (hε : ε ≠ 0) (hlam : lam ≠ 0) (hk : k ∈ Ioo (0 : ℝ) 1) :
    deriv (iotaK lam ε S) k =
      (Zd ε k * F1 ε S k - Zint ε k * F1d ε S k) / F1 ε S k ^ 2 := by
  have hk' : k ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hk.1], hk.2⟩
  have heq : iotaK lam ε S =ᶠ[𝓝 k] fun k => Zint ε k / F1 ε S k :=
    Filter.eventually_of_mem (Ioo_mem_nhds hk.1 hk.2) (fun x hx => iotaK_eq hε hlam hx)
  rw [heq.deriv_eq]
  exact ((hasDerivAt_Zint hk').div (hasDerivAt_F1 hε hk') (F1_pos hε hk').ne').deriv

/-- The specific volume in the toroidal-flux label, `V'(ψ_t) = (dV/dk)/(dψ_t/dk) = 2π Z E/F₁`
on `0 < k < 1`. -/
theorem volRatio_eq (hε : ε ≠ 0) (hlam : lam ≠ 0) (hk : k ∈ Ioo (0 : ℝ) 1) :
    deriv (volK lam ε) k / deriv (psiT lam ε S) k =
      2 * π * (Zint ε k * Eint k) / F1 ε S k := by
  have hk' : k ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hk.1], hk.2⟩
  rw [(hasDerivAt_volK hk').deriv, (hasDerivAt_psiT hε hk').deriv]
  have := F1_pos (S := S) hε hk'
  have := hk.1.ne'
  have := pi_pos.ne'
  field_simp
  ring

/-- `d/dk (2π Z E/F₁) = 2π (Z' E F₁ + Z E' F₁ - Z E F₁')/F₁²` on `0 < k < 1`. -/
theorem deriv_volRatio (hε : ε ≠ 0) (hlam : lam ≠ 0) (hk : k ∈ Ioo (0 : ℝ) 1) :
    deriv (fun k => deriv (volK lam ε) k / deriv (psiT lam ε S) k) k =
      2 * π * (Zd ε k * Eint k * F1 ε S k + Zint ε k * Ed k * F1 ε S k -
        Zint ε k * Eint k * F1d ε S k) / F1 ε S k ^ 2 := by
  have hk' : k ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hk.1], hk.2⟩
  have heq : (fun k => deriv (volK lam ε) k / deriv (psiT lam ε S) k) =ᶠ[𝓝 k]
      fun k => 2 * π * (Zint ε k * Eint k) / F1 ε S k :=
    Filter.eventually_of_mem (Ioo_mem_nhds hk.1 hk.2) (fun x hx => volRatio_eq hε hlam hx)
  rw [heq.deriv_eq]
  have hZE : HasDerivAt (fun k => Zint ε k * Eint k) (Zd ε k * Eint k + Zint ε k * Ed k) k :=
    (hasDerivAt_Zint hk').mul (hasDerivAt_Eint hk')
  have h : HasDerivAt (fun k => 2 * π * (Zint ε k * Eint k) / F1 ε S k)
      ((2 * π * (Zd ε k * Eint k + Zint ε k * Ed k) * F1 ε S k -
        2 * π * (Zint ε k * Eint k) * F1d ε S k) / F1 ε S k ^ 2) k :=
    (hZE.const_mul (2 * π)).div (hasDerivAt_F1 hε hk') (F1_pos hε hk').ne'
  rw [h.deriv]
  ring

end LabelDerivs

end PlasmaLean.Design.LandremanFamily2Labels
