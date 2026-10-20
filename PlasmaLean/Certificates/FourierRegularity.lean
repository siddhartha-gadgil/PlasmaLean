/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.WeightedEll1
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# From Fourier-coefficient equations to classical solutions

A radii-polynomial certificate in `ℓ¹(ℤ)` (`PlasmaLean.Certificates.WeightedEll1`) proves
that a *coefficient sequence* `u` solves an equation such as
`-(1+k²) uₖ + (u ⋆ u)ₖ - fₖ = 0`. This file supplies the regularity step that turns such a
sequence into a classical periodic solution of the ODE.

**Termwise differentiation.** For a real sequence `x : ℤ → ℝ` with
`∑ₖ (1 + k²) |xₖ| < ∞`, the cosine series `U(θ) = ∑ₖ xₖ cos(kθ)` is `C²`
(`contDiff_two_cosSum`), and may be differentiated termwise twice
(`hasDerivAt_cosSum`, `hasDerivAt_dCosSum`):

  `U'(θ) = -∑ₖ k xₖ sin(kθ)`,  `U''(θ) = -∑ₖ k² xₖ cos(kθ)`.

The proofs use Mathlib's `hasDerivAt_tsum` with the summable majorant `(1 + k²)|xₖ|`. The
function is `2π`-periodic (`cosSum_periodic`).

**Regularity from the equation.** If `-k² uₖ = gₖ` for all `k` with `u, g ∈ ℓ¹`, then
automatically `∑ (1 + k²)|uₖ| < ∞`, so `U = evalCos u` is `C²` with `U'' = evalCos g`
pointwise (`classical_of_coeff`). No extra decay hypothesis is needed: it is supplied by
the equation itself.

**Products.** For *even* sequences (`a₋ₖ = aₖ`, i.e. genuine cosine series), point
evaluation is multiplicative on convolutions: `evalCos (a ⋆ b) = evalCos a · evalCos b`
(`evalCos_conv`). The proof reindexes the absolutely summable double series
`∑_{j,m} aⱼ bₘ cos((j+m)θ)` and uses that the sine series of an even sequence vanishes
(`sinSum_even`). Even sequences are closed under convolution (`conv_even`).

Sanity: `cosSum_single` (a single mode is `cos(nθ)`) and `classical_of_coeff_zero`
(the zero sequence gives the zero solution).
-/
public section
noncomputable section

namespace PlasmaLean.Certificates

open scoped BigOperators

/-! ### The cosine series and its termwise derivatives -/

/-- The cosine series `θ ↦ ∑ₖ xₖ cos(kθ)` of a real sequence on `ℤ`. For `x ∈ ℓ¹` this is
`evalCos x` (`evalCos_eq_cosSum`). -/
@[expose] def cosSum (x : ℤ → ℝ) (θ : ℝ) : ℝ := ∑' k : ℤ, x k * Real.cos (k * θ)

/-- The termwise first derivative `θ ↦ -∑ₖ k xₖ sin(kθ)`. -/
@[expose] def dCosSum (x : ℤ → ℝ) (θ : ℝ) : ℝ := ∑' k : ℤ, -((k : ℝ) * x k * Real.sin (k * θ))

/-- The termwise second derivative `θ ↦ -∑ₖ k² xₖ cos(kθ)`. -/
@[expose] def ddCosSum (x : ℤ → ℝ) (θ : ℝ) : ℝ :=
  ∑' k : ℤ, -((k : ℝ) ^ 2 * x k * Real.cos (k * θ))

/-- The sine series `θ ↦ ∑ₖ xₖ sin(kθ)`. -/
@[expose] def sinSum (x : ℤ → ℝ) (θ : ℝ) : ℝ := ∑' k : ℤ, x k * Real.sin (k * θ)

/-- `evalCos` is the cosine series of the entries. -/
theorem evalCos_eq_cosSum (x : Ell1Z) (θ : ℝ) : evalCos x θ = cosSum x θ := rfl

/-- `|k| ≤ 1 + k²`. -/
theorem abs_int_le_one_add_sq (k : ℤ) : |(k : ℝ)| ≤ 1 + (k : ℝ) ^ 2 := by
  nlinarith [sq_abs (k : ℝ), abs_nonneg (k : ℝ), sq_nonneg (|(k : ℝ)| - 1)]

/-- The standing decay hypothesis `∑ₖ (1 + k²)|xₖ| < ∞`. -/
@[expose] def DecayTwo (x : ℤ → ℝ) : Prop := Summable fun k : ℤ => (1 + (k : ℝ) ^ 2) * |x k|

variable {x : ℤ → ℝ}

/-- Decay implies absolute summability. -/
theorem DecayTwo.summable_abs (hx : DecayTwo x) : Summable fun k : ℤ => |x k| :=
  hx.of_nonneg_of_le (fun _ => abs_nonneg _) fun k => by
    nlinarith [abs_nonneg (x k), sq_nonneg (k : ℝ)]

/-- Decay implies summability of `|k xₖ|`. -/
theorem DecayTwo.summable_k (hx : DecayTwo x) : Summable fun k : ℤ => |(k : ℝ) * x k| :=
  hx.of_nonneg_of_le (fun _ => abs_nonneg _) fun k => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_int_le_one_add_sq k) (abs_nonneg _)

/-- Decay implies summability of `k² |xₖ|`. -/
theorem DecayTwo.summable_k2 (hx : DecayTwo x) : Summable fun k : ℤ => (k : ℝ) ^ 2 * |x k| :=
  hx.of_nonneg_of_le (fun _ => by positivity) fun k => by
    nlinarith [abs_nonneg (x k)]

/-- Each term of the cosine series has the expected derivative. -/
theorem hasDerivAt_cos_term (x : ℤ → ℝ) (k : ℤ) (θ : ℝ) :
    HasDerivAt (fun t => x k * Real.cos (k * t)) (-((k : ℝ) * x k * Real.sin (k * θ))) θ := by
  have h := ((hasDerivAt_id' θ).const_mul (k : ℝ)).cos.const_mul (x k)
  convert h using 1
  ring

/-- Each term of the first-derivative series has the expected derivative. -/
theorem hasDerivAt_sin_term (x : ℤ → ℝ) (k : ℤ) (θ : ℝ) :
    HasDerivAt (fun t => -((k : ℝ) * x k * Real.sin (k * t)))
      (-((k : ℝ) ^ 2 * x k * Real.cos (k * θ))) θ := by
  have h := (((hasDerivAt_id' θ).const_mul (k : ℝ)).sin.const_mul ((k : ℝ) * x k)).neg
  convert h using 1
  ring

/-- The cosine series converges absolutely under the decay hypothesis. -/
theorem summable_cos_terms (hx : Summable fun k : ℤ => |x k|) (θ : ℝ) :
    Summable fun k : ℤ => x k * Real.cos (k * θ) :=
  Summable.of_norm_bounded hx fun k => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- **First termwise derivative.** -/
theorem hasDerivAt_cosSum (hx : DecayTwo x) (θ : ℝ) :
    HasDerivAt (cosSum x) (dCosSum x θ) θ := by
  unfold cosSum dCosSum
  refine hasDerivAt_tsum (u := fun k : ℤ => |(k : ℝ) * x k|) hx.summable_k
    (fun k t => hasDerivAt_cos_term x k t) (fun k t => ?_)
    (summable_cos_terms hx.summable_abs 0) θ
  rw [Real.norm_eq_abs, abs_neg, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- **Second termwise derivative.** -/
theorem hasDerivAt_dCosSum (hx : DecayTwo x) (θ : ℝ) :
    HasDerivAt (dCosSum x) (ddCosSum x θ) θ := by
  unfold dCosSum ddCosSum
  refine hasDerivAt_tsum (u := fun k : ℤ => (k : ℝ) ^ 2 * |x k|) hx.summable_k2
    (fun k t => hasDerivAt_sin_term x k t) (fun k t => ?_) (y₀ := 0) ?_ θ
  · rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  · simp

/-- The second termwise derivative is continuous. -/
theorem continuous_ddCosSum (hx : DecayTwo x) : Continuous (ddCosSum x) := by
  unfold ddCosSum
  refine continuous_tsum (u := fun k : ℤ => (k : ℝ) ^ 2 * |x k|) (fun k => by fun_prop)
    hx.summable_k2 fun k t => ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- `deriv` of the cosine series is the termwise derivative. -/
theorem deriv_cosSum (hx : DecayTwo x) : deriv (cosSum x) = dCosSum x :=
  funext fun θ => (hasDerivAt_cosSum hx θ).deriv

/-- The second derivative of the cosine series is the termwise second derivative. -/
theorem deriv_deriv_cosSum (hx : DecayTwo x) : deriv (deriv (cosSum x)) = ddCosSum x := by
  rw [deriv_cosSum hx]
  exact funext fun θ => (hasDerivAt_dCosSum hx θ).deriv

/-- **The cosine series is `C²`.** -/
theorem contDiff_two_cosSum (hx : DecayTwo x) : ContDiff ℝ 2 (cosSum x) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun θ => (hasDerivAt_cosSum hx θ).differentiableAt, by simp, ?_⟩
  rw [contDiff_one_iff_deriv, deriv_cosSum hx]
  refine ⟨fun θ => (hasDerivAt_dCosSum hx θ).differentiableAt, ?_⟩
  have : deriv (dCosSum x) = ddCosSum x :=
    funext fun θ => (hasDerivAt_dCosSum hx θ).deriv
  rw [this]
  exact continuous_ddCosSum hx

/-- The second termwise derivative is minus the cosine series of `k² xₖ`. -/
theorem ddCosSum_eq (x : ℤ → ℝ) (θ : ℝ) :
    ddCosSum x θ = cosSum (fun k => -((k : ℝ) ^ 2 * x k)) θ := by
  unfold ddCosSum cosSum
  congr 1; funext k; ring

/-- The cosine series is `2π`-periodic. -/
theorem cosSum_periodic (x : ℤ → ℝ) : Function.Periodic (cosSum x) (2 * Real.pi) := by
  intro θ
  unfold cosSum
  congr 1; funext k
  have : (k : ℝ) * (θ + 2 * Real.pi) = k * θ + k * (2 * Real.pi) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

/-- Sanity: a single mode `δₙ` gives `cos(nθ)`. -/
theorem cosSum_single (n : ℤ) (θ : ℝ) :
    cosSum (fun k => if k = n then 1 else 0) θ = Real.cos (n * θ) := by
  unfold cosSum
  rw [tsum_eq_single n (fun k hk => by simp [hk])]
  simp

/-! ### Regularity from the coefficient equation -/

/-- If `-k² uₖ = gₖ` with `u, g ∈ ℓ¹`, then `∑ (1 + k²)|uₖ| < ∞`. -/
theorem decayTwo_of_coeff (u g : Ell1Z) (h : ∀ k : ℤ, -((k : ℝ) ^ 2 * u k) = g k) :
    DecayTwo u := by
  have hs : Summable fun k : ℤ => |u k| + |g k| :=
    (summable_abs u).add (summable_abs g)
  refine hs.congr fun k => ?_
  rw [← h k, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (k : ℝ))]; ring

/-- **Classical solution from the coefficient equation.** If `u, g ∈ ℓ¹(ℤ)` satisfy
`-k² uₖ = gₖ` for every `k`, then `U = evalCos u` is a `C²`, `2π`-periodic function with
`U'' = evalCos g` pointwise; the derivatives are the termwise ones. -/
theorem classical_of_coeff (u g : Ell1Z) (h : ∀ k : ℤ, -((k : ℝ) ^ 2 * u k) = g k) :
    ContDiff ℝ 2 (evalCos u) ∧ Function.Periodic (evalCos u) (2 * Real.pi) ∧
      (∀ θ, HasDerivAt (evalCos u) (dCosSum u θ) θ) ∧
      (∀ θ, HasDerivAt (dCosSum u) (evalCos g θ) θ) ∧
      ∀ θ, deriv (deriv (evalCos u)) θ = evalCos g θ := by
  have hx := decayTwo_of_coeff u g h
  have hdd : ∀ θ, ddCosSum u θ = evalCos g θ := by
    intro θ
    rw [ddCosSum_eq, evalCos_eq_cosSum]
    unfold cosSum
    congr 1; funext k; beta_reduce; rw [h k]
  refine ⟨contDiff_two_cosSum hx, cosSum_periodic u, hasDerivAt_cosSum hx,
    fun θ => hdd θ ▸ hasDerivAt_dCosSum hx θ, fun θ => ?_⟩
  change deriv (deriv (cosSum u)) θ = _
  rw [deriv_deriv_cosSum hx, hdd]

/-- Sanity: the zero sequence gives the zero function, with zero second derivative. -/
theorem classical_of_coeff_zero (θ : ℝ) : deriv (deriv (evalCos 0)) θ = 0 := by
  have := (classical_of_coeff 0 0 (fun k => by simp)).2.2.2.2 θ
  rw [this]; simp [evalCos]

/-- Point evaluation is additive. -/
theorem evalCos_add (x y : Ell1Z) (θ : ℝ) :
    evalCos (x + y) θ = evalCos x θ + evalCos y θ := by
  unfold evalCos
  rw [← (summable_evalCos x θ).tsum_add (summable_evalCos y θ)]
  congr 1; funext k
  rw [lp.coeFn_add, Pi.add_apply]; ring

/-- Point evaluation commutes with scalars. -/
theorem evalCos_smul (c : ℝ) (x : Ell1Z) (θ : ℝ) : evalCos (c • x) θ = c * evalCos x θ := by
  unfold evalCos
  rw [← tsum_mul_left]
  congr 1; funext k
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring

/-! ### Products of even cosine series -/

/-- The sine series of an even sequence vanishes. -/
theorem sinSum_even (a : ℤ → ℝ) (ha : ∀ k, a (-k) = a k) (θ : ℝ) : sinSum a θ = 0 := by
  have h : sinSum a θ = -sinSum a θ := by
    unfold sinSum
    rw [← tsum_neg, ← (Equiv.neg ℤ).tsum_eq]
    congr 1; funext k
    simp only [Equiv.neg_apply, ha, Int.cast_neg, neg_mul, Real.sin_neg, mul_neg]
  linarith

/-- The convolution of two even sequences is even. -/
theorem conv_even (a b : Ell1Z) (ha : ∀ k, a (-k) = a k) (hb : ∀ k, b (-k) = b k) :
    ∀ k, conv 1 a b (-k) = conv 1 a b k := by
  have hra : refl a = a := by ext k; rw [refl_apply, ha]
  have hrb : refl b = b := by ext k; rw [refl_apply, hb]
  intro k
  have := congrArg (fun z : Ell1Z => z k) (conv_refl (ν := 1) a b)
  simp only [hra, hrb, refl_apply] at this
  exact this.symm

/-- The double series `∑_{j,m} aⱼ bₘ cos((j+m)θ)` is absolutely summable. -/
theorem summable_double_cos (a b : Ell1Z) (θ : ℝ) :
    Summable fun p : ℤ × ℤ => a p.1 * b p.2 * Real.cos ((p.1 + p.2 : ℤ) * θ) := by
  have hprod : Summable fun p : ℤ × ℤ => |a p.1| * |b p.2| :=
    summable_mul_of_summable_norm (R := ℝ) (f := fun j => |a j|) (g := fun j => |b j|)
      (by simpa only [Real.norm_eq_abs, abs_abs] using summable_abs a)
      (by simpa only [Real.norm_eq_abs, abs_abs] using summable_abs b)
  refine Summable.of_norm_bounded hprod fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- The reindexing `(k, j) ↦ (j, k - j)` of `ℤ × ℤ`. -/
@[expose] def convEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by simp
  right_inv q := by simp

/-- The cosine series of a convolution is the double series `∑_{j,m} aⱼ bₘ cos((j+m)θ)`. -/
theorem evalCos_conv_eq_double (a b : Ell1Z) (θ : ℝ) :
    evalCos (conv 1 a b) θ =
      ∑' p : ℤ × ℤ, a p.1 * b p.2 * Real.cos ((p.1 + p.2 : ℤ) * θ) := by
  have hgs := summable_double_cos a b θ
  set g : ℤ × ℤ → ℝ := fun p => a p.1 * b p.2 * Real.cos ((p.1 + p.2 : ℤ) * θ)
  have hgs' : Summable (g ∘ convEquiv) := (convEquiv.summable_iff).2 hgs
  have h1 : HasSum (g ∘ convEquiv) (∑' p, g p) := (convEquiv.hasSum_iff).2 hgs.hasSum
  have hfib : HasSum (fun k : ℤ => ∑' j : ℤ, (g ∘ convEquiv) (k, j)) (∑' p, g p) :=
    h1.prod_fiberwise fun k => (hgs'.prod_factor k).hasSum
  rw [← hfib.tsum_eq]
  unfold evalCos
  refine tsum_congr fun k => ?_
  rw [conv_one_apply, ← tsum_mul_right]
  refine tsum_congr fun j => ?_
  simp only [g, Function.comp_apply, convEquiv, Equiv.coe_fn_mk, add_sub_cancel]

/-- **Point evaluation is multiplicative on even sequences:** (only the first factor needs
to be even, since the cross term is `(∑ aⱼ sin jθ)(∑ bₘ sin mθ)`)
`∑ₖ (a ⋆ b)ₖ cos kθ = (∑ⱼ aⱼ cos jθ)(∑ₘ bₘ cos mθ)`. -/
theorem evalCos_conv (a b : Ell1Z) (ha : ∀ k, a (-k) = a k) (θ : ℝ) :
    evalCos (conv 1 a b) θ = evalCos a θ * evalCos b θ := by
  have hA := summable_abs a
  have hB := summable_abs b
  have hcs : ∀ p : ℤ × ℤ, a p.1 * b p.2 * Real.cos ((p.1 + p.2 : ℤ) * θ) =
      (a p.1 * Real.cos (p.1 * θ)) * (b p.2 * Real.cos (p.2 * θ)) -
      (a p.1 * Real.sin (p.1 * θ)) * (b p.2 * Real.sin (p.2 * θ)) := by
    intro p
    push_cast
    rw [add_mul, Real.cos_add]; ring
  have hsumA : Summable fun j : ℤ => ‖a j * Real.cos (j * θ)‖ :=
    hA.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hsumB : Summable fun j : ℤ => ‖b j * Real.cos (j * θ)‖ :=
    hB.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hsumA' : Summable fun j : ℤ => ‖a j * Real.sin (j * θ)‖ :=
    hA.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hsumB' : Summable fun j : ℤ => ‖b j * Real.sin (j * θ)‖ :=
    hB.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hcc := tsum_mul_tsum_of_summable_norm hsumA hsumB
  have hss := tsum_mul_tsum_of_summable_norm hsumA' hsumB'
  have hP1 : Summable fun p : ℤ × ℤ =>
      (a p.1 * Real.cos (p.1 * θ)) * (b p.2 * Real.cos (p.2 * θ)) :=
    summable_mul_of_summable_norm (R := ℝ)
      (f := fun j : ℤ => a j * Real.cos (j * θ)) (g := fun j : ℤ => b j * Real.cos (j * θ))
      hsumA hsumB
  have hP2 : Summable fun p : ℤ × ℤ =>
      (a p.1 * Real.sin (p.1 * θ)) * (b p.2 * Real.sin (p.2 * θ)) :=
    summable_mul_of_summable_norm (R := ℝ)
      (f := fun j : ℤ => a j * Real.sin (j * θ)) (g := fun j : ℤ => b j * Real.sin (j * θ))
      hsumA' hsumB'
  have hsa : (∑' j : ℤ, a j * Real.sin (j * θ)) = 0 := sinSum_even a ha θ
  rw [evalCos_conv_eq_double, tsum_congr hcs, hP1.tsum_sub hP2, ← hcc, ← hss, hsa,
    zero_mul, sub_zero]
  rfl

end PlasmaLean.Certificates
