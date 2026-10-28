/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Contraction
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The radii polynomial theorem (Newton-like form)

Let `E` be a Banach space, `F : E → E`, `A` an injective approximate inverse, and
`T(u) = u - A F(u)`. With bounds

* `Y₀ ≥ ‖A F(ū)‖` (residual),
* `Z(r) = Z₀ + Z₂ r ≥` a Lipschitz constant of `T` on the closed ball `B̄(ū, r)`, e.g.
  `Z(r) ≥ sup_{u ∈ B̄(ū,r)} ‖I - A DF(u)‖`,

the *radii polynomial* is `p(r) = Z(r) r - r + Y₀ = Z₂ r² + (Z₀ - 1) r + Y₀`. If
`p(r₀) < 0` for some `r₀ > 0`, then `F` has exactly one zero in `B̄(ū, r₀)`.

Three entry points are provided.

* `radii_polynomial_fixedPoint`: Lipschitz form, for any self-map `T` of a complete metric
  normed group. This is what concrete sequence-space certificates use, because the
  Lipschitz estimate can be obtained algebraically (e.g. from a difference of squares)
  without computing Fréchet derivatives.
* `radii_polynomial_zero`: Newton form `T = id - A ∘ F`; injectivity of `A` turns the fixed
  point into a zero (`fixedPoint_equation` from `Contraction`).
* `radii_polynomial_fderiv`: derivative form with the classical split
  `Z(r) = Z₀ + Z₁ + Z₂ r`, where `‖I - A A†‖ ≤ Z₀`, `‖A (DF(ū) - A†)‖ ≤ Z₁` and
  `‖A (DF(u) - DF(ū))‖ ≤ Z₂ ‖u - ū‖` on the ball (van den Berg–Lessard).

All reduce to `local_fixedPoint` and `radii_conditions` from
`LeanTheory.Certificates.Contraction`; nothing about the Banach fixed-point theorem is
re-proved here.

Sanity: `radii_polynomial_rejects_small` (a radius below the residual is always rejected),
and `radii_polynomial_rejects_identity`: for the degenerate approximate inverse `A = 0`
(`T = id`, compare `zero_inverse_counterexample`) **no** Lipschitz bound can make the
radii polynomial negative, so the test is not vacuously passed by the degenerate choice.
-/
public section

namespace LeanTheory.Certificates

open Metric

variable {E : Type*} [NormedAddCommGroup E]

/-- The radii polynomial `p(r) = Z₂ r² + (Z₀ - 1) r + Y₀`. -/
@[expose] def radiiPoly (Y₀ Z₀ Z₂ r : ℝ) : ℝ := Z₂ * r ^ 2 + (Z₀ - 1) * r + Y₀

/-- `p(r) = Z(r) r - r + Y₀` with `Z(r) = Z₀ + Z₂ r`. -/
theorem radiiPoly_eq (Y₀ Z₀ Z₂ r : ℝ) :
    radiiPoly Y₀ Z₀ Z₂ r = (Z₀ + Z₂ * r) * r - r + Y₀ := by
  unfold radiiPoly; ring

/-- **Radii polynomial theorem, Lipschitz form.** A residual bound `Y₀` at the centre and
a Lipschitz bound `Z₀ + Z₂ r` for `T` on the whole closed ball of radius `r`, with
`p(r) < 0`, give a unique fixed point of `T` in that ball. -/
theorem radii_polynomial_fixedPoint [CompleteSpace E] (T : E → E) (ubar : E)
    {Y₀ Z₀ Z₂ r : ℝ} (hr : 0 < r) (hZ₀ : 0 ≤ Z₀) (hZ₂ : 0 ≤ Z₂)
    (hY : ‖T ubar - ubar‖ ≤ Y₀)
    (hlip : ∀ u ∈ closedBall ubar r, ∀ v ∈ closedBall ubar r,
      ‖T u - T v‖ ≤ (Z₀ + Z₂ * r) * ‖u - v‖)
    (hp : radiiPoly Y₀ Z₀ Z₂ r < 0) :
    ∃ u ∈ closedBall ubar r, T u = u ∧ ∀ v ∈ closedBall ubar r, T v = v → v = u := by
  have hY0 : 0 ≤ Y₀ := (norm_nonneg _).trans hY
  have hp' : Y₀ + (Z₀ + Z₂ * r - 1) * r + 0 * r ^ 2 < 0 := by
    unfold radiiPoly at hp; nlinarith
  obtain ⟨hK, hbudget⟩ := radii_conditions (Z₂ := 0) hY0 hr hp'
  have hZ : 0 ≤ Z₀ + Z₂ * r := by positivity
  set K : NNReal := ⟨Z₀ + Z₂ * r, hZ⟩
  have hKc : (K : ℝ) = Z₀ + Z₂ * r := rfl
  refine local_fixedPoint T ubar (Y := Y₀) (K := K) hr.le ?_ ?_ ?_ ?_
  · change (K : ℝ) < 1; rw [hKc]; linarith
  · rw [dist_eq_norm]; exact hY
  · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    rw [dist_eq_norm, dist_eq_norm, hKc]
    exact hlip u hu v hv
  · rw [hKc]; linarith

/-- **Radii polynomial theorem, Newton form.** For `T(u) = u - A F(u)` with `A` injective,
the certificate yields a unique zero of `F` in the closed ball. -/
theorem radii_polynomial_zero [CompleteSpace E] (F : E → E) (A : E →+ E)
    (hA : Function.Injective A) (ubar : E) {Y₀ Z₀ Z₂ r : ℝ} (hr : 0 < r)
    (hZ₀ : 0 ≤ Z₀) (hZ₂ : 0 ≤ Z₂) (hY : ‖A (F ubar)‖ ≤ Y₀)
    (hlip : ∀ u ∈ closedBall ubar r, ∀ v ∈ closedBall ubar r,
      ‖(u - A (F u)) - (v - A (F v))‖ ≤ (Z₀ + Z₂ * r) * ‖u - v‖)
    (hp : radiiPoly Y₀ Z₀ Z₂ r < 0) :
    ∃ u ∈ closedBall ubar r, F u = 0 ∧ ∀ v ∈ closedBall ubar r, F v = 0 → v = u := by
  have hY' : ‖(ubar - A (F ubar)) - ubar‖ ≤ Y₀ := by
    rw [sub_sub_cancel_left, norm_neg]; exact hY
  obtain ⟨u, hu, hfix, huniq⟩ :=
    radii_polynomial_fixedPoint (fun u => u - A (F u)) ubar hr hZ₀ hZ₂ hY' hlip hp
  refine ⟨u, hu, fixedPoint_equation A F hA u hfix, fun v hv hFv => huniq v hv ?_⟩
  simp [hFv]

/-- The classical bound `‖I - A DF(u)‖ ≤ Z₀ + Z₁ + Z₂ ‖u - ū‖` from the three
van den Berg–Lessard bounds with an approximate derivative `A†`. -/
theorem norm_id_sub_comp_le [NormedSpace ℝ E] (A Adag D Dbar : E →L[ℝ] E)
    {Z₀ Z₁ Z₂ ρ : ℝ}
    (h₀ : ‖ContinuousLinearMap.id ℝ E - A.comp Adag‖ ≤ Z₀)
    (h₁ : ‖A.comp (Dbar - Adag)‖ ≤ Z₁) (h₂ : ‖A.comp (D - Dbar)‖ ≤ Z₂ * ρ) :
    ‖ContinuousLinearMap.id ℝ E - A.comp D‖ ≤ Z₀ + Z₁ + Z₂ * ρ := by
  have : ContinuousLinearMap.id ℝ E - A.comp D =
      (ContinuousLinearMap.id ℝ E - A.comp Adag) - A.comp (Dbar - Adag) -
        A.comp (D - Dbar) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub]; abel
  rw [this]
  calc _ ≤ ‖ContinuousLinearMap.id ℝ E - A.comp Adag - A.comp (Dbar - Adag)‖ +
        ‖A.comp (D - Dbar)‖ := norm_sub_le _ _
    _ ≤ ‖ContinuousLinearMap.id ℝ E - A.comp Adag‖ + ‖A.comp (Dbar - Adag)‖ +
        ‖A.comp (D - Dbar)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ Z₀ + Z₁ + Z₂ * ρ := by linarith

/-- **Radii polynomial theorem, derivative form** with `Z(r) = Z₀ + Z₁ + Z₂ r` and
`p(r) = Z₂ r² - (1 - Z₀ - Z₁) r + Y₀`. Here `A†` is any bounded approximation of
`DF(ū)` (in practice a finite block plus a diagonal tail). -/
theorem radii_polynomial_fderiv [NormedSpace ℝ E] [CompleteSpace E] (F : E → E)
    (DF : E → E →L[ℝ] E) (A Adag : E →L[ℝ] E) (hA : Function.Injective A) (ubar : E)
    {Y₀ Z₀ Z₁ Z₂ r : ℝ} (hr : 0 < r) (hZ₀ : 0 ≤ Z₀) (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂)
    (hF : ∀ u ∈ closedBall ubar r, HasFDerivAt F (DF u) u)
    (hY : ‖A (F ubar)‖ ≤ Y₀)
    (h₀ : ‖ContinuousLinearMap.id ℝ E - A.comp Adag‖ ≤ Z₀)
    (h₁ : ‖A.comp (DF ubar - Adag)‖ ≤ Z₁)
    (h₂ : ∀ u ∈ closedBall ubar r, ‖A.comp (DF u - DF ubar)‖ ≤ Z₂ * ‖u - ubar‖)
    (hp : radiiPoly Y₀ (Z₀ + Z₁) Z₂ r < 0) :
    ∃ u ∈ closedBall ubar r, F u = 0 ∧ ∀ v ∈ closedBall ubar r, F v = 0 → v = u := by
  refine radii_polynomial_zero F A.toLinearMap.toAddMonoidHom hA ubar hr
    (by positivity) hZ₂ hY ?_ hp
  intro u hu v hv
  have hderiv : ∀ w ∈ closedBall ubar r, HasFDerivWithinAt (fun w => w - A (F w))
      (ContinuousLinearMap.id ℝ E - A.comp (DF w)) (closedBall ubar r) w := by
    intro w hw
    exact ((hasFDerivAt_id w).sub (A.hasFDerivAt.comp w (hF w hw))).hasFDerivWithinAt
  have hbound : ∀ w ∈ closedBall ubar r,
      ‖ContinuousLinearMap.id ℝ E - A.comp (DF w)‖ ≤ Z₀ + Z₁ + Z₂ * r := by
    intro w hw
    have hw' : ‖w - ubar‖ ≤ r := by rw [← dist_eq_norm]; exact hw
    have := norm_id_sub_comp_le A Adag (DF w) (DF ubar) h₀ h₁ (h₂ w hw)
    nlinarith
  have := (convex_closedBall ubar r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hbound hv hu
  simpa using this

/-- A radius smaller than the residual bound is always rejected (nonnegative `Z`'s). -/
theorem radii_polynomial_rejects_small {Y₀ Z₀ Z₂ r : ℝ} (hZ₀ : 0 ≤ Z₀) (hZ₂ : 0 ≤ Z₂)
    (hr : 0 ≤ r) (hrY : r < Y₀) : ¬ radiiPoly Y₀ Z₀ Z₂ r < 0 := by
  unfold radiiPoly
  have : 0 ≤ Z₂ * r ^ 2 := by positivity
  have : 0 ≤ Z₀ * r := by positivity
  nlinarith

/-- **The degenerate inverse `A = 0` cannot pass the radii test.** For `T = id` on a
nontrivial space, any valid Lipschitz bound on a ball of positive radius satisfies
`Z₀ + Z₂ r ≥ 1`, hence `p(r) ≥ Y₀ ≥ 0`. Contrast `zero_inverse_counterexample`, where the
bare fixed-point claim for `A = 0` is vacuously true. -/
theorem radii_polynomial_rejects_identity [NormedSpace ℝ E] [Nontrivial E] (ubar : E)
    {Y₀ Z₀ Z₂ r : ℝ} (hr : 0 < r) (hY : ‖ubar - ubar‖ ≤ Y₀)
    (hlip : ∀ u ∈ closedBall ubar r, ∀ v ∈ closedBall ubar r,
      ‖u - v‖ ≤ (Z₀ + Z₂ * r) * ‖u - v‖) :
    ¬ radiiPoly Y₀ Z₀ Z₂ r < 0 := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hne : 0 < ‖e‖ := norm_pos_iff.2 he
  set u := ubar + (r / ‖e‖) • e
  have hnorm : ‖u - ubar‖ = r := by
    simp only [u, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hne)]
    field_simp
  have hu : u ∈ closedBall ubar r := by rw [mem_closedBall, dist_eq_norm, hnorm]
  have h := hlip u hu ubar (mem_closedBall_self hr.le)
  rw [hnorm] at h
  have hZ : 1 ≤ Z₀ + Z₂ * r := by
    by_contra hc; have hc' := lt_of_not_ge hc; nlinarith
  have hY0 : 0 ≤ Y₀ := (norm_nonneg _).trans hY
  rw [radiiPoly_eq]
  nlinarith

end LeanTheory.Certificates
