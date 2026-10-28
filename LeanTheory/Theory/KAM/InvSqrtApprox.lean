/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.InvSqrt

/-!
# A posteriori bound for an approximate inverse square root in the strip algebra

The residual of a torus for a field with an inverse-square-root variable can contain
the non-polynomial factor `V = (1 + E(K₀))^{−1/2}`. A certificate replaces it by a trigonometric
polynomial `V₀` and needs a bound on `V − V₀` computable from `V₀` alone. This file proves one:

* `invSqrt_approx_bound`: if `‖x − 1‖_ρ ≤ m < 1`, `V₀` has an inverse `V₀⁻¹` with
  `‖V₀⁻² − 1‖_ρ ≤ m`, `‖V₀ − 1‖_ρ ≤ a` (with `½ (1 − m)^{−3/2} m + a < 2`) and
  `‖V₀⁻¹‖_ρ ≤ b`, then
  `‖x^{−1/2} − V₀‖_ρ ≤ ½ (1 − m)^{−3/2} b² ‖V₀² x − 1‖_ρ`.

The proof shows that `V₀` is itself the node value `(V₀⁻²)^{−1/2}`. The two square roots of
`V₀⁻²`, `±V₀`, are told apart by invertibility of `w + V₀` near `2`; this is needed because `𝔸`
has zero divisors. The bound then follows from the Lipschitz estimate `Bd.invSqrt_sub`.
Only the defect `‖V₀²x − 1‖_ρ` (a polynomial in the data, certified exactly) enters linearly.

**Sanity.** `invSqrt_one_eq`: the degenerate case `x = 1`, `V₀ = 1` gives `1^{−1/2} = 1`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

open WEll1Z2

/-- `1` as the centre of the node in `𝔸`. -/
theorem algebraMap_one_FA : algebraMap ℂ FA ((1 : ℝ) : ℂ) = 1 := by
  rw [Complex.ofReal_one, map_one]

/-- Sanity (degenerate case): `1^{−1/2} = 1` in `𝔸`. -/
theorem invSqrt_one_eq : invSqrt ℂ 1 (1 : FA) = 1 := by
  have := invSqrt_algebraMap (𝕜 := ℂ) (A := FA) 1
  simpa using this

/-- **A posteriori bound for an approximate inverse square root.** -/
theorem invSqrt_approx_bound {ρ m a b η : ℝ} (hρ : 0 ≤ ρ) {x V₀ Vi : FA} (hinv : V₀ * Vi = 1)
    (hx : Bd ρ (x - 1) m) (hVi : Bd ρ (Vi ^ 2 - 1) m) (hm : m < 1) (hV₀ : Bd ρ (V₀ - 1) a)
    (hsmall : isqG 1 m ^ 3 / 2 * m + a < 2) (hb : Bd ρ Vi b) (hη : Bd ρ (V₀ ^ 2 * x - 1) η) :
    Bd ρ (invSqrt ℂ 1 x - V₀) (isqG 1 m ^ 3 / 2 * (b ^ 2 * η)) := by
  have e1 : (1 : FA) = algebraMap ℂ FA ((1 : ℝ) : ℂ) := algebraMap_one_FA.symm
  set w := invSqrt ℂ 1 (Vi ^ 2) with hw_def
  -- `w` is close to `1`
  have h0 : Bd ρ (algebraMap ℂ FA ((1 : ℝ) : ℂ) - algebraMap ℂ FA ((1 : ℝ) : ℂ)) m := by
    rw [sub_self]; exact (Bd_zero ρ).le hx.nonneg
  have hVi' : Bd ρ (Vi ^ 2 - algebraMap ℂ FA ((1 : ℝ) : ℂ)) m := by rw [← e1]; exact hVi
  have hw1 : Bd ρ (w - 1) (isqG 1 m ^ 3 / 2 * m) := by
    have h := Bd.invSqrt_sub hρ hVi' h0 hm (by rw [← e1]; exact hVi)
    rw [algebraMap_one_FA, invSqrt_one_eq] at h
    exact h
  -- `w² Vi² = 1`, hence `w² = V₀²`
  have hsq : w ^ 2 * Vi ^ 2 = 1 := by
    refine invSqrt_sq_mul ?_
    rw [norm_eq_wnorm]
    exact (hVi'.mono hρ le_rfl).2.trans_lt hm
  have hw2 : w ^ 2 = V₀ ^ 2 := by
    have h2 : (V₀ * Vi) ^ 2 = 1 := by rw [hinv, one_pow]
    linear_combination V₀ ^ 2 * hsq - w ^ 2 * h2
  -- `w + V₀` is a unit, so `w = V₀`
  have hunit : IsUnit (w + V₀) := by
    have hB : Bd ρ (w + V₀ - algebraMap ℂ FA (2 : ℂ)) (isqG 1 m ^ 3 / 2 * m + a) := by
      have e2 : w + V₀ - algebraMap ℂ FA (2 : ℂ) = (w - 1) + (V₀ - 1) := by
        rw [map_ofNat]; ring
      rw [e2]; exact hw1.add hV₀
    exact (Bd.inverse hρ hB (by simpa using hsmall)).1
  have hwV : w = V₀ := by
    have hz : (w - V₀) * (w + V₀) = 0 := by linear_combination hw2
    obtain ⟨uu, huu⟩ := hunit
    have : w - V₀ = (w - V₀) * (w + V₀) * ↑uu⁻¹ := by
      rw [← huu, mul_assoc, Units.mul_inv, mul_one]
    rw [hz, zero_mul] at this
    exact sub_eq_zero.1 this
  -- the Lipschitz bound
  have hxc : Bd ρ (x - algebraMap ℂ FA ((1 : ℝ) : ℂ)) m := by rw [← e1]; exact hx
  have hdiff : Bd ρ (x - Vi ^ 2) (b ^ 2 * η) := by
    have e3 : x - Vi ^ 2 = Vi ^ 2 * (V₀ ^ 2 * x - 1) := by
      have h2 : (V₀ * Vi) ^ 2 = 1 := by rw [hinv, one_pow]
      linear_combination (-x) * h2
    rw [e3]; exact (hb.pow hρ 2).mul hρ hη
  have h := Bd.invSqrt_sub hρ hxc hVi' hm hdiff
  rw [← hw_def, hwV] at h
  exact h

end LeanTheory.Theory.KAM
