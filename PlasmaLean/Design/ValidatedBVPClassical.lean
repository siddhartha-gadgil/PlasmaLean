/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.ValidatedBVP
public import PlasmaLean.Certificates.FourierRegularity

/-!
# The validated BVP has a classical `C²` solution

`PlasmaLean.Design.ValidatedBVP.validated_bvp_uniform` gives an even sequence `u* ∈ ℓ¹(ℤ)`
solving the coefficient equation `-(1+k²) u*ₖ + (u* ⋆ u*)ₖ - fₖ = 0` within `10⁻⁴` of the
4-mode candidate `ū`. Here we close the regularity gap recorded in that file.

* The equation gives `-k² u*ₖ = gₖ` with `g = u* - u* ⋆ u* + f ∈ ℓ¹`, so
  `∑ (1 + k²)|u*ₖ| < ∞` and `U = evalCos u*` is `C²` and `2π`-periodic, with termwise
  derivatives (`Certificates.classical_of_coeff`).
* Since `u*` is even, `evalCos (u* ⋆ u*) = U²` (`Certificates.evalCos_conv`), and
  `evalCos f = (4/5) cos θ` (`evalCos_forcing`).

**Result** (`validated_bvp_classical`). There is a `C²`, `2π`-periodic, even function `U`
with

  `U''(θ) - U(θ) + U(θ)² = (4/5) cos θ` for every real `θ`,

and `|U(θ) - ū(θ)| ≤ 10⁻⁴` for all `θ`, where `ū(θ) = ∑_{|k| ≤ 3} ūₖ cos kθ` is the explicit
rational trigonometric polynomial of the certificate. Non-triviality: `U(π) - U(0) ≥ 9/10`
(`validated_bvp_classical_nonconstant`), so `U` is not a constant solution.

**Scope.** Uniqueness is proved in the coefficient space (within `1/10` of `ū` in `ℓ¹`),
not among all classical solutions; transferring it would require identifying the Fourier
coefficients of an arbitrary classical solution, which is not formalized.
-/
public section
noncomputable section

namespace PlasmaLean.Design.ValidatedBVP

open PlasmaLean.Certificates

/-- The forcing sequence is the function `(4/5) cos θ`. -/
theorem evalCos_forcing (θ : ℝ) : evalCos forcing θ = 4 / 5 * Real.cos θ := by
  rw [evalCos, tsum_eq_sum (s := {-1, 1}) (fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hne : k.natAbs ≠ 1 := by omega
    simp [forcing_apply, fq, hne])]
  rw [Finset.sum_pair (by norm_num)]
  simp only [forcing_apply, fq]
  norm_num [Real.cos_neg]
  ring

/-- The candidate `ū` evaluated at `θ`. -/
@[expose] def abarFun (θ : ℝ) : ℝ := ∑ k ∈ blk, ((abarq k : ℚ) : ℝ) * Real.cos (k * θ)

/-- **Classical validated solution.** There is a `C²`, `2π`-periodic, even function `U`
satisfying `U'' - U + U² = (4/5) cos θ` at every point, uniformly within `10⁻⁴` of the
candidate `ū`. It is the cosine series of the unique coefficient solution within `1/10` of
`ū` in `ℓ¹`. -/
theorem validated_bvp_classical :
    ∃ U : ℝ → ℝ, ContDiff ℝ 2 U ∧ Function.Periodic U (2 * Real.pi) ∧
      (∀ θ, U (-θ) = U θ) ∧
      (∀ θ, deriv (deriv U) θ - U θ + U θ ^ 2 = 4 / 5 * Real.cos θ) ∧
      ∀ θ, |U θ - abarFun θ| ≤ 1 / 10000 := by
  obtain ⟨u, hcoef, heven, -, hunif, -⟩ := validated_bvp_uniform
  set g : Ell1Z := (u + forcing) - conv 1 u u with hg
  have hcoef' : ∀ k : ℤ, -((k : ℝ) ^ 2 * u k) = g k := by
    intro k
    have := hcoef k
    rw [hg, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply, forcing_apply]
    linarith
  obtain ⟨hC2, hper, -, -, hdd⟩ := classical_of_coeff u g hcoef'
  refine ⟨evalCos u, hC2, hper, fun θ => ?_, fun θ => ?_, fun θ => hunif θ⟩
  · unfold evalCos
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; funext k
    simp only [Equiv.neg_apply, heven, Int.cast_neg]
    congr 1
    rw [show -(k : ℝ) * -θ = k * θ by ring]
  · rw [hdd θ, hg, evalCos_sub, evalCos_add, evalCos_forcing, evalCos_conv u u heven]
    ring

/-- Exact value `ū(0) = -0.31845` (rational check). -/
theorem abar_sum_zero : ∑ k ∈ blk, abarq k = -31845 / 100000 := by decide +kernel

/-- Exact value `ū(π) = 0.60587` (rational check). -/
theorem abar_sum_pi : ∑ k ∈ blk, abarq k * (-1) ^ k = 60587 / 100000 := by decide +kernel

/-- Non-triviality: the classical solution is not constant, since
`U(π) - U(0) ≥ 9/10` (the candidate has `ū(π) - ū(0) = 0.92432`). -/
theorem validated_bvp_classical_nonconstant :
    ∃ U : ℝ → ℝ, ContDiff ℝ 2 U ∧
      (∀ θ, deriv (deriv U) θ - U θ + U θ ^ 2 = 4 / 5 * Real.cos θ) ∧
      9 / 10 ≤ U Real.pi - U 0 := by
  obtain ⟨U, hC2, -, -, hode, hclose⟩ := validated_bvp_classical
  refine ⟨U, hC2, hode, ?_⟩
  have h0 := hclose 0
  have hπ := hclose Real.pi
  have hb0 : abarFun 0 = -31845 / 100000 := by
    have := ratCast_le (le_of_eq abar_sum_zero)
    have h2 := ratCast_le (le_of_eq abar_sum_zero.symm)
    push_cast at this h2
    simp only [abarFun, mul_zero, Real.cos_zero, mul_one]
    linarith
  have hbπ : abarFun Real.pi = 60587 / 100000 := by
    have := ratCast_le (le_of_eq abar_sum_pi)
    have h2 := ratCast_le (le_of_eq abar_sum_pi.symm)
    push_cast at this h2
    simp only [abarFun, Real.cos_int_mul_pi]
    linarith
  rw [hb0] at h0
  rw [hbπ] at hπ
  have := (abs_le.1 h0).2
  have := (abs_le.1 hπ).1
  linarith

end PlasmaLean.Design.ValidatedBVP
