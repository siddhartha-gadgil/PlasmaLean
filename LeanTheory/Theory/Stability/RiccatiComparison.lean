/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Conditional Riccati comparison

A scalar comparison step:
if a real function `Y` satisfies the differential inequality

`Y' ≤ -ν Y + C ε Y²` on `[0, T)`, with `0 ≤ Y(0)` and `C ε Y(0) < ν`,

then `Y(t) ≤ Y(0)` on `[0, T]` (`riccati_le_initial`), and if moreover `Y ≥ 0` and `C ε ≥ 0`,
then `Y(t) ≤ Y(0) e^{-(ν - C ε Y(0)) t}` (`riccati_exp_decay`).

**Scope.** The differential inequality is a *hypothesis*. It is not derived from any PDE here:
no established theorem derives `Y' ≤ -ν Y + C ε_QS Y²` from the ideal MHD equations with
`ε_QS` the scalar quasisymmetry error, and
`LeanTheory.Sanity.QuasisymmetryNotSymmetry` shows that zero scalar QS error does not make the
pressure force invariant. Only the ODE comparison implication is formalized here.

Derivatives are right derivatives (`HasDerivWithinAt … (Ici t) t`), and the proofs use Mathlib's
fencing theorems `image_le_of_deriv_right_lt_deriv_boundary` and
`image_le_of_deriv_right_le_deriv_boundary`.

Sanity: `riccati_hyp_exp` shows the hypotheses are satisfiable by `Y₀ e^{-νt}`.
-/

open Set Filter Topology

public section
noncomputable section
namespace LeanTheory.Stability

/-- **Conditional Riccati comparison, monotone bound.** If `Y` is continuous on `[0, T]`, has
right derivative `Y'` on `[0, T)`, satisfies `Y' ≤ -ν Y + C ε Y²` there (a hypothesis, not a
PDE theorem), and `0 ≤ Y(0)` with `C ε Y(0) < ν`, then `Y(t) ≤ Y(0)` on `[0, T]`. -/
theorem riccati_le_initial {Y Y' : ℝ → ℝ} {T ν C ε : ℝ}
    (hcont : ContinuousOn Y (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hineq : ∀ t ∈ Ico 0 T, Y' t ≤ -ν * Y t + C * ε * Y t ^ 2)
    (h0 : 0 ≤ Y 0) (hsmall : C * ε * Y 0 < ν) :
    ∀ t ∈ Icc 0 T, Y t ≤ Y 0 := by
  intro t ht
  -- Fence by every constant `c > Y 0` with `C ε c < ν`.
  have hfence : ∀ c, Y 0 < c → C * ε * c < ν → Y t ≤ c := by
    intro c hc hcs
    refine image_le_of_deriv_right_lt_deriv_boundary (B := fun _ => c) (B' := fun _ => 0)
      hcont hderiv hc.le (fun _ => hasDerivAt_const _ _) ?_ ht
    intro s hs hYs
    have hcpos : 0 < c := lt_of_le_of_lt h0 hc
    have hneg : c * (C * ε * c - ν) < 0 := mul_neg_of_pos_of_neg hcpos (by linarith)
    calc Y' s ≤ -ν * Y s + C * ε * Y s ^ 2 := hineq s hs
      _ = c * (C * ε * c - ν) := by rw [hYs]; ring
      _ < 0 := hneg
  have hev : ∀ᶠ c in 𝓝[>] (Y 0), Y t ≤ c := by
    have hlt : ∀ᶠ c in 𝓝 (Y 0), C * ε * c < ν :=
      (continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const hsmall
    filter_upwards [nhdsWithin_le_nhds hlt, self_mem_nhdsWithin] with c hc1 hc2
    exact hfence c hc2 hc1
  exact ge_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) hev

/-- **Conditional Riccati comparison, exponential decay.** Under the hypotheses of
`riccati_le_initial`, if moreover `Y ≥ 0` on `[0, T]` (e.g. `Y` is a norm) and `C ε ≥ 0`, then
`Y(t) ≤ Y(0) e^{-(ν - C ε Y(0)) t}` on `[0, T]`. -/
theorem riccati_exp_decay {Y Y' : ℝ → ℝ} {T ν C ε : ℝ}
    (hcont : ContinuousOn Y (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hineq : ∀ t ∈ Ico 0 T, Y' t ≤ -ν * Y t + C * ε * Y t ^ 2)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ Y t) (hCε : 0 ≤ C * ε) (hsmall : C * ε * Y 0 < ν) :
    ∀ t ∈ Icc 0 T, Y t ≤ Y 0 * Real.exp (-(ν - C * ε * Y 0) * t) := by
  have hT : ∀ t ∈ Icc 0 T, 0 ≤ T := fun t ht => ht.1.trans ht.2
  set l := ν - C * ε * Y 0 with hl
  have hle := riccati_le_initial hcont hderiv hineq
  have hd : ∀ s ∈ Ico 0 T, HasDerivWithinAt (fun s => Y s * Real.exp (l * s))
      (Y' s * Real.exp (l * s) + Y s * (Real.exp (l * s) * l)) (Ici s) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (l * s)) (Real.exp (l * s) * l) s := by
      exact ((Real.hasDerivAt_exp (l * s)).comp s ((hasDerivAt_id' s).const_mul l)).congr_deriv
        (by ring)
    exact (hderiv s hs).mul he.hasDerivWithinAt
  intro t ht
  have h0 : 0 ≤ Y 0 := hnonneg 0 ⟨le_rfl, hT t ht⟩
  have hle0 := hle h0 hsmall
  have hg : Y t * Real.exp (l * t) ≤ Y 0 * Real.exp (l * 0) := by
    refine image_le_of_deriv_right_le_deriv_boundary (f := fun s => Y s * Real.exp (l * s))
      (B := fun _ => Y 0 * Real.exp (l * 0)) (B' := fun _ => 0)
      (hcont.mul (by fun_prop)) hd le_rfl continuousOn_const
      (fun _ _ => hasDerivWithinAt_const _ _ _) ?_ ht
    intro s hs
    have hYs : 0 ≤ Y s := hnonneg s (Ico_subset_Icc_self hs)
    have hY0 : Y s ≤ Y 0 := hle0 s (Ico_subset_Icc_self hs)
    have hq : C * ε * Y s ^ 2 ≤ C * ε * Y 0 * Y s := by
      have := mul_le_mul_of_nonneg_left hY0 (mul_nonneg hCε hYs)
      nlinarith
    have hlin : Y' s + l * Y s ≤ 0 := by
      have := hineq s hs
      rw [hl]
      nlinarith
    have he := Real.exp_pos (l * s)
    have : (Y' s + l * Y s) * Real.exp (l * s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hlin he.le
    linarith
  rw [mul_zero, Real.exp_zero, mul_one] at hg
  have he := Real.exp_pos (l * t)
  calc Y t = Y t * Real.exp (l * t) * Real.exp (-l * t) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
    _ ≤ Y 0 * Real.exp (-l * t) := by gcongr

/-- Sanity: the hypotheses are satisfiable. `Y(t) = Y₀ e^{-νt}` with `Y₀ ≥ 0` satisfies
`Y' ≤ -ν Y + C ε Y²` whenever `C ε ≥ 0` (for any `Y₀`; the comparison uses `Y₀ ≥ 0`). -/
theorem riccati_hyp_exp {ν C ε Y₀ : ℝ} (hCε : 0 ≤ C * ε) (t : ℝ) :
    HasDerivAt (fun s => Y₀ * Real.exp (-ν * s)) (Y₀ * (Real.exp (-ν * t) * -ν)) t ∧
      Y₀ * (Real.exp (-ν * t) * -ν) ≤
        -ν * (Y₀ * Real.exp (-ν * t)) + C * ε * (Y₀ * Real.exp (-ν * t)) ^ 2 := by
  refine ⟨?_, ?_⟩
  · have := (Real.hasDerivAt_exp (-ν * t)).comp t ((hasDerivAt_id t).const_mul (-ν))
    simpa using this.const_mul Y₀
  · have : 0 ≤ C * ε * (Y₀ * Real.exp (-ν * t)) ^ 2 := mul_nonneg hCε (sq_nonneg _)
    linarith

end LeanTheory.Stability
