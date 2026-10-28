/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Stability.BlockBounds

/-! # Exact rational certificates for two-block lower bounds
An accepted certificate is a theorem about real scalar blocks. Analytic bounds
linking those blocks to a specific operator remain explicit prerequisites.
-/
public section

namespace LeanTheory.Certificates

/-- Exact diagonal, coupling, and proposed positive margin data. -/
structure BlockCertificate where
  a : ℚ
  b : ℚ
  coupling : ℚ
  margin : ℚ
  deriving DecidableEq, Repr

namespace BlockCertificate
/-- Rational inequalities sufficient for a positive two-block margin. -/
@[expose] def check (c : BlockCertificate) : Bool :=
  decide (0 < c.margin ∧ c.margin ≤ c.a ∧ c.margin ≤ c.b ∧
    c.coupling ^ 2 ≤ (c.a - c.margin) * (c.b - c.margin))

/-- Soundness for every real pair, not a sample grid. -/
theorem sound (c : BlockCertificate) (h : c.check = true) :
    (0 : ℝ) < c.margin ∧ ∀ x y : ℝ,
      (c.margin : ℝ) * (x ^ 2 + y ^ 2) ≤ c.a * x ^ 2 - 2 * c.coupling * x * y + c.b * y ^ 2 := by
  have hq := of_decide_eq_true h
  change 0 < c.margin ∧ c.margin ≤ c.a ∧ c.margin ≤ c.b ∧
    c.coupling ^ 2 ≤ (c.a - c.margin) * (c.b - c.margin) at hq
  refine ⟨by exact_mod_cast hq.1, ?_⟩
  intro x y
  apply LeanTheory.Stability.two_block_margin
  · exact_mod_cast hq.2.1
  · exact_mod_cast hq.2.2.1
  · have hh : ((c.coupling ^ 2 : ℚ) : ℝ) ≤
        (((c.a - c.margin) * (c.b - c.margin) : ℚ) : ℝ) := by
      exact_mod_cast hq.2.2.2
    simpa only [pow_two, Rat.cast_mul, Rat.cast_sub] using hh

/-- An exact example with certified margin one. -/
theorem example_accepted : (⟨5, 2, 2, 1⟩ : BlockCertificate).check = true := by norm_num [check]

/-- Excessive coupling is rejected even when the diagonal entries are positive. -/
theorem coupling_rejected : (⟨5, 2, 3, 1⟩ : BlockCertificate).check = false := by norm_num [check]

/-- A zero requested margin does not certify strict positivity. -/
theorem zero_margin_rejected : (⟨5, 2, 2, 0⟩ : BlockCertificate).check = false := by
  norm_num [check]
end BlockCertificate
end LeanTheory.Certificates
