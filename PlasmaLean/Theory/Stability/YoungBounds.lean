/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Scalar drive estimate for the energy-principle route

This is the pointwise algebra behind note 03's Young bound. The variables stand
for already bounded magnitudes, but the inequality itself holds for all real
inputs. No MHD energy identity, integral estimate, Poincaré inequality, admissible
space, or global coercivity constant is assumed to follow from this lemma.
-/
public section

namespace PlasmaLean.Stability

/-- Absorb a drive term into half a positive restoring term with an explicit loss. -/
theorem young_drive {A : ℝ} (hA : 0 < A) (Q J r : ℝ) :
    A / 2 * Q ^ 2 - J ^ 2 / (2 * A) * r ^ 2 ≤ A * Q ^ 2 - J * r * Q := by
  have hs : 0 ≤ (A * Q - J * r) ^ 2 := sq_nonneg _
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * A by linarith)).mp
  field_simp
  nlinarith

/-- Two independent positive restoring channels absorb current and pressure drives. -/
theorem two_channel_drive {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (Q d J P r : ℝ) :
    A / 2 * Q ^ 2 + B / 2 * d ^ 2 -
        (J ^ 2 / (2 * A) + P ^ 2 / (2 * B)) * r ^ 2 ≤
      A * Q ^ 2 - J * r * Q + B * d ^ 2 - P * r * d := by
  have h₁ := young_drive hA Q J r
  have h₂ := young_drive hB d P r
  nlinarith

end PlasmaLean.Stability
