/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkToroidalEnvelope

/-! # Exact upper obstruction for a uniform pilot toroidal field floor -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkToroidalEnvelope
open DommaschkKam DommaschkKam.DkPoly DommaschkBounceField

private def atTest (p : SP) : ℚ :=
  (p.map fun t => t.q * ((3 / 32 : ℚ) ^ t.a * 0 ^ t.b * (-1) ^ t.c * 0 ^ t.d)).sum

private theorem test_cast (p : SP) :
    evR (3 / 32) 0 (-1) 0 p = (atTest p : ℝ) := by
  induction p with
  | nil => simp [evR, atTest]
  | cons t p ih =>
    simp only [evR, atTest, List.map_cons, List.sum_cons] at ih ⊢
    push_cast
    rw [ih]
    norm_num

/-- The upper radial edge contains a value strictly below 24/25, so even a proposed
uniform unit toroidal field floor fails on this same spatial envelope. -/
theorem boundary_value :
    cylBphi 1 (Real.pi / 2) 0 = 2387710247 / 2500000000 := by
  have eq := (field_id (by norm_num : (0 : ℝ) < 1) (Real.pi / 2) 0).1
  rw [one_pow, one_mul] at eq
  rw [← eq, atPoint, show 2 * (Real.pi / 2) = Real.pi by ring,
    Real.cos_pi, Real.sin_pi, show 1 - dkR0 = (3 / 32 : ℝ) by norm_num [dkR0], test_cast]
  rw [show atTest dD = 2387710247 / 2500000000 by kernel_fact]
  norm_num

end PlasmaLean.Design.DommaschkToroidalEnvelope
