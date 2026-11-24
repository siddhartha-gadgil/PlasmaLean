/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeActionGeometry

/-! # Sparse physical field and opposite-section harmonic coefficient tables -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCoarseActionPhase
open DommaschkKam DommaschkKam.DkPoly

/-- Apply the change of angular variables `(c,s) ↦ (-c,-s)` before spatial Horner evaluation. -/
def halfTurn (p : SP) : SP := p.map fun m => {m with q := m.q * (-1)^(m.c+m.d)}

theorem halfTurn_eval (p : SP) (u z c s : ℝ) :
    evR u z c s (halfTurn p) = evR u z (-c) (-s) p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    change (((m.q * (-1)^(m.c+m.d) : ℚ) : ℝ) * _) + evR u z c s (halfTurn p) =
      (m.q : ℝ) * (u^m.a*z^m.b*(-c)^m.c*(-s)^m.d) + evR u z (-c) (-s) p
    rw [ih]
    push_cast
    rw [show -c = (-1:ℝ)*c by ring, show -s = (-1:ℝ)*s by ring, mul_pow, mul_pow, pow_add]
    ring

/-- The opposite-section table still evaluates the actual field at its physical azimuth. -/
theorem physical_phase (p : SP) (u z t : ℝ) :
    evR u z (Real.cos (2*t)) (Real.sin (2*t)) (halfTurn p) =
      evR u z (Real.cos (2*(Real.pi/2+t))) (Real.sin (2*(Real.pi/2+t))) p := by
  rw [halfTurn_eval, show 2*(Real.pi/2+t) = Real.pi+2*t by ring,
    Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi]
  simp

end PlasmaLean.Design.DommaschkCoarseActionPhase
