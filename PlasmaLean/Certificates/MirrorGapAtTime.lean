/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.TrajectoryTaylorModel
public import Mathlib.Algebra.Order.Ring.Abs

/-! # A fixed-time sign from a compensated squared-strength model -/

@[expose] public section
namespace PlasmaLean.Certificates.TrajectoryTaylorModel

/-- The model encloses a positive multiple of height squared minus strength squared. -/
def EndpointSign (above : Bool) (m : Model) (s : ℚ) : Prop :=
  if above then QPoly.evalQ m.poly s + m.radius < 0 else m.radius < QPoly.evalQ m.poly s

theorem strength_at {above : Bool} {m : Model} {s : ℚ} {w f h : ℝ}
    (model : m.Mem (s : ℝ) (w * (h ^ 2 - f ^ 2)))
    (ok : EndpointSign above m s) (positive : 0 < w) (field : 0 ≤ f) (height : 0 ≤ h) :
    if above then h < f else f < h := by
  have tube : |w * (h ^ 2 - f ^ 2) - (QPoly.evalQ m.poly s : ℝ)| ≤ (m.radius : ℝ) := by
    simpa only [Model.Mem,QPoly.eval_cast] using model
  rcases abs_le.mp tube with ⟨lo,hi⟩
  cases above
  · change m.radius < QPoly.evalQ m.poly s at ok
    have margin : (m.radius : ℝ) < (QPoly.evalQ m.poly s : ℝ) := by exact_mod_cast ok
    exact (sq_lt_sq₀ field height).mp (sub_pos.mp
      (pos_of_mul_pos_right (by linarith only [lo,margin]) positive.le))
  · change QPoly.evalQ m.poly s + m.radius < 0 at ok
    have margin : (QPoly.evalQ m.poly s : ℝ) + (m.radius : ℝ) < 0 := by exact_mod_cast ok
    exact (sq_lt_sq₀ height field).mp (sub_neg.mp
      (neg_of_mul_neg_right (by linarith only [hi,margin]) positive.le))

end PlasmaLean.Certificates.TrajectoryTaylorModel
