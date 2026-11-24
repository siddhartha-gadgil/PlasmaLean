/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkProjectedTrial

/-! # A reflected backward trial ellipsoid in a forward Taylor rectangle -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkProjectedTrial

open Certificates PositionFrameSlabs TrajectoryTaylorModel
open DommaschkPhysicalTraceStep DommaschkKam DommaschkBounceTaylor Set

/-- If the two model centres are related by vertical reflection, bounds for the
two backward frame rows place each reflected physical trial point in the forward
Jacobian model with its own radial and vertical widths. -/
theorem reflected_membership {lim : Limits} {s : State} {r : Step} {back box : Inputs}
    {radial vertical : ℕ} (ok : test lim s r = true) (center : CenterMatches r back)
    (sameR : back.u.poly = box.u.poly) (flipZ : back.z.poly = QPoly.scale (-1) box.z.poly)
    (fits : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (radR : (box.u.radius : ℝ) = (radial : ℝ) / 2 ^ 80)
    (radZ : (box.z.radius : ℝ) = (vertical : ℝ) / 2 ^ 80)
    {a t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) :
    let x := reference a r t + moving s r a t v
    box.u.Mem (coord a t) (x 0 - dkR0) ∧ box.z.Mem (coord a t) (-x 1) := by
  have hs := abs_coord_le ht
  obtain ⟨u,z⟩ := fits.coordinates hs (det_ne_zero ((Bool.and_eq_true_iff.mp ok).1) hs)
    (by simpa using hv : ‖v‖ ≤ (r.trial : ℝ) / 2 ^ 80)
  have hr := congrFun (center.position a t) 0
  have hz := congrFun (center.position a t) 1
  change reference a r t 0 = dkR0 + QPoly.eval back.u.poly (coord a t) at hr
  change reference a r t 1 = QPoly.eval back.z.poly (coord a t) at hz
  rw [sameR] at hr
  rw [flipZ, QPoly.eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul] at hz
  dsimp only
  constructor
  · rw [Model.Mem, radR, PiLp.add_apply, hr]
    convert u using 2
    unfold moving
    ring
  · rw [Model.Mem, radZ, PiLp.add_apply, hz]
    rw [show -(-QPoly.eval box.z.poly (coord a t) + moving s r a t v 1) -
        QPoly.eval box.z.poly (coord a t) = -(moving s r a t v 1) by ring, abs_neg]
    exact z

end PlasmaLean.Design.DommaschkProjectedTrial
