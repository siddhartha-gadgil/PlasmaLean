/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkEndpointContinuation
public import PlasmaLean.Design.DommaschkBackwardRectangle
public import PlasmaLean.Certificates.PositionFrameWide

/-! # Physical field and Jacobian bounds on wider moving-frame rectangles

The geometric determinant and operator tests justify the change of coordinates.
Regularity and the spatial Jacobian are checked on the entire proposed rectangle.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkWideTraceFields
set_option linter.style.longLine false

section
open Certificates PositionFrameSlabs QPoly TrajectoryTaylorModel DommaschkKam
open DommaschkBounceField DommaschkBounceTaylor DommaschkJacobian Set
open scoped RealInnerProductSpace
open DommaschkPhysicalTraceStep

theorem field_bounds_of_geometry {lim : Limits} {s : PositionFrameSlabs.State} {r : Step} {a phase sign : ℝ}
    (ok : geometry lim s r = true)
    (reg : ∀ t ∈ Icc a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80),
      let x := reference a r t + moving s r a t v
      0 < x 0 ∧ atPoint dD (x 0) (phase + sign * t) (x 1) ≠ 0)
    (quad : ∀ t ∈ Ico a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80),
      ∀ w : Plane, let x := reference a r t + moving s r a t v
      ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian phase sign t x)
        (moving s r a t) (frameVelocity s.frame r.frame) w⟫ ≤ r.mu * ‖w‖^2)
    (res : ∀ t ∈ Ico a (a + 1 / 64), ‖(moving s r a t).symm
      (euclideanFlow phase sign t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect) :
    FieldBounds s r a (euclideanFlow phase sign) (velocityJacobian phase sign) ballDomain := by
  let S := Icc a (a + 1 / 64) ×ˢ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)
  let x := fun q : ℝ × Plane => reference a r q.1 + moving s r a q.1 q.2
  let g := fun q : ℝ × Plane => (q.1,x q)
  have geo := ok
  have cm : ContinuousOn (fun t => (moving s r a t).toContinuousLinearMap) (Icc a (a + 1 / 64)) :=
    fun _ ht => (hasDerivWithinAt_frame geo a ht).continuousWithinAt
  have fstmem : MapsTo Prod.fst S (Icc a (a + 1 / 64)) := fun _ h => h.1
  have cp : Continuous (reference a r) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_reference a r t).continuousAt)
  have cg : ContinuousOn g S := continuous_fst.continuousOn.prodMk
    ((cp.comp continuous_fst).continuousOn.add
      ((cm.comp continuous_fst.continuousOn fstmem).clm_apply continuous_snd.continuousOn))
  have regular {q : ℝ × Plane} (hq : q ∈ S) :
      0 < x q 0 ∧ clockValue dD phase sign (g q) ≠ 0 := reg _ hq.1 _ hq.2
  refine ⟨?_,?_,?_,quad,res⟩
  · intro q hq
    exact (continuousAt_euclideanFlow phase sign (g q) (regular hq).1
      (regular hq).2).comp_continuousWithinAt (cg q hq)
  · intro q hq
    exact (continuousAt_velocityJacobian phase sign (g q) (regular hq).2).comp_continuousWithinAt
      (cg q hq)
  · intro t ht v hv
    obtain ⟨hr,hd⟩ := reg t ht v hv
    exact physical_derivative phase sign t _ hr hd

end

section
open Certificates PositionFrameSlabs TrajectoryTaylorModel QPoly Set
open DommaschkPhysicalTraceStep DommaschkKam DommaschkBounceTaylor
open DommaschkProjectedTrial

theorem forward_membership {lim : Limits} {s : State} {r : Step} {m : Inputs}
    {radial vertical : ℕ} (ok : geometry lim s r = true) (hm : CenterMatches r m)
    (box : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (hu : (m.u.radius : ℝ) = (radial : ℝ) / 2 ^ 80)
    (hz : (m.z.radius : ℝ) = (vertical : ℝ) / 2 ^ 80)
    {a t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) :
    let x := reference a r t + moving s r a t v
    m.u.Mem (coord a t) (x 0 - dkR0) ∧ m.z.Mem (coord a t) (x 1) := by
  have hs := abs_coord_le ht
  obtain ⟨cu,cz⟩ := box.coordinates hs (det_ne_zero (ok) hs)
    (by simpa using hv : ‖v‖ ≤ r.trial / (2 : ℝ) ^ 80)
  have x := congrFun (hm.position a t) 0
  have z := congrFun (hm.position a t) 1
  change reference a r t 0 = dkR0 + eval m.u.poly (coord a t) at x
  change reference a r t 1 = eval m.z.poly (coord a t) at z
  dsimp only
  constructor
  · rw [Model.Mem, hu, PiLp.add_apply, x]
    change |_ + moving s r a t v 0 - _ - _| ≤ _
    convert cu using 2
    unfold moving
    ring
  · rw [Model.Mem, hz, PiLp.add_apply, z, add_sub_cancel_left]
    exact cz

end

section
open Certificates PositionFrameSlabs TrajectoryTaylorModel QPoly Set
open DommaschkKam DommaschkBounceTaylor
open DommaschkShiftedTrial

theorem backward_membership {lim : Limits} {s : State} {r : Step} {box : Inputs} {radial vertical : ℕ}
    (ok : geometry lim s r = true)
    (axes : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (fits : Fits r box radial vertical) {a t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) :
    let x := reference a r t + moving s r a t v
    box.u.Mem (coord a t) (x 0 - dkR0) ∧ box.z.Mem (coord a t) (-x 1) := by
  have hs := abs_coord_le ht
  obtain ⟨u,z⟩ := axes.coordinates hs (det_ne_zero (ok) hs)
    (by simpa using hv : ‖v‖ ≤ (r.trial : ℝ) / 2 ^ 80)
  dsimp only
  constructor
  · apply enclose (a := ⟨radialPoly r, (radial : ℚ) / 2 ^ 80⟩) hs _ fits.u
    simp only [Model.Mem, radialPoly, eval_difference, eval_cons, eval_nil, mul_zero, add_zero,
      Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, PiLp.add_apply]
    change |eval (polynomial r 0) _ + moving s r a t v 0 - dkR0 -
      (eval (polynomial r 0) _ - 29 / 32)| ≤ _
    convert u using 2
    unfold dkR0 moving
    ring
  · apply enclose (a := ⟨verticalPoly r, (vertical : ℚ) / 2 ^ 80⟩) hs _ fits.z
    simp only [Model.Mem, verticalPoly, eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul,
      PiLp.add_apply, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
    change |-(eval (polynomial r 1) _ + moving s r a t v 1) - -eval (polynomial r 1) _| ≤ _
    rw [show -(eval (polynomial r 1) (coord a t) + moving s r a t v 1) -
      -eval (polynomial r 1) (coord a t) = -moving s r a t v 1 by ring, abs_neg]
    exact z

end

section
open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkBounceTaylor Set
open DommaschkPhysicalTraceStep DommaschkKam DommaschkKam.DkPoly DommaschkJacobian
open DommaschkBounceField (atPoint)
open scoped RealInnerProductSpace
open DommaschkEndpointContinuation

theorem forward_rectangle {lim : Limits} {s : State} {r : Step} {a α : ℝ} {box : Inputs}
    {left right : Frame} {radial vertical : ℕ} (ok : geometry lim s r = true)
    (axes : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (centres : CenterMatches r box)
    (u : (box.u.radius : ℝ) = (radial : ℝ) / 2 ^ 80)
    (z : (box.z.radius : ℝ) = (vertical : ℝ) / 2 ^ 80)
    (safe : box.u.radius + magnitude (difference box.u.poly [0]) ≤ 1 / 2)
    (l : s.frame = left) (c : r.frame = right)
    (den : ∀ t ∈ Icc a (a + 1 / 64), ∀ R z,
      box.u.Mem (coord a t) (R - dkR0) → box.z.Mem (coord a t) z → 0 < atPoint dD R (α + t) z)
    (jac : ∀ t ∈ Icc a (a + 1 / 64), ∀ R z,
      box.u.Mem (coord a t) (R - dkR0) → box.z.Mem (coord a t) z → ∀ w : Plane,
      ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
        (spatialMatrix (R - dkR0) z (Real.cos (2 * (α + t))) (Real.sin (2 * (α + t))))
        (frameEquiv left right (coord a t)) (frameVelocity left right) w⟫ ≤ r.mu * ‖w‖ ^ 2)
    (res : ∀ t ∈ Ico a (a + 1 / 64), ‖(moving s r a t).symm
      (euclideanFlow α 1 t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect) :
    FieldBounds s r a (euclideanFlow α 1) (velocityJacobian α 1) ballDomain := by
  apply field_bounds_of_geometry ok _ _ res
  · intro t ht v hv
    let x := reference a r t + moving s r a t v
    obtain ⟨hu, hz⟩ := forward_membership ok centres axes u z ht hv
    have hr := enclose (c := ⟨[0], 1 / 2⟩) (abs_coord_le ht) hu safe
    change (⟨[0], 1 / 2⟩ : Model).Mem (coord a t) (x 0 - dkR0) at hr
    norm_num [Model.Mem, dkR0, abs_le] at hr
    have pos : 0 < x 0 := by linarith
    exact ⟨pos, by simpa only [one_mul] using (den t ht (x 0) (x 1) hu hz).ne'⟩
  · intro t ht v hv w
    let x := reference a r t + moving s r a t v
    have ht' := Ico_subset_Icc_self ht
    obtain ⟨hu, hz⟩ := forward_membership ok centres axes u z ht' hv
    have hj := jac t ht' (x 0) (x 1) hu hz w
    change ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian α 1 t x)
      (moving s r a t) (frameVelocity s.frame r.frame) w⟫ ≤ _
    rw [velocityJacobian_spatial]
    simpa only [one_mul, one_smul, moving, l, c] using hj

end

section
open Certificates PositionFrameSlabs TrajectoryTaylorModel Set DommaschkKam DommaschkKam.DkPoly
open DommaschkJacobian DommaschkJacobianReflection DommaschkShiftedTrial DommaschkBounceTaylor
open DommaschkBounceField (atPoint)
open scoped RealInnerProductSpace
open DommaschkBackwardRectangle

theorem backward_rectangle {lim : Limits} {s : State} {r : Step} {a α : ℝ} {box : Inputs}
    {left right : Frame} {radial vertical : ℕ} (axis : DommaschkSymmetricSections.Axis α)
    (ok : geometry lim s r = true)
    (axes : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (fits : Fits r box radial vertical)
    (safe : box.u.radius + magnitude (difference box.u.poly [0]) ≤ 1 / 2)
    (l : s.frame = reflectFrame left) (c : r.frame = reflectFrame right)
    (den : ∀ t ∈ Icc a (a + 1 / 64), ∀ R z,
      box.u.Mem (coord a t) (R - dkR0) → box.z.Mem (coord a t) z →
      0 < atPoint dD R (α + t) z)
    (jac : ∀ t ∈ Icc a (a + 1 / 64), ∀ R z,
      box.u.Mem (coord a t) (R - dkR0) → box.z.Mem (coord a t) z →
      ∀ w : Plane, ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
        (spatialMatrix (R - dkR0) z (Real.cos (2 * (α + t))) (Real.sin (2 * (α + t))))
        (frameEquiv left right (coord a t)) (frameVelocity left right) w⟫ ≤ r.mu * ‖w‖ ^ 2)
    (res : ∀ t ∈ Ico a (a + 1 / 64), ‖(moving s r a t).symm
      (euclideanFlow α (-1) t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect) :
    FieldBounds s r a (euclideanFlow α (-1)) (velocityJacobian α (-1)) ballDomain := by
  apply field_bounds_of_geometry ok _ _ res
  · intro t ht v hv
    let x := reference a r t + moving s r a t v
    obtain ⟨hu,hz⟩ := backward_membership ok axes fits ht hv
    have hr := enclose (c := ⟨[0], 1 / 2⟩) (abs_coord_le ht) hu safe
    change (⟨[0],1/2⟩ : Model).Mem (coord a t) (x 0 - dkR0) at hr
    norm_num [Model.Mem,dkR0,abs_le] at hr
    have pos : 0 < x 0 := by linarith
    have hd := den t ht (x 0) (-x 1) hu hz
    have heq := DommaschkSymmetricSections.denominator axis (x 0) (-x 1) t
    simp only [neg_neg] at heq
    refine ⟨pos, ?_⟩
    change atPoint dD (x 0) (α + -1 * t) (x 1) ≠ 0
    rw [neg_one_mul, ← sub_eq_add_neg, heq]
    exact hd.ne'
  · intro t ht v hv w
    let x := reference a r t + moving s r a t v
    have h := Ico_subset_Icc_self ht
    obtain ⟨hu,hz⟩ := backward_membership ok axes fits h hv
    have det := det_ne_zero (ok) (abs_coord_le h)
    rw [l,c,reflected_det] at det
    have est := DommaschkSymmetricSections.quadratic_upper axis (x := x) det
      (jac t h (x 0) (-x 1) hu hz) w
    simpa only [x, moving, l, c] using est

end

end PlasmaLean.Design.DommaschkWideTraceFields
