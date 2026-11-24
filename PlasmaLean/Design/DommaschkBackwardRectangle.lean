/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSymmetricSections
public import PlasmaLean.Design.DommaschkShiftedTrial

/-! # Backward physical field bounds from a forward rectangle at a symmetry section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkBackwardRectangle
open Certificates PositionFrameSlabs TrajectoryTaylorModel Set DommaschkKam DommaschkKam.DkPoly
open DommaschkJacobian DommaschkJacobianReflection DommaschkShiftedTrial DommaschkBounceTaylor
open DommaschkBounceField (atPoint)
open scoped RealInnerProductSpace

/-- A reflected forward rectangle controls the whole backward ODE step with the
backward witness's central defect, physical coordinates, and growth allowance. -/
theorem field_bounds {lim : Limits} {s : State} {r : Step} {a α : ℝ} {box : Inputs}
    {left right : Frame} {radial vertical : ℕ} (axis : DommaschkSymmetricSections.Axis α)
    (ok : test lim s r = true)
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
  apply DommaschkPhysicalTraceStep.field_bounds ok _ _ res
  · intro t ht v hv
    let x := reference a r t + moving s r a t v
    obtain ⟨hu,hz⟩ := membership ok axes fits ht hv
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
    obtain ⟨hu,hz⟩ := membership ok axes fits h hv
    have det := det_ne_zero ((Bool.and_eq_true_iff.mp ok).1) (abs_coord_le h)
    rw [l,c,reflected_det] at det
    have est := DommaschkSymmetricSections.quadratic_upper axis (x := x) det
      (jac t h (x 0) (-x 1) hu hz) w
    simpa only [x, moving, l, c] using est

end PlasmaLean.Design.DommaschkBackwardRectangle
