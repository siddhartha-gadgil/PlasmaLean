/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameProjection
public import PlasmaLean.Design.DommaschkReflectedBack001
public import PlasmaLean.Design.DommaschkPhysicalBackwardFirstStep
public import PlasmaLean.Design.DommaschkPhysicalSecondStep

/-! # Second backward QA2R step by reflection on the actual trial ellipsoid

The archived backward coordinate radius exceeds the forward Taylor radius by
two units of 2⁻⁸⁰. The four endpoint row-length checks place the actual backward
ellipsoid strictly inside the original forward coordinate bounds.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalBackwardSecondStep
open Certificates PositionFrameSlabs DommaschkBounceField DommaschkKam DommaschkKam.DkPoly
open DommaschkPhysicalTraceStep DommaschkJacobian DommaschkJacobianReflection
open TrajectoryTaylorModel DommaschkReflectedBack001 Set
open scoped RealInnerProductSpace

/-- Exit ellipsoid of the first backward physical slab. -/
abbrev previous := next DommaschkJacobianBackward000.row

/-- The actual second step of the backward archive. -/
def row : Step := DommaschkPositionFramesBack.block0[1]

theorem checked : test pilotLimits previous row = true := by with_unfolding_all rfl

private theorem clock (t : ℝ) : coord (1 / 64) t = 128*t-3 := by unfold coord; ring
private theorem stop : (1 / 64 : ℝ) + 1 / 64 = 2 / 64 := by norm_num
private theorem central : CenterMatches row backReference := by
  constructor <;> with_unfolding_all rfl

/-- Each of the four endpoint frame rows fits the original forward spatial box. -/
theorem projections : PositionFrameProjection.Fits previous.frame row.frame row.trial
    2975746919922455539 := by
  constructor <;> unfold PositionFrameProjection.rowFits <;>
    apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl

private theorem reflected_membership {t : ℝ} (ht : t ∈ Icc (1 / 64) (1 / 64 + 1 / 64))
    {v : Plane} (hv : v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80)) :
    let x := reference (1 / 64) row t + moving previous row (1 / 64) t v
    DommaschkJacobianForward001.trial.u.Mem (128*t-3) (x 0 - dkR0) ∧
      DommaschkJacobianForward001.trial.z.Mem (128*t-3) (-x 1) := by
  let s := coord (1/64) t
  have hs : |s| ≤ 1 := abs_coord_le ht
  have det := det_ne_zero ((Bool.and_eq_true_iff.mp checked).1) hs
  have bound (i : Fin 2) : |moving previous row (1/64) t v i| ≤ (2975746919922455539:ℝ)/2^80 :=
    PositionFrameProjection.coordinates_le projections hs det (by simpa using hv) i
  have hr := congrFun (central.position (1/64) t) 0
  have hz := congrFun (central.position (1/64) t) 1
  change reference (1/64) row t 0 = dkR0 + QPoly.eval backReference.u.poly s at hr
  change reference (1/64) row t 1 = QPoly.eval backReference.z.poly s at hz
  have ru : backReference.u.poly = DommaschkJacobianForward001.trial.u.poly :=
    eq_of_beq (by kernel_fact)
  have rz : backReference.z.poly = QPoly.scale (-1) DommaschkJacobianForward001.trial.z.poly :=
    eq_of_beq (by kernel_fact)
  rw [ru] at hr
  rw [rz,QPoly.eval_scale,Rat.cast_neg,Rat.cast_one,neg_one_mul] at hz
  have rad : (DommaschkJacobianForward001.trial.u.radius : ℝ) =
      (2975746919922455539:ℝ)/2^80 := by
    change ((2975746919922455539/2^80 : ℚ) : ℝ) = _
    norm_num
  have radz : DommaschkJacobianForward001.trial.z.radius =
      DommaschkJacobianForward001.trial.u.radius := rfl
  dsimp only
  rw [← clock]
  constructor
  · rw [Model.Mem,rad,PiLp.add_apply,hr]
    convert bound 0 using 2
    ring
  · rw [Model.Mem,radz,rad,PiLp.add_apply,hz]
    convert bound 1 using 1
    rw [show -(-QPoly.eval DommaschkJacobianForward001.trial.z.poly s +
      moving previous row (1/64) t v 1) - QPoly.eval DommaschkJacobianForward001.trial.z.poly s =
      -(moving previous row (1/64) t v 1) by ring, abs_neg]

/-- The backward row's own growth allowance dominates the sharp forward bound. -/
theorem fits_backward : DommaschkJacobianForward001.logNorm ≤ row.mu := by kernel_fact

/-- Denominator, physical spatial growth, and physical central defect are
controlled on the actual backward ball with its recorded allowance. -/
theorem field_bounds : FieldBounds previous row (1 / 64) (euclideanFlow 0 (-1))
    (velocityJacobian 0 (-1)) ballDomain := by
  apply DommaschkPhysicalTraceStep.field_bounds checked
  · intro t ht v hv
    obtain ⟨u,z⟩ := reflected_membership ht hv
    let x := reference (1/64) row t + moving previous row (1/64) t v
    have hs : |128*t-3| ≤ 1 := by simpa only [clock] using abs_coord_le ht
    have radial := enclose (c := ⟨[0],1/2⟩) hs u (by kernel_fact)
    have pos : 0 < x 0 := by
      change (⟨[0],1/2⟩ : Model).Mem (128*t-3) (x 0 - dkR0) at radial
      norm_num [Model.Mem,dkR0,abs_le] at radial
      linarith
    have den := DommaschkJacobianForward001.denominator_pos (stop ▸ ht) u z
    have eq := DommaschkSectionReflection.evR_reflect
      (show DommaschkSectionReflection.parity dD 0 = true by kernel_fact) (x 0 - dkR0) (-x 1)
      (Real.cos (2*t)) (Real.sin (2*t))
    simp only [neg_neg,pow_zero,one_mul] at eq
    refine ⟨pos,?_⟩
    change atPoint dD (x 0) (0 + -1*t) (x 1) ≠ 0
    simp only [zero_add,neg_one_mul,atPoint,mul_neg,Real.cos_neg,Real.sin_neg,eq]
    exact den.ne'
  · intro t ht v hv w
    obtain ⟨u,z⟩ := reflected_membership (Ico_subset_Icc_self ht) hv
    let x := reference (1/64) row t + moving previous row (1/64) t v
    have ht' := stop ▸ Ico_subset_Icc_self ht
    have hs : |128*t-3| ≤ 1 := by simpa only [clock] using abs_coord_le (Ico_subset_Icc_self ht)
    have hd : affineDet DommaschkJacobianForward001.leftFrame
        DommaschkJacobianForward001.rightFrame (128*t-3) ≠ 0 :=
      det_ne_zero ((Bool.and_eq_true_iff.mp DommaschkPhysicalSecondStep.checked).1) hs
    have left : previous.frame = reflectFrame DommaschkJacobianForward001.leftFrame := rfl
    have right : row.frame = reflectFrame DommaschkJacobianForward001.rightFrame := rfl
    have eq := moving_quadratic_eq t (128*t-3) DommaschkJacobianForward001.leftFrame
      DommaschkJacobianForward001.rightFrame (flip x) (flip w) hd
    simp only [flip_twice] at eq
    have hj := DommaschkJacobianForward001.physical_clock_log_norm ht' u z (flip w)
    have mu : (DommaschkJacobianForward001.logNorm : ℝ) ≤ (row.mu:ℝ) :=
      Rat.cast_le.mpr fits_backward
    change ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian 0 (-1) t x)
      (moving previous row (1/64) t) (frameVelocity previous.frame row.frame) w⟫ ≤ _
    rw [moving,clock,left,right,eq,velocityJacobian_spatial]
    simpa [x,add_comm] using hj.trans (mul_le_mul_of_nonneg_right mu (sq_nonneg _))
  · intro t ht
    have h := Ico_subset_Icc_self ht
    apply residual_of_pulled ((Bool.and_eq_true_iff.mp checked).1) central h
    have fm : residualFrame previous row = backFrame := by with_unfolding_all rfl
    have b : row.defect = backBudget := rfl
    simpa only [clock, fm, b] using physical_defect (stop ▸ h)

/-- Each exit state of row zero starts a genuine physical solution through row one. -/
theorem physical_step : Fields.TrajectorySlabs.Step (euclideanFlow 0 (-1))
    (physicalSlab previous row (1 / 64)) (stateSet previous) (stateSet (next row)) :=
  physical_step_ball checked field_bounds

end PlasmaLean.Design.DommaschkPhysicalBackwardSecondStep
