/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalFirstStep
public import PlasmaLean.Design.DommaschkPhysicalTraceStep
public import PlasmaLean.Design.DommaschkJacobianForward001
public import PlasmaLean.Design.DommaschkTraceResidualForward001

/-! # Second forward physical step of the QA2R pilot

The nonlinear field solve starts in the exit ellipsoid of the first step.
All field tests use the second recorded curve, its inherited frame, and the
physical clock from 1/64 to 2 / 64.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalSecondStep

open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkKam DommaschkBounceField
open DommaschkJacobian DommaschkPhysicalTraceStep Set
open scoped RealInnerProductSpace

/-- Exact exit of the first physical step. -/
abbrev previous := next DommaschkPhysicalFirstStep.row

/-- Second datum in the first block of the archived pilot. -/
def row : Step := DommaschkPositionFramesFwd.block0[1]

theorem checked : test pilotLimits previous row = true := by with_unfolding_all rfl

private theorem clock (t : ℝ) : coord (1 / 64) t = 128*t-3 := by unfold coord; ring

private theorem stop : (1 / 64 : ℝ) + 1 / 64 = 2 / 64 := by norm_num

private theorem trialMatches : CenterMatches row DommaschkJacobianForward001.trial := by
  constructor <;> with_unfolding_all rfl

private theorem central : CenterMatches row DommaschkTraceResidualForward001.reference := by
  constructor <;> with_unfolding_all rfl

private theorem member {t : ℝ} (ht : t ∈ Icc (1 / 64) (1 / 64 + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80)) :
    let x := reference (1 / 64) row t + moving previous row (1 / 64) t v
    DommaschkJacobianForward001.trial.u.Mem (128*t-3) (x 0 - dkR0) ∧
      DommaschkJacobianForward001.trial.z.Mem (128*t-3) (x 1) := by
  have radius : (DommaschkJacobianForward001.trial.u.radius : ℝ) =
      row.physicalTrial / (2 : ℝ) ^ 80 := by
    change ((2975746919922455539 / 2^80 : ℚ) : ℝ) = 2975746919922455539 / (2 : ℝ) ^ 80
    norm_num
  simpa only [clock] using trial_membership checked trialMatches radius (by rfl) ht hv

/-- Second physical slab with regularity, transformed logarithmic norm, and
defect all certified on the same Euclidean trial ball. -/
theorem field_bounds : FieldBounds previous row (1 / 64) (euclideanFlow 0 1)
    (velocityJacobian 0 1) ballDomain := by
  apply DommaschkPhysicalTraceStep.field_bounds checked
  · intro t ht v hv
    obtain ⟨u,z⟩ := member ht hv
    let x := reference (1 / 64) row t + moving previous row (1 / 64) t v
    have hs : |128*t-3| ≤ 1 := by simpa only [clock] using abs_coord_le ht
    have radial := enclose (c := ⟨[0],1/2⟩) hs u (by kernel_fact)
    have pos : 0 < x 0 := by
      change (⟨[0],1/2⟩ : Model).Mem (128*t-3) (x 0-dkR0) at radial
      norm_num [Model.Mem, dkR0, abs_le] at radial
      linarith
    have den := DommaschkJacobianForward001.denominator_pos (stop ▸ ht) u z
    exact ⟨pos,by simpa only [zero_add,one_mul,atPoint] using den.ne'⟩
  · intro t ht v hv w
    have ht' := Ico_subset_Icc_self ht
    obtain ⟨u,z⟩ := member ht' hv
    let x := reference (1 / 64) row t + moving previous row (1 / 64) t v
    have hj := DommaschkJacobianForward001.physical_clock_log_norm (stop ▸ ht') u z w
    have eq := velocityJacobian_spatial 0 1 t x
    simp only [zero_add, one_mul, one_smul] at eq
    change ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian 0 1 t x) _ _ w⟫ ≤ _
    rw [eq]
    have hm : (DommaschkJacobianForward001.logNorm : ℝ) ≤ (row.mu : ℝ) :=
      Rat.cast_le.mpr DommaschkJacobianForward001.fits_record
    have l : previous.frame = DommaschkJacobianForward001.leftFrame := rfl
    have r : row.frame = DommaschkJacobianForward001.rightFrame := rfl
    simpa only [x, moving, l, r, clock] using hj.trans (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
  · intro t ht
    have h := Ico_subset_Icc_self ht
    apply residual_of_pulled ((Bool.and_eq_true_iff.mp checked).1) central h
    have fm : residualFrame previous row = DommaschkTraceResidualForward001.frame := by
      with_unfolding_all rfl
    have b : row.defect = DommaschkTraceResidualForward001.budget := rfl
    simpa only [clock, fm, b] using DommaschkTraceResidualForward001.physical_defect (stop ▸ h)

/-- Physical solution of the true field on the second interval, with the
inherited first-step exit state and the stored uniform outgoing position error. -/
theorem physical_second_step :
    Fields.TrajectorySlabs.Step (euclideanFlow 0 1) (physicalSlab previous row (1 / 64))
      (stateSet previous) (stateSet (next row)) := physical_step_ball checked field_bounds

end PlasmaLean.Design.DommaschkPhysicalSecondStep
