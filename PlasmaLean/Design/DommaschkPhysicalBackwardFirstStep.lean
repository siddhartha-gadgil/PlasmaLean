/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianBackward000
public import PlasmaLean.Design.DommaschkPhysicalTraceStep
public import PlasmaLean.Design.DommaschkTraceResidualBack000

/-! # First backward physical QA2R moving-frame step

The actual signed field is integrated over outward time from 0 to 1/64. The
spatial estimate comes from stellarator reflection of the first forward
Jacobian. The reference residual uses the archived backward polynomial.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalBackwardFirstStep

open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkKam DommaschkBounceField
open DommaschkJacobian DommaschkPhysicalTraceStep DommaschkJacobianBackward000 Set
open scoped RealInnerProductSpace

theorem checked : test pilotLimits seed row = true := by with_unfolding_all rfl

private theorem trialMatches : CenterMatches row trial := by
  constructor <;> with_unfolding_all rfl

private theorem central : CenterMatches row DommaschkTraceResidualBack000.reference := by
  constructor <;> with_unfolding_all rfl

private theorem clock (t : ℝ) : coord 0 t = 128*t-1 := by simp [coord]

private theorem member {t : ℝ} (ht : t ∈ Icc 0 (0 + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80)) :
    let x := reference 0 row t + moving seed row 0 t v
    trial.u.Mem (128*t-1) (x 0 - dkR0) ∧ trial.z.Mem (128*t-1) (x 1) := by
  have radius : (trial.u.radius : ℝ) = row.physicalTrial / (2 : ℝ) ^ 80 := by
    change (((row.physicalTrial : ℚ) / 2^80 : ℚ) : ℝ) = _
    push_cast
    rfl
  simpa only [clock] using trial_membership checked trialMatches radius (by rfl) ht hv

/-- All three analytic inputs concern the true signed field on the backward row. -/
theorem field_bounds : FieldBounds seed row 0 (euclideanFlow 0 (-1))
    (velocityJacobian 0 (-1)) ballDomain := by
  apply DommaschkPhysicalTraceStep.field_bounds checked
  · intro t ht v hv
    obtain ⟨u,z⟩ := member ht hv
    let x := reference 0 row t + moving seed row 0 t v
    have hs : |128*t-1| ≤ 1 := by simpa only [clock] using abs_coord_le ht
    have radial := enclose (c := ⟨[0],1/2⟩) hs u (by kernel_fact)
    have pos : 0 < x 0 := by
      change (⟨[0],1/2⟩ : Model).Mem (128*t-1) (x 0-dkR0) at radial
      norm_num [Model.Mem, dkR0, abs_le] at radial
      linarith
    have den := denominator_pos (by simpa using ht) u z
    exact ⟨pos,by simpa only [zero_add,neg_one_mul,atPoint] using den.ne'⟩
  · intro t ht v hv w
    have ht' := Ico_subset_Icc_self ht
    obtain ⟨u,z⟩ := member ht' hv
    let x := reference 0 row t + moving seed row 0 t v
    have hj := DommaschkJacobianBackward000.physical_clock_log_norm (y := x)
      (by simpa using ht') u z w
    have mu : (logNorm : ℝ) ≤ (row.mu : ℝ) := Rat.cast_le.mpr fits_record
    simpa only [x, moving, clock] using hj.trans (mul_le_mul_of_nonneg_right mu (sq_nonneg _))
  · intro t ht
    have h := Ico_subset_Icc_self ht
    apply residual_of_pulled ((Bool.and_eq_true_iff.mp checked).1) central h
    have fm : residualFrame seed row = DommaschkTraceResidualBack000.frame := by
      with_unfolding_all rfl
    have b : row.defect = DommaschkTraceResidualBack000.budget := rfl
    have h' : t ∈ Icc (0/64:ℝ) (1/64) := by simpa using h
    simpa only [clock, fm, b] using DommaschkTraceResidualBack000.physical_defect h'

/-- Every actual incoming state has a backward physical field trajectory, with
uniform error from the recorded curve and an exit in the recorded ellipsoid. -/
theorem physical_backward_step :
    Fields.TrajectorySlabs.Step (euclideanFlow 0 (-1)) (physicalSlab seed row 0)
      (stateSet seed) (stateSet (next row)) := physical_step_ball checked field_bounds

end PlasmaLean.Design.DommaschkPhysicalBackwardFirstStep
