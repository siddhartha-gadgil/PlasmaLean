/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianReflection
public import PlasmaLean.Design.DommaschkPhysicalFirstStep
public import PlasmaLean.Design.DommaschkPositionFramesBack
public import PlasmaLean.Design.DommaschkTraceResidualBack000Inputs

/-! # The first backward QA2R Jacobian from physical reflection

This backward row has the same physical trial radius as the forward row.
Its own recorded logarithmic norm is checked after reflecting the physical
quadratic form.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJacobianBackward000

open DommaschkKam DommaschkKam.DkPoly DommaschkJacobian DommaschkJacobianReflection
open Certificates.TrajectoryTaylorModel Certificates.PositionFrameSlabs
open scoped RealInnerProductSpace

abbrev seed := DommaschkPositionFramesBack.start
def row : Step := DommaschkPositionFramesBack.block0.head (by intro h; contradiction)

def trial : DommaschkBounceTaylor.Inputs :=
  let ref := DommaschkTraceResidualBack000.reference
  let radius : ℚ := row.physicalTrial / 2^80
  ⟨⟨ref.u.poly, radius⟩, ⟨ref.z.poly, radius⟩, ref.cos, ref.sin⟩

def logNorm : ℚ := 201/10000

theorem fits_record : logNorm ≤ row.mu := by
  change 201/10000 ≤ (_ : ℚ)
  kernel_fact

private theorem forward_inputs {s R z : ℝ} (hu : trial.u.Mem s (R - dkR0))
    (hz : trial.z.Mem s z) :
    DommaschkBounceTaylorFirst.trial.u.Mem s (R - dkR0) ∧
      DommaschkBounceTaylorFirst.trial.z.Mem s (-z) := by
  have rad : trial.u = DommaschkBounceTaylorFirst.trial.u := by
    apply DommaschkBounceTaylor.Matches.eq
    constructor <;> apply eq_of_beq <;> kernel_fact
  have ht : DommaschkBounceTaylorFirst.trial.z.poly = Certificates.QPoly.scale (-1) trial.z.poly :=
    eq_of_beq (by kernel_fact)
  have he : DommaschkBounceTaylorFirst.trial.z.radius = trial.z.radius :=
    eq_of_beq (by kernel_fact)
  refine ⟨rad ▸ hu, ?_⟩
  simp only [Model.Mem, ht, he, Certificates.QPoly.eval_scale, Rat.cast_neg, Rat.cast_one,
    neg_one_mul, sub_neg_eq_add] at hz ⊢
  rwa [show -z + Certificates.QPoly.eval trial.z.poly s =
    -(z - Certificates.QPoly.eval trial.z.poly s) by ring, abs_neg]

/-- At the signed backward clock the denominator of the physical ODE stays positive. -/
theorem denominator_pos {t R z : ℝ} (ht : t ∈ Set.Icc 0 (1 / 64))
    (hu : trial.u.Mem (128 * t - 1) (R - dkR0)) (hz : trial.z.Mem (128 * t - 1) z) :
    0 < evR (R - dkR0) z (Real.cos (2 * (-t))) (Real.sin (2 * (-t))) dD := by
  have hs : |128*t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨u,h⟩ := forward_inputs hu hz
  have hc : t ∈ Set.Icc (0/64:ℝ) (1/64) := by simpa using ht
  have hin : DommaschkBounceTaylorFirst.trial.Mem (128*t-1) (R-dkR0) (-z)
      (Real.cos (2*t)) (Real.sin (2*t)) := by
    refine ⟨u,h,?_,?_⟩
    · change (DommaschkHarmonicSlab0.model false 0 false).Mem _ _
      simpa [Certificates.TrajectoryTrig.wave] using
        DommaschkHarmonicSlab0.physical false 0 false hc
    · change (DommaschkHarmonicSlab0.model false 0 true).Mem _ _
      simpa [Certificates.TrajectoryTrig.wave] using
        DommaschkHarmonicSlab0.physical false 0 true hc
  have low := DommaschkBounceTaylorFirst.dD_range hs
    (DommaschkBounceTaylorFirst.dD_checked.mem hs hin)
  have eq := DommaschkSectionReflection.evR_reflect
    (show DommaschkSectionReflection.parity dD 0 = true by kernel_fact) (R-dkR0) (-z)
    (Real.cos (2*t)) (Real.sin (2*t))
  simp only [neg_neg, pow_zero, one_mul] at eq
  simpa only [mul_neg, Real.cos_neg, Real.sin_neg, eq] using lt_of_lt_of_le (by norm_num) low.1

/-- The archived backward frame, a true physical point and its actual signed
velocity Jacobian satisfy the uniform quadratic bound on the entire first trial tube. -/
theorem physical_clock_log_norm {t : ℝ} {y : Plane} (ht : t ∈ Set.Icc 0 (1 / 64))
    (hu : trial.u.Mem (128 * t - 1) (y 0 - dkR0)) (hz : trial.z.Mem (128 * t - 1) (y 1))
    (w : Plane) :
    ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian 0 (-1) t y)
      (frameEquiv seed.frame row.frame (128 * t - 1)) (frameVelocity seed.frame row.frame) w⟫ ≤
      (logNorm : ℝ) * ‖w‖ ^ 2 := by
  obtain ⟨u,z⟩ := forward_inputs hu hz
  have hs : |128*t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd : affineDet firstLeft firstRight (128*t-1) ≠ 0 := by
    exact det_ne_zero ((Bool.and_eq_true_iff.mp DommaschkPhysicalFirstStep.checked).1) hs
  have left : seed.frame = reflectFrame firstLeft := rfl
  have right : row.frame = reflectFrame firstRight := rfl
  rw [left,right]
  have eq := moving_quadratic_eq t (128*t-1) firstLeft firstRight (flip y) (flip w) hd
  simp only [flip_twice] at eq
  rw [eq, velocityJacobian_spatial]
  simpa [logNorm] using DommaschkJacobian.physical_clock_log_norm ht u z (flip w)

end PlasmaLean.Design.DommaschkJacobianBackward000
