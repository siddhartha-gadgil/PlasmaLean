/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianFirst

/-! # First forward slab logarithmic norm of the physical quotient Jacobian -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJacobian

open PlasmaLean.Certificates.PositionFrameSlabs DommaschkKam DommaschkKam.DkPoly
open DommaschkBounceTaylorFirst
open scoped RealInnerProductSpace

/-- The continuous, tube-wide logarithmic norm fits strictly below the
recorded first forward bound. All six sparse derivatives are evaluated on the
same full trial tube as the physical denominator and velocity numerators. -/
theorem first_log_norm {t u z c s : ℝ} (ht : |t| ≤ 1) (hin : trial.Mem t u z c s)
    (x : Plane) :
    ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian (spatialMatrix u z c s)
      (frameEquiv firstLeft firstRight t) (frameVelocity firstLeft firstRight) x⟫ ≤
      201/10000 * ‖x‖ ^ 2 := by
  let m := frameEntries firstLeft firstRight t
  let denSq := evR u z c s dD * evR u z c s dD
  let A := transformedNumerator (spatialNumerator u z c s) m
    (velocityEntries firstLeft firstRight) denSq
  obtain ⟨hd,htr,hv,hw⟩ := symmetric_bounds ht hin
  change 1017/1000 ≤ m.det * denSq at hd
  change A.a + A.d ≤ 943/1000000 at htr
  change |A.a - A.d| ≤ 39764/1000000 at hv
  change |A.b + A.c| ≤ 2884/1000000 at hw
  have hpos : 0 < m.det * denSq := by linarith only [hd]
  obtain ⟨hm,hs⟩ := mul_ne_zero_iff.mp hpos.ne'
  have hdisk : (A.a - A.d)^2 + (A.b + A.c)^2 ≤ (39870/1000000:ℝ)^2 := by
    have h1 : |A.a - A.d|^2 ≤ (39764/1000000:ℝ)^2 :=
      pow_le_pow_left₀ (abs_nonneg _) hv 2
    have h2 : |A.b + A.c|^2 ≤ (2884/1000000:ℝ)^2 :=
      pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs] at h1 h2
    linarith only [h1,h2]
  have hform := quadratic_le_of_trace A hpos htr hdisk (by norm_num)
    (mu := 201/10000) (by linarith only [hd]) (x 0) (x 1)
  have hj : spatialMatrix u z c s = ((spatialNumerator u z c s).scale (1 / denSq)).toCLM := by
    unfold spatialMatrix Entries.toCLM Entries.scale spatialNumerator quotientEntry
    dsimp only [denSq]
    congr 1 <;> ring
  rw [hj, conjugate_quad _ _ _ _ _ hm hs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  exact hform

/-- On the actual first forward clock, the two trial position memberships
supply every spatial and angular hypothesis needed for the logarithmic norm. -/
theorem physical_clock_log_norm {t R z : ℝ} (ht : t ∈ Set.Icc 0 (1 / 64))
    (hu : trial.u.Mem (128 * t - 1) (R - dkR0)) (hz : trial.z.Mem (128 * t - 1) z)
    (x : Plane) :
    ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian
      (spatialMatrix (R - dkR0) z (Real.cos (2*t)) (Real.sin (2*t)))
      (frameEquiv firstLeft firstRight (128*t-1)) (frameVelocity firstLeft firstRight) x⟫ ≤
      201/10000 * ‖x‖ ^ 2 := by
  have hs : |128*t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc : t ∈ Set.Icc (0/64:ℝ) (1/64) := by simpa using ht
  apply first_log_norm hs _ x
  refine ⟨hu, hz, ?_, ?_⟩
  · change (DommaschkHarmonicSlab0.model false 0 false).Mem _ _
    simpa [Certificates.TrajectoryTrig.wave] using DommaschkHarmonicSlab0.physical false 0 false hc
  · change (DommaschkHarmonicSlab0.model false 0 true).Mem _ _
    simpa [Certificates.TrajectoryTrig.wave] using DommaschkHarmonicSlab0.physical false 0 true hc

end PlasmaLean.Design.DommaschkJacobian
