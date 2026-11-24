/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalJacobian
public import PlasmaLean.Design.DommaschkSectionReflection

/-! # Section-zero reflection of the full moving-frame spatial Jacobian

The reflection conjugates the signed velocity Jacobians, the frame, its inverse,
and its time derivative. The two Euclidean quadratic forms therefore agree
exactly at reflected physical points.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJacobianReflection

open DommaschkKam DommaschkKam.DkPoly DommaschkJacobian DommaschkSectionReflection
open Certificates.PositionFrameSlabs
open scoped RealInnerProductSpace

/-- Orthogonal reflection of a physical or deviation vector. -/
def flip : Plane →L[ℝ] Plane := matrix 1 0 0 (-1)

@[simp] theorem flip_zero (v : Plane) : flip v 0 = v 0 := by simp [flip]
@[simp] theorem flip_one (v : Plane) : flip v 1 = -v 1 := by simp [flip]
@[simp] theorem flip_twice (v : Plane) : flip (flip v) = v := by ext i; fin_cases i <;> simp

@[simp] theorem flip_inner (u v : Plane) : ⟪flip u, flip v⟫ = ⟪u,v⟫ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    flip_zero, flip_one, neg_mul_neg]

@[simp] theorem flip_norm (v : Plane) : ‖flip v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem pD : parity dD 0 = true := by kernel_fact
private theorem pR : parity dnR 1 = true := by kernel_fact
private theorem pZ : parity dnZ 0 = true := by kernel_fact
private theorem pDu : parity (dU dD) 0 = true := by kernel_fact
private theorem pDz : parity (dZ dD) 1 = true := by kernel_fact
private theorem pRu : parity (dU dnR) 1 = true := by kernel_fact
private theorem pRz : parity (dZ dnR) 0 = true := by kernel_fact
private theorem pZu : parity (dU dnZ) 0 = true := by kernel_fact
private theorem pZz : parity (dZ dnZ) 1 = true := by kernel_fact

/-- The signed derivative conjugacy holds for the exact candidate polynomials. -/
theorem velocity_reflect (t : ℝ) (x v : Plane) :
    velocityJacobian 0 (-1) t (flip x) (flip v) = flip (velocityJacobian 0 1 t x v) := by
  rw [velocityJacobian_spatial, velocityJacobian_spatial]
  ext i
  fin_cases i <;> simp [spatialMatrix, quotientEntry, quotientNumerator,
    evR_reflect pD, evR_reflect pR, evR_reflect pZ, evR_reflect pDu, evR_reflect pDz,
    evR_reflect pRu, evR_reflect pRz, evR_reflect pZu, evR_reflect pZz] <;> ring

def reflectFrame (m : Frame) : Frame := ⟨m.a, -m.b, -m.c, m.d⟩

private theorem entry_neg (a b : ℤ) (t : ℝ) : entry (-a) (-b) t = -entry a b t := by
  simp [entry]
  ring

@[simp] theorem reflected_det (l r : Frame) (t : ℝ) :
    affineDet (reflectFrame l) (reflectFrame r) t = affineDet l r t := by
  simp [affineDet, reflectFrame, entry_neg]

@[simp] theorem forward_reflect (l r : Frame) (t : ℝ) (v : Plane) :
    forward (reflectFrame l) (reflectFrame r) t (flip v) = flip (forward l r t v) := by
  ext i
  fin_cases i <;> simp [forward, reflectFrame, entry_neg]
  ring

@[simp] theorem backward_reflect (l r : Frame) (t : ℝ) (v : Plane) :
    backward (reflectFrame l) (reflectFrame r) t (flip v) = flip (backward l r t v) := by
  ext i
  fin_cases i <;> simp [backward, reflectFrame, entry_neg, affineDet]
  ring_nf
  simp

@[simp] theorem frame_rate_reflect (l r : Frame) (v : Plane) :
    frameVelocity (reflectFrame l) (reflectFrame r) (flip v) = flip (frameVelocity l r v) := by
  simp [frameVelocity]

/-- At any matching pair of absolute-clock points the backward moving-frame
quadratic form equals its forward value on the reflected deviation. -/
theorem moving_quadratic_eq (t s : ℝ) (l r : Frame) (x v : Plane) (hd : affineDet l r s ≠ 0) :
    ⟪flip v, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian 0 (-1) t (flip x))
      (frameEquiv (reflectFrame l) (reflectFrame r) s)
      (frameVelocity (reflectFrame l) (reflectFrame r)) (flip v)⟫ =
    ⟪v, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian 0 1 t x)
      (frameEquiv l r s) (frameVelocity l r) v⟫ := by
  have hb : affineDet (reflectFrame l) (reflectFrame r) s ≠ 0 := by simpa using hd
  unfold Fields.LogNormTrajectory.MovingFrame.jacobian
  rw [frameEquiv_forward hb, frameEquiv_backward hb, frameEquiv_forward hd, frameEquiv_backward hd]
  simp only [ContinuousLinearMap.comp_apply, sub_apply, forward_reflect, velocity_reflect,
    frame_rate_reflect, ← map_sub, backward_reflect, flip_inner]

end PlasmaLean.Design.DommaschkJacobianReflection
