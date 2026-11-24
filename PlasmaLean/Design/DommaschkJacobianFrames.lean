/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobian
public import PlasmaLean.Certificates.PositionFrameODE

/-! # Frame and Taylor-model operations for the spatial Jacobian checker -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkBounceTaylor

open PlasmaLean.Certificates.TrajectoryTaylorModel

def Format.neg (f : Format) (x : Model) := f.mul (constant (-1)) x

theorem Format.neg_mem (f : Format) {x : Model} {t a : ℝ} (ht : |t| ≤ 1) (h : x.Mem t a) :
    (f.neg x).Mem t (-a) := by
  simpa [neg] using f.mul_mem ht (constant_mem (-1) t) h

def Format.sub (f : Format) (x y : Model) := f.add x (f.neg y)

theorem Format.sub_mem (f : Format) {x y : Model} {t a b : ℝ} (ht : |t| ≤ 1)
    (hx : x.Mem t a) (hy : y.Mem t b) : (f.sub x y).Mem t (a - b) := by
  simpa [sub, sub_eq_add_neg] using f.add_mem ht hx (f.neg_mem ht hy)

end PlasmaLean.Design.DommaschkBounceTaylor

namespace PlasmaLean.Design.DommaschkJacobian

open PlasmaLean.Certificates.PositionFrameSlabs DommaschkKam DommaschkKam.DkPoly

def format : DommaschkBounceTaylor.Format := ⟨7, 80⟩

/-- The Jacobian matrix uses the same four quotient-rule entries appearing in
the derivative of the field-line ODE in Euclidean coordinates. -/
noncomputable def spatialMatrix (u z c s : ℝ) : Plane →L[ℝ] Plane :=
  matrix (quotientEntry dnR dU u z c s) (quotientEntry dnR dZ u z c s)
    (quotientEntry dnZ dU u z c s) (quotientEntry dnZ dZ u z c s)

noncomputable def frameEntries (l r : Frame) (t : ℝ) : Entries :=
  ⟨entry l.a r.a t, entry l.b r.b t, entry l.c r.c t, entry l.d r.d t⟩

noncomputable def velocityEntries (l r : Frame) : Entries :=
  ((frameEntries l r 1).sub (frameEntries l r (-1))).scale 64


open scoped RealInnerProductSpace

/-- Interpret the spatial certificate in the Euclidean coordinate norm. -/
noncomputable def Entries.toCLM (m : Entries) : Plane →L[ℝ] Plane := matrix m.a m.b m.c m.d

private theorem velocity_toCLM (l r : Frame) :
    frameVelocity l r = (velocityEntries l r).toCLM := by
  ext x i
  fin_cases i <;>
    simp [frameVelocity, velocityEntries, frameEntries, Entries.toCLM, Entries.sub,
      Entries.scale, forward] <;> ring

/-- The scaled scalar quadratic form is precisely the Euclidean moving-frame
quadratic form used by the a posteriori trajectory theorem. -/
theorem conjugate_quad (j : Entries) (l r : Frame) (t denSq : ℝ)
    (hdet : affineDet l r t ≠ 0) (hd : denSq ≠ 0) (x : Plane) :
    ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian
      ((j.scale (1 / denSq)).toCLM) (frameEquiv l r t) (frameVelocity l r) x⟫ =
    (transformedNumerator j (frameEntries l r t) (velocityEntries l r) denSq).quad (x 0) (x 1) /
      ((frameEntries l r t).det * denSq) := by
  unfold Fields.LogNormTrajectory.MovingFrame.jacobian
  rw [frameEquiv_forward hdet, frameEquiv_backward hdet, velocity_toCLM]
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial, ContinuousLinearMap.comp_apply,
    sub_apply, backward, smul_apply, forward,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, matrix_zero, matrix_one, Entries.toCLM,
    Entries.scale, Entries.quad, transformedNumerator, Entries.product, Entries.sub,
    Entries.adj, frameEntries, Entries.det]
  unfold affineDet at hdet ⊢
  field_simp [hdet, hd]
  ring

/-- A reusable certificate for the actual quotient-rule matrix on any affine frame.
The four simultaneous real inequalities are supplied by the sparse Taylor packet. -/
theorem spatial_log_norm_of_bounds (l r : Frame) (t u z c s : ℝ)
    {dl tr di off disk mu : ℝ} (lower : 0 < dl) (hmu : 0 ≤ mu) (hr : 0 ≤ disk)
    (hsmall : di ^ 2 + off ^ 2 ≤ disk ^ 2) (hbudget : tr + disk ≤ 2 * dl * mu)
    (h :
      let m := frameEntries l r t
      let denSq := evR u z c s dD * evR u z c s dD
      let A := transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) denSq
      dl ≤ m.det * denSq ∧ A.a + A.d ≤ tr ∧ |A.a - A.d| ≤ di ∧ |A.b + A.c| ≤ off)
    (x : Plane) :
    ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian (spatialMatrix u z c s)
      (frameEquiv l r t) (frameVelocity l r) x⟫ ≤ mu * ‖x‖ ^ 2 := by
  let m := frameEntries l r t
  let D := evR u z c s dD * evR u z c s dD
  let A := transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) D
  obtain ⟨hd,htr,hv,hw⟩ := h
  change dl ≤ m.det * D at hd
  change A.a + A.d ≤ tr at htr
  change |A.a - A.d| ≤ di at hv
  change |A.b + A.c| ≤ off at hw
  have hdisk : (A.a - A.d)^2 + (A.b + A.c)^2 ≤ disk^2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hv 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs] at h1 h2
    exact (add_le_add h1 h2).trans hsmall
  have hp := lower.trans_le hd
  have cost : tr + disk ≤ 2 * (m.det * D) * mu := by
    nlinarith only [hbudget, mul_le_mul_of_nonneg_right hd hmu]
  have hform := quadratic_le_of_trace A hp htr hdisk hr cost (x 0) (x 1)
  obtain ⟨hm, hs⟩ := mul_ne_zero_iff.mp hp.ne'
  have hj : spatialMatrix u z c s = ((spatialNumerator u z c s).scale (1 / D)).toCLM := by
    unfold spatialMatrix Entries.toCLM Entries.scale spatialNumerator quotientEntry
    dsimp only [D]
    congr 1 <;> ring
  rw [hj, conjugate_quad _ _ _ _ _ hm hs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  exact hform

end PlasmaLean.Design.DommaschkJacobian
