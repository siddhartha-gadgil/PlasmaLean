/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianFrames

/-! # Lower bounds for the frame-reduced spatial Jacobian

The upper logarithmic-norm bound of `DommaschkJacobian` applied to the negated
entries gives the lower bound from the same disk and a lower bound on the trace.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkJacobianLower

open PlasmaLean.Design.DommaschkJacobian
open PlasmaLean.Certificates.PositionFrameSlabs DommaschkKam DommaschkKam.DkPoly
open scoped RealInnerProductSpace

/-- Entrywise negation of four matrix entries. -/
def neg (A : Entries) : Entries := ⟨-A.a, -A.b, -A.c, -A.d⟩

theorem neg_quad (A : Entries) (x y : ℝ) : (neg A).quad x y = -A.quad x y := by
  simp only [neg, Entries.quad]
  ring

/-- A lower bound on the trace and a disk enclosing the two independent traceless
entries bound the quadratic form from below. -/
theorem quadratic_ge_of_trace (A : Entries) {den traceRadius diskRadius mu : ℝ}
    (hd : 0 < den) (htrace : -(A.a + A.d) ≤ traceRadius)
    (hdisk : (A.a - A.d) ^ 2 + (A.b + A.c) ^ 2 ≤ diskRadius ^ 2)
    (hr : 0 ≤ diskRadius) (hmu : traceRadius + diskRadius ≤ 2 * den * mu) (x y : ℝ) :
    -(mu * (x^2+y^2)) ≤ A.quad x y / den := by
  have htrace' : (neg A).a + (neg A).d ≤ traceRadius := by
    simp only [neg]
    linarith only [htrace]
  have hdisk' : ((neg A).a - (neg A).d) ^ 2 + ((neg A).b + (neg A).c) ^ 2 ≤ diskRadius ^ 2 := by
    have e : (-A.a - -A.d) ^ 2 + (-A.b + -A.c) ^ 2 = (A.a - A.d) ^ 2 + (A.b + A.c) ^ 2 := by
      ring
    simpa only [neg, e] using hdisk
  have h := quadratic_le_of_trace (neg A) hd htrace' hdisk' hr hmu x y
  rw [neg_quad, neg_div] at h
  linarith only [h]

/-- The lower counterpart of `spatial_log_norm_of_bounds`: the same simultaneous
inequalities, with the trace bounded from below. -/
theorem spatial_log_norm_lower_of_bounds (l r : Frame) (t u z c s : ℝ)
    {dl tr di off disk mu : ℝ} (lower : 0 < dl) (hmu : 0 ≤ mu) (hr : 0 ≤ disk)
    (hsmall : di ^ 2 + off ^ 2 ≤ disk ^ 2) (hbudget : tr + disk ≤ 2 * dl * mu)
    (h :
      let m := frameEntries l r t
      let denSq := evR u z c s dD * evR u z c s dD
      let A := transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) denSq
      dl ≤ m.det * denSq ∧ -(A.a + A.d) ≤ tr ∧ |A.a - A.d| ≤ di ∧ |A.b + A.c| ≤ off)
    (x : Plane) :
    -(mu * ‖x‖ ^ 2) ≤ ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian (spatialMatrix u z c s)
      (frameEquiv l r t) (frameVelocity l r) x⟫ := by
  let m := frameEntries l r t
  let D := evR u z c s dD * evR u z c s dD
  let A := transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) D
  obtain ⟨hd,htr,hv,hw⟩ := h
  change dl ≤ m.det * D at hd
  change -(A.a + A.d) ≤ tr at htr
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
  have hform := quadratic_ge_of_trace A hp htr hdisk hr cost (x 0) (x 1)
  obtain ⟨hm, hs⟩ := mul_ne_zero_iff.mp hp.ne'
  have hj : spatialMatrix u z c s = ((spatialNumerator u z c s).scale (1 / D)).toCLM := by
    unfold spatialMatrix Entries.toCLM Entries.scale spatialNumerator quotientEntry
    dsimp only [D]
    congr 1 <;> ring
  rw [hj, conjugate_quad _ _ _ _ _ hm hs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  exact hform

/-- A two-sided trace bound gives a two-sided bound on the moving-frame quadratic form. -/
theorem spatial_log_norm_abs_of_bounds (l r : Frame) (t u z c s : ℝ)
    {dl tr di off disk mu : ℝ} (lower : 0 < dl) (hmu : 0 ≤ mu) (hr : 0 ≤ disk)
    (hsmall : di ^ 2 + off ^ 2 ≤ disk ^ 2) (hbudget : tr + disk ≤ 2 * dl * mu)
    (h :
      let m := frameEntries l r t
      let denSq := evR u z c s dD * evR u z c s dD
      let A := transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) denSq
      dl ≤ m.det * denSq ∧ |A.a + A.d| ≤ tr ∧ |A.a - A.d| ≤ di ∧ |A.b + A.c| ≤ off)
    (x : Plane) :
    |⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian (spatialMatrix u z c s)
      (frameEquiv l r t) (frameVelocity l r) x⟫| ≤ mu * ‖x‖ ^ 2 := by
  obtain ⟨hd,htr,hv,hw⟩ := h
  obtain ⟨lo,hi⟩ := abs_le.mp htr
  exact abs_le.mpr
    ⟨spatial_log_norm_lower_of_bounds l r t u z c s lower hmu hr hsmall hbudget
        ⟨hd, by linarith only [lo], hv, hw⟩ x,
      spatial_log_norm_of_bounds l r t u z c s lower hmu hr hsmall hbudget ⟨hd, hi, hv, hw⟩ x⟩

end PlasmaLean.Design.DommaschkJacobianLower
