/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianReflection
public import PlasmaLean.Design.DommaschkMirrorTubeCrossing

/-! # Signed field and moving-frame reflection at the two QA2R sections

The sparse field depends on the toroidal angle only through its second harmonic.
Reflection compares t ↦ α−t with t ↦ α+t at each section satisfying sin(2α)=0.
It applies to all physical points and does not require reflected numerical centres.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSymmetricSections

open DommaschkKam DommaschkKam.DkPoly DommaschkBounceField DommaschkSectionReflection
open DommaschkJacobian DommaschkJacobianReflection Certificates.PositionFrameSlabs Real
open scoped RealInnerProductSpace

/-- The symmetry axes of the phase harmonic. -/
def Axis (α : ℝ) : Prop := sin (2 * α) = 0

theorem zero_axis : Axis 0 := by simp [Axis]

theorem half_pi_axis : Axis (π / 2) := by
  unfold Axis
  rw [show 2 * (π / 2) = π by ring, sin_pi]

/-- The toroidal sine and cosine on the negative clock agree with those at the
reflected positive angle. -/
theorem clock {α : ℝ} (axis : Axis α) (t : ℝ) :
    cos (2 * (α - t)) = cos (2 * (-(α + t))) ∧
    sin (2 * (α - t)) = sin (2 * (-(α + t))) := by
  simp [mul_neg, mul_sub, mul_add, cos_sub, cos_add, sin_sub, sin_add, Axis] at axis ⊢
  simp [axis]
  constructor <;> ring

/-- Every sparse polynomial has identical values on these two negative clocks. -/
theorem negative_clock {α : ℝ} (axis : Axis α) (p : SP) (R z t : ℝ) :
    atPoint p R (α - t) z = atPoint p R (-(α + t)) z := by
  simp only [atPoint, (clock axis t).1, (clock axis t).2]

theorem denominator {α : ℝ} (axis : Axis α) (R z t : ℝ) :
    atPoint dD R (α - t) (-z) = atPoint dD R (α + t) z := by
  rw [negative_clock axis]
  simpa using atPoint_reflect (p := dD) (k := 0) (by kernel_fact) R (α + t) z

/-- Physical toroidal and vertical components are even and the radial component
is odd at every positive radius about either axis. -/
theorem cylindrical {α R : ℝ} (axis : Axis α) (hR : 0 < R) (z t : ℝ) :
    cylBphi R (α - t) (-z) = cylBphi R (α + t) z ∧
    cylBR R (α - t) (-z) = -cylBR R (α + t) z ∧
    cylBz R (α - t) (-z) = cylBz R (α + t) z := by
  obtain ⟨d,r,v⟩ := field_reflect hR (α + t) z
  obtain ⟨d₁,r₁,v₁⟩ := field_id hR (α - t) (-z)
  obtain ⟨d₂,r₂,v₂⟩ := field_id hR (-(α + t)) (-z)
  have de := negative_clock axis dD R (-z) t
  have re := negative_clock axis dnR R (-z) t
  have ve := negative_clock axis dnZ R (-z) t
  rw [d₁,d₂] at de
  rw [r₁,r₂] at re
  rw [v₁,v₂] at ve
  exact ⟨(mul_left_cancel₀ (pow_ne_zero 7 hR.ne') de).trans d,
    (mul_left_cancel₀ (pow_ne_zero 8 hR.ne') re).trans r,
    (mul_left_cancel₀ (pow_ne_zero 8 hR.ne') ve).trans v⟩

theorem strength {α : ℝ} (axis : Axis α) (t : ℝ) (x : Plane) (hR : 0 < x 0) :
    DommaschkMirrorTubeCrossing.strength (α - t) (flip x) =
      DommaschkMirrorTubeCrossing.strength (α + t) x := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  obtain ⟨d,r,v⟩ := cylindrical axis hR (x 1) t
  simp only [flip_zero, flip_one,
    DommaschkKamC.norm_field_sq, d, r, v, neg_sq]

theorem flow {α : ℝ} (axis : Axis α) (t : ℝ) (p : DommaschkBounceField.State) (hR : 0 < p 0) :
    physicalFlow α (-1) t (reflect p) = reflect (physicalFlow α 1 t p) := by
  obtain ⟨d,r,v⟩ := cylindrical axis hR (p 1) t
  funext i
  fin_cases i <;> simp [physicalFlow, reflect, ← sub_eq_add_neg, d, r, v, neg_div]

private theorem jacobian_clocks {α : ℝ} (axis : Axis α) (t : ℝ) (x : Plane) :
    velocityJacobian α (-1) t x = velocityJacobian 0 (-1) (α + t) x ∧
    velocityJacobian α 1 t x = velocityJacobian 0 1 (α + t) x := by
  simp only [velocityJacobian_spatial, neg_one_mul, zero_add, one_mul, ← sub_eq_add_neg,
    (clock axis t).1, (clock axis t).2, zero_sub, and_self]

/-- The full signed spatial derivative conjugates at arbitrary physical positions. -/
theorem jacobian {α : ℝ} (axis : Axis α) (t : ℝ) (x v : Plane) :
    velocityJacobian α (-1) t (flip x) (flip v) = flip (velocityJacobian α 1 t x v) := by
  rw [(jacobian_clocks axis t (flip x)).1, (jacobian_clocks axis t x).2]
  exact velocity_reflect (α + t) x v

/-- The affine moving-frame quadratic forms agree for the full conjugate
frames. This covers differing numerical centres at the same reflected point. -/
theorem quadratic {α : ℝ} (axis : Axis α) (t s : ℝ) (l r : Frame) (x v : Plane)
    (hd : affineDet l r s ≠ 0) :
    ⟪flip v, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian α (-1) t (flip x))
      (frameEquiv (reflectFrame l) (reflectFrame r) s)
      (frameVelocity (reflectFrame l) (reflectFrame r)) (flip v)⟫ =
    ⟪v, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian α 1 t x)
      (frameEquiv l r s) (frameVelocity l r) v⟫ := by
  rw [(jacobian_clocks axis t (flip x)).1, (jacobian_clocks axis t x).2]
  exact moving_quadratic_eq (α + t) s l r x v hd

/-- Transfer a certified positive-clock estimate on the reflected physical point
to every deviation on the negative clock, in the backward row's conjugate frame. -/
theorem quadratic_upper {α : ℝ} (axis : Axis α) {t s μ : ℝ} {l r : Frame} {x : Plane}
    (hd : affineDet l r s ≠ 0)
    (bound : ∀ w : Plane,
      ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
        (spatialMatrix (x 0 - dkR0) (-x 1) (cos (2 * (α + t))) (sin (2 * (α + t))))
        (frameEquiv l r s) (frameVelocity l r) w⟫ ≤ μ * ‖w‖ ^ 2)
    (w : Plane) :
    ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian α (-1) t x)
      (frameEquiv (reflectFrame l) (reflectFrame r) s)
      (frameVelocity (reflectFrame l) (reflectFrame r)) w⟫ ≤ μ * ‖w‖ ^ 2 := by
  have link := quadratic axis t s l r (flip x) (flip w) hd
  simp only [flip_twice] at link
  rw [link, velocityJacobian_spatial, one_smul, one_mul, flip_zero, flip_one]
  simpa only [flip_norm] using bound (flip w)

end PlasmaLean.Design.DommaschkSymmetricSections
