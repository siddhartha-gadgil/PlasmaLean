/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalJacobian
public import PlasmaLean.Design.DommaschkJacobianLower
public import PlasmaLean.Theory.Fields.FrameJacobianVariation

/-!
# Spatial derivative of the field-line velocity Jacobian

Each entry of the spatial Jacobian is a quotient `N / D²` with
`N = n_x D - n D_x`. Its partial derivative in a second position coordinate `y` is
`(N_y D - 2 N D_y) / D³` with `N_y = n_xy D + n_x D_y - n_y D_x - n D_xy`. The
formal derivatives of the sparse polynomials give these as real derivatives, and
the four entries assemble into the Fréchet derivative of the velocity Jacobian in
position. The mean value bound of `FrameJacobianVariation` is then specialized to
this field.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJacobianSecond

open DommaschkKam DkPoly DommaschkBounceField
open PlasmaLean.Design.DommaschkJacobian
open PlasmaLean.Certificates.PositionFrameSlabs
open scoped RealInnerProductSpace

/-- The partial derivative `N_y = n_xy D + n_x D_y - n_y D_x - n D_xy` of the quotient
numerator `N = n_x D - n D_x`; `der` is the formal `∂_x` and `der'` the formal `∂_y`. -/
def numeratorPartial (n : SP) (der der' : SP → SP) (u z c s : ℝ) : ℝ :=
  evR u z c s (der' (der n)) * evR u z c s dD + evR u z c s (der n) * evR u z c s (der' dD) -
    evR u z c s (der' n) * evR u z c s (der dD) - evR u z c s n * evR u z c s (der' (der dD))

/-- Numerator `N_y D - 2 N D_y` of the second partial derivative of a field-line velocity,
over the denominator `D³`. -/
def secondNumerator (n : SP) (der der' : SP → SP) (u z c s : ℝ) : ℝ :=
  numeratorPartial n der der' u z c s * evR u z c s dD -
    2 * quotientNumerator n der u z c s * evR u z c s (der' dD)

/-- The partial derivative in the `der'` coordinate of the Jacobian entry
`quotientEntry n der`. -/
def secondEntry (n : SP) (der der' : SP → SP) (u z c s : ℝ) : ℝ :=
  secondNumerator n der der' u z c s / evR u z c s dD ^ 3

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quotient numerator is differentiable along arbitrary differentiable input
coordinates, with the formal partial derivatives as coefficients. -/
theorem numerator_derivative (n : SP) (der : SP → SP) {u z : E → ℝ} {U Z : E →L[ℝ] ℝ} {x : E}
    (hu : HasFDerivAt u U x) (hz : HasFDerivAt z Z x) (c s : ℝ) :
    HasFDerivAt (fun y => quotientNumerator n der (u y) (z y) c s)
      (numeratorPartial n der dU (u x) (z x) c s • U +
        numeratorPartial n der dZ (u x) (z x) c s • Z) x := by
  have h := ((sparse_derivative (der n) hu hz c s).mul (sparse_derivative dD hu hz c s)).sub
    ((sparse_derivative n hu hz c s).mul (sparse_derivative (der dD) hu hz c s))
  unfold quotientNumerator
  apply h.congr_fderiv
  ext y
  simp only [numeratorPartial, add_apply, sub_apply,
    smul_apply, smul_eq_mul]
  ring

/-- Each quotient-rule Jacobian entry is differentiable along arbitrary differentiable
input coordinates wherever the field denominator does not vanish. -/
theorem entry_derivative (n : SP) (der : SP → SP) {u z : E → ℝ} {U Z : E →L[ℝ] ℝ} {x : E}
    (hu : HasFDerivAt u U x) (hz : HasFDerivAt z Z x) (c s : ℝ)
    (hd : evR (u x) (z x) c s dD ≠ 0) :
    HasFDerivAt (fun y => quotientEntry n der (u y) (z y) c s)
      (secondEntry n der dU (u x) (z x) c s • U + secondEntry n der dZ (u x) (z x) c s • Z)
      x := by
  have hN := numerator_derivative n der hu hz c s
  have hD := sparse_derivative dD hu hz c s
  have hi := (hasDerivAt_inv (mul_ne_zero hd hd)).comp_hasFDerivAt x (hD.mul hD)
  have h := hN.mul hi
  unfold quotientEntry
  simp only [div_eq_mul_inv]
  apply h.congr_fderiv
  ext y
  simp only [secondEntry, secondNumerator, add_apply, smul_apply,
    smul_eq_mul, Function.comp_apply, Pi.mul_apply]
  field_simp [hd]
  ring

end General

/-- Scalar form in the shifted radius: `∂_u` of a Jacobian entry. -/
theorem hasDerivAt_quotientEntry_u (n : SP) (der : SP → SP) (u z c s : ℝ)
    (hd : evR u z c s dD ≠ 0) :
    HasDerivAt (fun u' => quotientEntry n der u' z c s) (secondEntry n der dU u z c s) u := by
  have h := (entry_derivative n der (hasFDerivAt_id u) (hasFDerivAt_const z u) c s hd).hasDerivAt
  simpa using h

/-- Scalar form in the height: `∂_z` of a Jacobian entry. -/
theorem hasDerivAt_quotientEntry_z (n : SP) (der : SP → SP) (u z c s : ℝ)
    (hd : evR u z c s dD ≠ 0) :
    HasDerivAt (fun z' => quotientEntry n der u z' c s) (secondEntry n der dZ u z c s) z := by
  have h := (entry_derivative n der (hasFDerivAt_const u z) (hasFDerivAt_id z) c s hd).hasDerivAt
  simpa using h

/-- Sanity check: the two orders of the mixed second derivative of a velocity component
agree as soon as the formal mixed derivatives of the polynomials have equal values. -/
theorem secondEntry_symm (n : SP) (u z c s : ℝ)
    (hn : evR u z c s (dZ (dU n)) = evR u z c s (dU (dZ n)))
    (hD : evR u z c s (dZ (dU dD)) = evR u z c s (dU (dZ dD))) :
    secondEntry n dU dZ u z c s = secondEntry n dZ dU u z c s := by
  simp only [secondEntry, secondNumerator, numeratorPartial, quotientNumerator, hn, hD]
  ring

/-- Gradient in position of one Jacobian entry, in the radius/height basis. -/
def entryGradient (n : SP) (der : SP → SP) (u z c s : ℝ) : PhysicalPlane →L[ℝ] ℝ :=
  secondEntry n der dU u z c s • proj 0 + secondEntry n der dZ u z c s • proj 1

/-- Derivative in position of one row of the velocity Jacobian. -/
def rowHessian (n : SP) (phase sign t : ℝ) (x : PhysicalPlane) :
    PhysicalPlane →L[ℝ] PhysicalPlane →L[ℝ] ℝ :=
  let φ := phase + sign * t
  let grad := fun der =>
    entryGradient n der (x 0 - dkR0) (x 1) (Real.cos (2 * φ)) (Real.sin (2 * φ))
  sign • ((grad dU).smulRight (proj 0) + (grad dZ).smulRight (proj 1))

/-- A row placed in coordinate `i` of the plane, as a continuous linear map of the row. -/
def embedRow (i : Fin 2) : (PhysicalPlane →L[ℝ] ℝ) →L[ℝ] PhysicalPlane →L[ℝ] PhysicalPlane :=
  (ContinuousLinearMap.smulRightL ℝ PhysicalPlane PhysicalPlane).flip
    (EuclideanSpace.single i (1 : ℝ))

/-- The derivative in position of the velocity Jacobian. -/
def velocityHessian (phase sign t : ℝ) (x : PhysicalPlane) :
    PhysicalPlane →L[ℝ] PhysicalPlane →L[ℝ] PhysicalPlane :=
  (embedRow 0).comp (rowHessian dnR phase sign t x) +
    (embedRow 1).comp (rowHessian dnZ phase sign t x)

/-- The velocity Jacobian is the sum of its two embedded rows. -/
theorem velocityJacobian_rows (phase sign t : ℝ) (x : PhysicalPlane) :
    velocityJacobian phase sign t x =
      embedRow 0 (velocityRow dnR phase sign t x) +
        embedRow 1 (velocityRow dnZ phase sign t x) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;> simp [velocityJacobian, embedRow, coordinates]

/-- Each row of the velocity Jacobian is differentiable in position where the field
denominator does not vanish. -/
theorem row_derivative (n : SP) (phase sign t : ℝ) (x : PhysicalPlane)
    (hd : atPoint dD (x 0) (phase + sign * t) (x 1) ≠ 0) :
    HasFDerivAt (fun y => velocityRow n phase sign t y) (rowHessian n phase sign t x) x := by
  have hu : HasFDerivAt (fun y : PhysicalPlane => y 0 - dkR0) (proj 0) x :=
    (proj 0).hasFDerivAt.sub_const dkR0
  have hz : HasFDerivAt (fun y : PhysicalPlane => y 1) (proj 1) x := (proj 1).hasFDerivAt
  have e (der : SP → SP) := entry_derivative n der hu hz (Real.cos (2 * (phase + sign * t)))
    (Real.sin (2 * (phase + sign * t))) hd
  exact (((e dU).smul_const (proj 0)).add ((e dZ).smul_const (proj 1))).const_smul sign

/-- With nonzero field denominator, the velocity Jacobian is Fréchet differentiable in
position with derivative `velocityHessian`. -/
theorem jacobian_derivative (phase sign t : ℝ) (x : PhysicalPlane)
    (hd : atPoint dD (x 0) (phase + sign * t) (x 1) ≠ 0) :
    HasFDerivAt (fun y => velocityJacobian phase sign t y) (velocityHessian phase sign t x) x := by
  have h := ((embedRow 0).hasFDerivAt.comp x (row_derivative dnR phase sign t x hd)).add
    ((embedRow 1).hasFDerivAt.comp x (row_derivative dnZ phase sign t x hd))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => velocityJacobian_rows phase sign t y)

/-- Radial component of the second derivative of the velocity in two directions. -/
theorem velocityHessian_apply_zero (phase sign t : ℝ) (x v w : PhysicalPlane) :
    let φ := phase + sign * t
    let S := fun der der' =>
      secondEntry dnR der der' (x 0 - dkR0) (x 1) (Real.cos (2 * φ)) (Real.sin (2 * φ))
    velocityHessian phase sign t x v w 0 =
      sign * ((S dU dU * v 0 + S dU dZ * v 1) * w 0 + (S dZ dU * v 0 + S dZ dZ * v 1) * w 1) := by
  simp [velocityHessian, embedRow, rowHessian, entryGradient, proj]
  ring

/-- Vertical component of the second derivative of the velocity in two directions. -/
theorem velocityHessian_apply_one (phase sign t : ℝ) (x v w : PhysicalPlane) :
    let φ := phase + sign * t
    let S := fun der der' =>
      secondEntry dnZ der der' (x 0 - dkR0) (x 1) (Real.cos (2 * φ)) (Real.sin (2 * φ))
    velocityHessian phase sign t x v w 1 =
      sign * ((S dU dU * v 0 + S dU dZ * v 1) * w 0 + (S dZ dU * v 0 + S dZ dZ * v 1) * w 1) := by
  simp [velocityHessian, embedRow, rowHessian, entryGradient, proj]
  ring

open PlasmaLean.Fields.LogNormTrajectory in
/-- Mean value bridge for this field: a two-sided bound at the reference point and
bounds on the frame-conjugated second derivative in the two frame directions over a
convex position set give a two-sided bound at every displaced point of the set. -/
theorem abs_quad_le_of_center (phase sign t : ℝ) {T : Set PhysicalPlane}
    {ref v w : PhysicalPlane} {M : PhysicalPlane ≃L[ℝ] PhysicalPlane} {g₀ g₁ μ₀ ρ : ℝ}
    (dM : PhysicalPlane →L[ℝ] PhysicalPlane) (hT : Convex ℝ T)
    (reg : ∀ ζ ∈ T, atPoint dD (ζ 0) (phase + sign * t) (ζ 1) ≠ 0)
    (h₀ : ∀ ζ ∈ T, |⟪w, M.symm ((velocityHessian phase sign t ζ
      (M (EuclideanSpace.single 0 1))) (M w))⟫| ≤ g₀ * ‖w‖ ^ 2)
    (h₁ : ∀ ζ ∈ T, |⟪w, M.symm ((velocityHessian phase sign t ζ
      (M (EuclideanSpace.single 1 1))) (M w))⟫| ≤ g₁ * ‖w‖ ^ 2)
    (hz : ref ∈ T) (hv : ref + M v ∈ T) (hρ : ‖v‖ ≤ ρ)
    (hc : |⟪w, MovingFrame.jacobian (velocityJacobian phase sign t ref) M dM w⟫| ≤
      μ₀ * ‖w‖ ^ 2) :
    |⟪w, MovingFrame.jacobian (velocityJacobian phase sign t (ref + M v)) M dM w⟫| ≤
      (μ₀ + Real.sqrt (g₀ ^ 2 + g₁ ^ 2) * ρ) * ‖w‖ ^ 2 :=
  Fields.FrameJacobianVariation.abs_quad_le_of_center
    (J := fun y => velocityJacobian phase sign t y) (DJ := velocityHessian phase sign t)
    dM hT (fun ζ hζ => jacobian_derivative phase sign t ζ (reg ζ hζ))
    (Fields.FrameJacobianVariation.directional_bound_of_basis h₀ h₁) hz hv
    (Real.sqrt_nonneg _) hρ hc

open PlasmaLean.Fields.LogNormTrajectory in
/-- The bridge for the forward field on an affine certificate frame, with the central
bound supplied by the two-sided trace and disk inequalities at the reference point. -/
theorem abs_quad_le_of_central_bounds (phase t : ℝ) (l r : Frame) (τ : ℝ)
    {T : Set PhysicalPlane} {ref v w : PhysicalPlane} {g₀ g₁ ρ dl tr di off disk mu : ℝ}
    (hT : Convex ℝ T)
    (reg : ∀ ζ ∈ T, atPoint dD (ζ 0) (phase + 1 * t) (ζ 1) ≠ 0)
    (h₀ : ∀ ζ ∈ T, |⟪w, (frameEquiv l r τ).symm ((velocityHessian phase 1 t ζ
      (frameEquiv l r τ (EuclideanSpace.single 0 1))) (frameEquiv l r τ w))⟫| ≤ g₀ * ‖w‖ ^ 2)
    (h₁ : ∀ ζ ∈ T, |⟪w, (frameEquiv l r τ).symm ((velocityHessian phase 1 t ζ
      (frameEquiv l r τ (EuclideanSpace.single 1 1))) (frameEquiv l r τ w))⟫| ≤ g₁ * ‖w‖ ^ 2)
    (hz : ref ∈ T) (hv : ref + frameEquiv l r τ v ∈ T) (hρ : ‖v‖ ≤ ρ)
    (lower : 0 < dl) (hmu : 0 ≤ mu) (hr : 0 ≤ disk)
    (hsmall : di ^ 2 + off ^ 2 ≤ disk ^ 2) (hbudget : tr + disk ≤ 2 * dl * mu)
    (h :
      let u := ref 0 - dkR0
      let z := ref 1
      let c := Real.cos (2 * (phase + 1 * t))
      let s := Real.sin (2 * (phase + 1 * t))
      let m := frameEntries l r τ
      let denSq := evR u z c s dD * evR u z c s dD
      let A := transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) denSq
      dl ≤ m.det * denSq ∧ |A.a + A.d| ≤ tr ∧ |A.a - A.d| ≤ di ∧ |A.b + A.c| ≤ off) :
    |⟪w, MovingFrame.jacobian (velocityJacobian phase 1 t (ref + frameEquiv l r τ v))
      (frameEquiv l r τ) (frameVelocity l r) w⟫| ≤
      (mu + Real.sqrt (g₀ ^ 2 + g₁ ^ 2) * ρ) * ‖w‖ ^ 2 := by
  apply abs_quad_le_of_center phase 1 t (frameVelocity l r) hT reg h₀ h₁ hz hv hρ
  rw [velocityJacobian_spatial, one_smul]
  exact DommaschkJacobianLower.spatial_log_norm_abs_of_bounds l r τ _ _ _ _ lower hmu hr hsmall
    hbudget h w

end PlasmaLean.Design.DommaschkJacobianSecond
