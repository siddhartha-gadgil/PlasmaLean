/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianSecond

/-!
# Frame-conjugated second derivatives of the QA2R field-line velocity from jets

A wide-tube certificate encloses the values of the three field polynomials and of
their formal derivatives up to order two (a `Jet` each). This file writes the
numerators of the second derivatives of the velocity as explicit sums of products of
those eighteen values, conjugates them by an affine certificate frame, and proves
that trace and disk bounds on the conjugated numerators give the two directional
hypotheses of `DommaschkJacobianSecond.abs_quad_le_of_center`.

The expressions are written as nested multiply-adds `a * x + q`, the operation that
one certified Taylor-model step encloses, so that a generated proof matches them
term by term.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkWideTubeHessian

open DommaschkKam DkPoly DommaschkBounceField
open PlasmaLean.Design.DommaschkJacobian PlasmaLean.Design.DommaschkJacobianSecond
open PlasmaLean.Certificates.PositionFrameSlabs
open scoped RealInnerProductSpace

/-- The two formal first derivatives commute on every sparse polynomial. -/
theorem dU_dZ (p : SP) : dU (dZ p) = dZ (dU p) := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    have hm : dU (Tm.dZ m) = dZ (Tm.dU m) := by
      cases ha : m.a <;> cases hb : m.b <;>
        simp [dU, dZ, Tm.dU, Tm.dZ, ha, hb, mul_right_comm]
    have e1 : dU (dZ (m :: p)) = dU (Tm.dZ m) ++ dU (dZ p) := by
      simp [dU, dZ, List.flatMap_cons, List.flatMap_append]
    have e2 : dZ (dU (m :: p)) = dZ (Tm.dU m) ++ dZ (dU p) := by
      simp [dU, dZ, List.flatMap_cons, List.flatMap_append]
    rw [e1, e2, hm, ih]

/-- Values of a sparse polynomial and of its formal derivatives up to order two. -/
structure Jet where
  /-- The value. -/
  v : ℝ
  /-- The radial derivative. -/
  u : ℝ
  /-- The vertical derivative. -/
  z : ℝ
  /-- The second radial derivative. -/
  uu : ℝ
  /-- The mixed derivative, radial first. -/
  uz : ℝ
  /-- The second vertical derivative. -/
  zz : ℝ

/-- The jet of a sparse polynomial at a point. -/
def jet (p : SP) (u z c s : ℝ) : Jet :=
  ⟨evR u z c s p, evR u z c s (dU p), evR u z c s (dZ p), evR u z c s (dU (dU p)),
    evR u z c s (dZ (dU p)), evR u z c s (dZ (dZ p))⟩

/-- Quotient numerator `N_u D - N D_u`. -/
def firstU (N D : Jet) : ℝ := N.u * D.v + N.v * -D.u

/-- Quotient numerator `N_z D - N D_z`. -/
def firstZ (N D : Jet) : ℝ := N.z * D.v + N.v * -D.z

/-- Radial derivative of `firstU`. -/
def partUU (N D : Jet) : ℝ := N.uu * D.v + N.v * -D.uu

/-- Vertical derivative of `firstU`. -/
def partUZ (N D : Jet) : ℝ := N.uz * D.v + (N.u * D.z + (N.z * -D.u + N.v * -D.uz))

/-- Radial derivative of `firstZ`. -/
def partZU (N D : Jet) : ℝ := N.uz * D.v + (N.z * D.u + (N.u * -D.z + N.v * -D.uz))

/-- Vertical derivative of `firstZ`. -/
def partZZ (N D : Jet) : ℝ := N.zz * D.v + N.v * -D.zz

/-- Numerator over `D³` of `∂_u ∂_u (N / D)`. -/
def secUU (N D : Jet) : ℝ := partUU N D * D.v + (firstU N D + firstU N D) * -D.u

/-- Numerator over `D³` of `∂_z ∂_u (N / D)`. -/
def secUZ (N D : Jet) : ℝ := partUZ N D * D.v + (firstU N D + firstU N D) * -D.z

/-- Numerator over `D³` of `∂_u ∂_z (N / D)`. -/
def secZU (N D : Jet) : ℝ := partZU N D * D.v + (firstZ N D + firstZ N D) * -D.u

/-- Numerator over `D³` of `∂_z ∂_z (N / D)`. -/
def secZZ (N D : Jet) : ℝ := partZZ N D * D.v + (firstZ N D + firstZ N D) * -D.z

/-- `secUU` is the numerator of `secondEntry n dU dU`. -/
theorem secUU_eq (n : SP) (u z c s : ℝ) :
    secUU (jet n u z c s) (jet dD u z c s) = secondNumerator n dU dU u z c s := by
  simp only [secUU, partUU, firstU, jet, secondNumerator, numeratorPartial, quotientNumerator]
  ring

/-- `secUZ` is the numerator of `secondEntry n dU dZ`. -/
theorem secUZ_eq (n : SP) (u z c s : ℝ) :
    secUZ (jet n u z c s) (jet dD u z c s) = secondNumerator n dU dZ u z c s := by
  simp only [secUZ, partUZ, firstU, jet, secondNumerator, numeratorPartial, quotientNumerator]
  ring

/-- `secZU` is the numerator of `secondEntry n dZ dU`; the mixed formal derivatives
commute by `dU_dZ`. -/
theorem secZU_eq (n : SP) (u z c s : ℝ) :
    secZU (jet n u z c s) (jet dD u z c s) = secondNumerator n dZ dU u z c s := by
  simp only [secZU, partZU, firstZ, jet, secondNumerator, numeratorPartial, quotientNumerator,
    dU_dZ]
  ring

/-- `secZZ` is the numerator of `secondEntry n dZ dZ`. -/
theorem secZZ_eq (n : SP) (u z c s : ℝ) :
    secZZ (jet n u z c s) (jet dD u z c s) = secondNumerator n dZ dZ u z c s := by
  simp only [secZZ, partZZ, firstZ, jet, secondNumerator, numeratorPartial, quotientNumerator]
  ring

/-- Sanity check: a numerator proportional to the denominator gives a constant velocity,
so all four second-derivative numerators vanish. -/
theorem sec_eq_zero_of_proportional (D : Jet) (k : ℝ) :
    let N : Jet := ⟨k * D.v, k * D.u, k * D.z, k * D.uu, k * D.uz, k * D.zz⟩
    secUU N D = 0 ∧ secUZ N D = 0 ∧ secZU N D = 0 ∧ secZZ N D = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [secUU, secUZ, secZU, secZZ, partUU, partUZ, partZU, partZZ, firstU, firstZ] <;>
    ring

/-- Sanity check on a concrete jet: for `N = u` and `D = 1 + u` at `u = 1`, the velocity
`u / (1 + u)` has second derivative `-2 / (1 + u)³`, numerator `-2`. -/
theorem secUU_example : secUU ⟨1, 1, 0, 0, 0, 0⟩ ⟨2, 1, 0, 0, 0, 0⟩ = -2 := by
  norm_num [secUU, partUU, firstU]

/-- Numerators over `D³` of the derivative of the spatial Jacobian in the position
direction `(p, q)`, from the jets of the radial and vertical numerators and of the
denominator. -/
def direction (R Z D : Jet) (p q : ℝ) : Entries :=
  ⟨secUU R D * p + secUZ R D * q, secZU R D * p + secZZ R D * q,
    secUU Z D * p + secUZ Z D * q, secZU Z D * p + secZZ Z D * q⟩

/-- Numerator of `M⁻¹ j M`, with denominator `det M`. -/
def conjugated (j m : Entries) : Entries := m.adj.product (j.product m)

private theorem row_eq (N D : Jet) (hD : D.v ≠ 0) (p q x y : ℝ) :
    1 * ((secUU N D / D.v ^ 3 * p + secUZ N D / D.v ^ 3 * q) * x +
      (secZU N D / D.v ^ 3 * p + secZZ N D / D.v ^ 3 * q) * y) =
    1 / (D.v * D.v * D.v) * (secUU N D * p + secUZ N D * q) * x +
      1 / (D.v * D.v * D.v) * (secZU N D * p + secZZ N D * q) * y := by
  field_simp

/-- Sanity check: conjugation by the identity frame changes nothing. -/
theorem conjugated_one (j : Entries) : conjugated j ⟨1, 0, 0, 1⟩ = j := by
  cases j
  simp [conjugated, Entries.product, Entries.adj]

/-- The second derivative of the velocity in a position direction is the matrix of
`direction` divided by the cube of the field denominator. -/
theorem velocityHessian_eq (phase t : ℝ) (ζ v : PhysicalPlane)
    (hd : atPoint dD (ζ 0) (phase + 1 * t) (ζ 1) ≠ 0) :
    let u := ζ 0 - dkR0
    let z := ζ 1
    let c := Real.cos (2 * (phase + 1 * t))
    let s := Real.sin (2 * (phase + 1 * t))
    let D := jet dD u z c s
    velocityHessian phase 1 t ζ v =
      ((direction (jet dnR u z c s) (jet dnZ u z c s) D (v 0) (v 1)).scale
        (1 / (D.v * D.v * D.v))).toCLM := by
  intro u z c s D
  have hD : D.v ≠ 0 := hd
  apply ContinuousLinearMap.ext
  intro w
  ext i
  fin_cases i
  · have h := velocityHessian_apply_zero phase 1 t ζ v w
    simp only [Fin.zero_eta, Fin.isValue] at h ⊢
    rw [h]
    simp only [Entries.toCLM, Entries.scale, direction, matrix_zero, secondEntry, ← secUU_eq,
      ← secUZ_eq, ← secZU_eq, ← secZZ_eq]
    exact row_eq (jet dnR u z c s) D hD (v 0) (v 1) (w 0) (w 1)
  · have h := velocityHessian_apply_one phase 1 t ζ v w
    simp only [Fin.mk_one, Fin.isValue] at h ⊢
    rw [h]
    simp only [Entries.toCLM, Entries.scale, direction, matrix_one, secondEntry, ← secUU_eq,
      ← secUZ_eq, ← secZU_eq, ← secZZ_eq]
    exact row_eq (jet dnZ u z c s) D hD (v 0) (v 1) (w 0) (w 1)

/-- The quadratic form of a scaled matrix conjugated by an affine certificate frame,
over the common denominator. -/
theorem conjugated_quad (j : Entries) (l r : Frame) (τ den : ℝ)
    (hdet : affineDet l r τ ≠ 0) (hd : den ≠ 0) (x : Plane) :
    ⟪x, (frameEquiv l r τ).symm ((j.scale (1 / den)).toCLM (frameEquiv l r τ x))⟫ =
      (conjugated j (frameEntries l r τ)).quad (x 0) (x 1) /
        ((frameEntries l r τ).det * den) := by
  change ⟪x, (frameEquiv l r τ).symm.toContinuousLinearMap ((j.scale (1 / den)).toCLM
    ((frameEquiv l r τ).toContinuousLinearMap x))⟫ = _
  rw [frameEquiv_forward hdet, frameEquiv_backward hdet]
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial, backward, smul_apply, forward,
    PiLp.smul_apply, smul_eq_mul, matrix_zero, matrix_one, Entries.toCLM,
    Entries.scale, Entries.quad, conjugated, Entries.product, Entries.adj, frameEntries,
    Entries.det]
  unfold affineDet at hdet ⊢
  field_simp [hdet, hd]
  ring

/-- A two-sided trace bound and a disk for the traceless part bound the quadratic
form on both sides. -/
theorem abs_quad_le_of_trace (A : Entries) {den tr disk g : ℝ} (hd : 0 < den)
    (htrace : |A.a + A.d| ≤ tr) (hdisk : (A.a - A.d) ^ 2 + (A.b + A.c) ^ 2 ≤ disk ^ 2)
    (hr : 0 ≤ disk) (hg : tr + disk ≤ 2 * den * g) (x y : ℝ) :
    |A.quad x y / den| ≤ g * (x ^ 2 + y ^ 2) := by
  obtain ⟨lo, hi⟩ := abs_le.mp htrace
  exact abs_le.mpr
    ⟨DommaschkJacobianLower.quadratic_ge_of_trace A hd (by linarith only [lo]) hdisk hr hg x y,
      quadratic_le_of_trace A hd hi hdisk hr hg x y⟩

/-- The inequalities a certificate supplies for one conjugated numerator. -/
def DirectionBounds (A : Entries) (tr di off : ℝ) : Prop :=
  |A.a + A.d| ≤ tr ∧ |A.a - A.d| ≤ di ∧ |A.b + A.c| ≤ off

/-- The inequalities a certificate supplies at one point of the tube: a lower bound for
the common denominator and the bounds for the two frame directions. -/
def TubeBounds (m : Entries) (R Z D : Jet) (dl tr₀ di₀ off₀ tr₁ di₁ off₁ : ℝ) : Prop :=
  dl ≤ m.det * (D.v * D.v * D.v) ∧
    DirectionBounds (conjugated (direction R Z D m.a m.c) m) tr₀ di₀ off₀ ∧
    DirectionBounds (conjugated (direction R Z D m.b m.d) m) tr₁ di₁ off₁

/-- Accepted fixture: the zero numerator with denominator one satisfies the bounds zero. -/
theorem tubeBounds_zero :
    TubeBounds ⟨1, 0, 0, 1⟩ ⟨0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0, 0, 0, 0⟩ ⟨1, 0, 0, 0, 0, 0⟩
      1 0 0 0 0 0 0 := by
  simp [TubeBounds, DirectionBounds, conjugated, direction, secUU, secUZ, secZU, secZZ,
    partUU, partUZ, partZU, partZZ, firstU, firstZ, Entries.product, Entries.adj, Entries.det]

/-- Rejected fixture: a claimed lower bound above the true denominator fails. -/
theorem not_tubeBounds_denominator :
    ¬ TubeBounds ⟨1, 0, 0, 1⟩ ⟨0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0, 0, 0, 0⟩ ⟨1, 0, 0, 0, 0, 0⟩
      2 0 0 0 0 0 0 := by
  intro h
  have h1 := h.1
  norm_num [Entries.det] at h1

/-- Trace and disk bounds for the conjugated numerator of a position direction bound
the frame-conjugated quadratic form of the second derivative of the velocity. -/
theorem abs_hessian_quad_le (phase t : ℝ) (l r : Frame) (τ : ℝ) (ζ v w : Plane)
    {dl tr di off disk g : ℝ} (lower : 0 < dl) (hg : 0 ≤ g)
    (hr : 0 ≤ disk) (hsmall : di ^ 2 + off ^ 2 ≤ disk ^ 2) (hbudget : tr + disk ≤ 2 * dl * g)
    (h :
      let u := ζ 0 - dkR0
      let z := ζ 1
      let c := Real.cos (2 * (phase + 1 * t))
      let s := Real.sin (2 * (phase + 1 * t))
      let m := frameEntries l r τ
      let D := jet dD u z c s
      dl ≤ m.det * (D.v * D.v * D.v) ∧
        DirectionBounds (conjugated
          (direction (jet dnR u z c s) (jet dnZ u z c s) D (v 0) (v 1)) m) tr di off) :
    |⟪w, (frameEquiv l r τ).symm ((velocityHessian phase 1 t ζ v) (frameEquiv l r τ w))⟫| ≤
      g * ‖w‖ ^ 2 := by
  let u := ζ 0 - dkR0
  let z := ζ 1
  let c := Real.cos (2 * (phase + 1 * t))
  let s := Real.sin (2 * (phase + 1 * t))
  let m := frameEntries l r τ
  let D := jet dD u z c s
  let A := conjugated (direction (jet dnR u z c s) (jet dnZ u z c s) D (v 0) (v 1)) m
  obtain ⟨hd, htr, hv, hw⟩ := h
  change dl ≤ m.det * (D.v * D.v * D.v) at hd
  change |A.a + A.d| ≤ tr at htr
  change |A.a - A.d| ≤ di at hv
  change |A.b + A.c| ≤ off at hw
  have hdisk : (A.a - A.d) ^ 2 + (A.b + A.c) ^ 2 ≤ disk ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hv 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs] at h1 h2
    exact (add_le_add h1 h2).trans hsmall
  have hp := lower.trans_le hd
  have cost : tr + disk ≤ 2 * (m.det * (D.v * D.v * D.v)) * g := by
    nlinarith only [hbudget, mul_le_mul_of_nonneg_right hd hg]
  obtain ⟨hm, hs⟩ := mul_ne_zero_iff.mp hp.ne'
  have hDv : D.v ≠ 0 := fun h0 => hs (by rw [h0]; ring)
  rw [velocityHessian_eq phase t ζ v hDv, conjugated_quad _ _ _ _ _ hm hs,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  exact abs_quad_le_of_trace A hp htr hdisk hr cost (w 0) (w 1)

/-- The first frame direction in position coordinates. -/
theorem frame_single_zero (l r : Frame) (τ : ℝ) (hdet : affineDet l r τ ≠ 0) :
    frameEquiv l r τ (EuclideanSpace.single 0 1) 0 = (frameEntries l r τ).a ∧
      frameEquiv l r τ (EuclideanSpace.single 0 1) 1 = (frameEntries l r τ).c := by
  change (frameEquiv l r τ).toContinuousLinearMap _ 0 = _ ∧
    (frameEquiv l r τ).toContinuousLinearMap _ 1 = _
  rw [frameEquiv_forward hdet]
  simp [forward, frameEntries]

/-- The second frame direction in position coordinates. -/
theorem frame_single_one (l r : Frame) (τ : ℝ) (hdet : affineDet l r τ ≠ 0) :
    frameEquiv l r τ (EuclideanSpace.single 1 1) 0 = (frameEntries l r τ).b ∧
      frameEquiv l r τ (EuclideanSpace.single 1 1) 1 = (frameEntries l r τ).d := by
  change (frameEquiv l r τ).toContinuousLinearMap _ 0 = _ ∧
    (frameEquiv l r τ).toContinuousLinearMap _ 1 = _
  rw [frameEquiv_forward hdet]
  simp [forward, frameEntries]

/-- The certificate inequalities at a point of the tube give both directional
hypotheses of the mean value bridge at that point. -/
theorem directional_bounds (phase t : ℝ) (l r : Frame) (τ : ℝ) (ζ w : Plane)
    {dl tr₀ di₀ off₀ disk₀ g₀ tr₁ di₁ off₁ disk₁ g₁ : ℝ} (hdet : affineDet l r τ ≠ 0)
    (lower : 0 < dl) (hg₀ : 0 ≤ g₀) (hr₀ : 0 ≤ disk₀)
    (hsmall₀ : di₀ ^ 2 + off₀ ^ 2 ≤ disk₀ ^ 2) (hbudget₀ : tr₀ + disk₀ ≤ 2 * dl * g₀)
    (hg₁ : 0 ≤ g₁) (hr₁ : 0 ≤ disk₁)
    (hsmall₁ : di₁ ^ 2 + off₁ ^ 2 ≤ disk₁ ^ 2) (hbudget₁ : tr₁ + disk₁ ≤ 2 * dl * g₁)
    (h :
      let u := ζ 0 - dkR0
      let z := ζ 1
      let c := Real.cos (2 * (phase + 1 * t))
      let s := Real.sin (2 * (phase + 1 * t))
      TubeBounds (frameEntries l r τ) (jet dnR u z c s) (jet dnZ u z c s) (jet dD u z c s)
        dl tr₀ di₀ off₀ tr₁ di₁ off₁) :
    |⟪w, (frameEquiv l r τ).symm ((velocityHessian phase 1 t ζ
        (frameEquiv l r τ (EuclideanSpace.single 0 1))) (frameEquiv l r τ w))⟫| ≤ g₀ * ‖w‖ ^ 2 ∧
      |⟪w, (frameEquiv l r τ).symm ((velocityHessian phase 1 t ζ
        (frameEquiv l r τ (EuclideanSpace.single 1 1))) (frameEquiv l r τ w))⟫| ≤
        g₁ * ‖w‖ ^ 2 := by
  obtain ⟨hd, h₀, h₁⟩ := h
  obtain ⟨a0, c0⟩ := frame_single_zero l r τ hdet
  obtain ⟨b1, d1⟩ := frame_single_one l r τ hdet
  constructor
  · apply abs_hessian_quad_le phase t l r τ ζ _ w lower hg₀ hr₀ hsmall₀ hbudget₀
    rw [a0, c0]
    exact ⟨hd, h₀⟩
  · apply abs_hessian_quad_le phase t l r τ ζ _ w lower hg₁ hr₁ hsmall₁ hbudget₁
    rw [b1, d1]
    exact ⟨hd, h₁⟩

end PlasmaLean.Design.DommaschkWideTubeHessian
