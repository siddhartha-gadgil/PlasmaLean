/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianFrames
public import PlasmaLean.Design.DommaschkBounceFlowStep
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Spatial derivative of the physical field-line velocity

The two formal sparse polynomial derivatives give the Fréchet derivative with
respect to radius and height. The signed time direction multiplies both rows
of the velocity Jacobian.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJacobian

open DommaschkKam DkPoly DommaschkBounceField
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def value (m : Tm) (u z c s : ℝ) :=
  (m.q : ℝ) * (u ^ m.a * z ^ m.b * c ^ m.c * s ^ m.d)

private lemma evR_cons (m : Tm) (p : SP) (u z c s : ℝ) :
    evR u z c s (m :: p) = value m u z c s + evR u z c s p := by
  simp [evR, value]

private lemma evR_append (p q : SP) (u z c s : ℝ) :
    evR u z c s (p ++ q) = evR u z c s p + evR u z c s q := by
  simp [evR]

private lemma term_partials (m : Tm) (u z c s : ℝ) :
    evR u z c s m.dU = (m.q : ℝ) * (m.a * u ^ (m.a - 1) * z ^ m.b * c ^ m.c * s ^ m.d) ∧
    evR u z c s m.dZ = (m.q : ℝ) * (u ^ m.a * (m.b * z ^ (m.b - 1)) * c ^ m.c * s ^ m.d) := by
  constructor
  · cases ha : m.a <;> simp [Tm.dU, ha, evR]
    ring
  · cases hb : m.b <;> simp [Tm.dZ, hb, evR]
    ring

private lemma term_derivative (m : Tm) {u z : E → ℝ} {U Z : E →L[ℝ] ℝ} {x : E}
    (hu : HasFDerivAt u U x) (hz : HasFDerivAt z Z x) (c s : ℝ) :
    HasFDerivAt (fun y => value m (u y) (z y) c s)
      (evR (u x) (z x) c s m.dU • U + evR (u x) (z x) c s m.dZ • Z) x := by
  have hm := (((((hu.pow m.a).mul (hz.pow m.b)).mul_const (c ^ m.c)).mul_const
    (s ^ m.d)).const_mul (m.q : ℝ))
  unfold value
  convert hm using 1
  ext y
  obtain ⟨a, b⟩ := term_partials m (u x) (z x) c s
  simp [a, b, smul_eq_mul]
  ring

/-- Formal partial derivatives of any sparse field polynomial determine its full spatial
derivative for arbitrary differentiable input coordinates. -/
theorem sparse_derivative (p : SP) {u z : E → ℝ} {U Z : E →L[ℝ] ℝ} {x : E}
    (hu : HasFDerivAt u U x) (hz : HasFDerivAt z Z x) (c s : ℝ) :
    HasFDerivAt (fun y => evR (u y) (z y) c s p)
      (evR (u x) (z x) c s (dU p) • U + evR (u x) (z x) c s (dZ p) • Z) x := by
  induction p with
  | nil => simpa [dU, dZ, evR] using (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (x := x))
  | cons m p ih =>
    simp only [evR_cons]
    convert (term_derivative m hu hz c s).add ih using 1
    simp only [dU, dZ, List.flatMap_cons, evR_append, add_smul]
    abel

/-- The signed quotient derivative in both spatial directions at once. -/
theorem quotient_derivative (n : SP) {u z : E → ℝ} {U Z : E →L[ℝ] ℝ} {x : E}
    (hu : HasFDerivAt u U x) (hz : HasFDerivAt z Z x) (c s sign : ℝ)
    (hd : evR (u x) (z x) c s dD ≠ 0) :
    HasFDerivAt (fun y => sign * (evR (u y) (z y) c s n / evR (u y) (z y) c s dD))
      (sign • (quotientEntry n dU (u x) (z x) c s • U +
        quotientEntry n dZ (u x) (z x) c s • Z)) x := by
  have hn := sparse_derivative n hu hz c s
  have hD := sparse_derivative dD hu hz c s
  have hi := (hasDerivAt_inv hd).comp_hasFDerivAt x hD
  have h := (hn.mul hi).const_mul sign
  simp only [div_eq_mul_inv]
  apply h.congr_fderiv
  ext y
  simp [quotientEntry, quotientNumerator, smul_eq_mul]
  field_simp [hd]
  ring

/-- Euclidean plane with radius and height as its two coordinates. -/
abbrev PhysicalPlane := EuclideanSpace ℝ (Fin 2)

/-- Projection onto radius or height with the Euclidean norm on the domain. -/
abbrev proj (i : Fin 2) : PhysicalPlane →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) i

/-- The continuous linear identification with the coordinate function space. -/
abbrev coordinates := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)

/-- Physical cylinder field-line ODE expressed in Euclidean poloidal coordinates. -/
def euclideanFlow (phase sign t : ℝ) (x : PhysicalPlane) : PhysicalPlane :=
  coordinates.symm (physicalFlow phase sign t (coordinates x))

/-- One row of the physical Jacobian in the radius/height basis. -/
def velocityRow (n : SP) (phase sign t : ℝ) (x : PhysicalPlane) : PhysicalPlane →L[ℝ] ℝ :=
  let φ := phase + sign * t
  let u := x 0 - dkR0
  let z := x 1
  let entry := fun der => quotientEntry n der u z (Real.cos (2 * φ)) (Real.sin (2 * φ))
  sign • (entry dU • proj 0 + entry dZ • proj 1)

/-- The Jacobian assembled from the two certified rows. -/
def velocityJacobian (phase sign t : ℝ) (x : PhysicalPlane) : PhysicalPlane →L[ℝ] PhysicalPlane :=
  coordinates.symm.toContinuousLinearMap.comp <|
    ContinuousLinearMap.pi ![velocityRow dnR phase sign t x, velocityRow dnZ phase sign t x]

/-- With positive cylindrical radius and nonzero field denominator, the candidate's true
field-line vector field has the sparse quotient Jacobian in Euclidean coordinates. -/
theorem physical_derivative (phase sign t : ℝ) (x : PhysicalPlane) (hr : 0 < x 0)
    (hd : atPoint dD (x 0) (phase + sign * t) (x 1) ≠ 0) :
    HasFDerivAt (euclideanFlow phase sign t) (velocityJacobian phase sign t x) x := by
  let φ := phase + sign * t
  let c := Real.cos (2 * φ)
  let s := Real.sin (2 * φ)
  let u (y : PhysicalPlane) := y 0 - dkR0
  let z (y : PhysicalPlane) := y 1
  have hu : HasFDerivAt u (proj 0) x := (proj 0).hasFDerivAt.sub_const dkR0
  have hz : HasFDerivAt z (proj 1) x := (proj 1).hasFDerivAt
  have hD := sparse_derivative dD hu hz c s
  have denom : evR (u x) (z x) c s dD ≠ 0 := hd
  have row (n : SP) : HasFDerivAt
      (fun y => sign * (evR (u y) (z y) c s n / evR (u y) (z y) c s dD))
      (velocityRow n phase sign t x) x := quotient_derivative n hu hz c s sign denom
  have both : HasFDerivAt (fun y : PhysicalPlane => ratioFlow phase sign t (coordinates y))
      (ContinuousLinearMap.pi ![velocityRow dnR phase sign t x, velocityRow dnZ phase sign t x])
      x := by
    apply hasFDerivAt_pi''
    intro i
    fin_cases i
    · exact row dnR
    · exact row dnZ
  have radiusPos : ∀ᶠ y in 𝓝 x, 0 < y 0 :=
    (proj 0).continuous.continuousAt.eventually_const_lt hr
  have denomNe := hD.continuousAt.eventually_ne denom
  apply (coordinates.symm.toContinuousLinearMap.hasFDerivAt.comp x both).congr_of_eventuallyEq
  filter_upwards [radiusPos, denomNe] with y hR hden
  exact congrArg coordinates.symm (ratio_eq_physical phase sign t (coordinates y) hR hden).symm

open Certificates.PositionFrameSlabs

/-- The analytic derivative is the matrix used by the quadratic certificate. -/
theorem velocityJacobian_eq (phase sign t : ℝ) (x : PhysicalPlane) :
    let φ := phase + sign * t
    let D := atPoint dD (x 0) φ (x 1)
    velocityJacobian phase sign t x =
      ((spatialNumerator (x 0 - dkR0) (x 1) (Real.cos (2 * φ)) (Real.sin (2 * φ))).scale
        (sign / (D * D))).toCLM := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;>
    simp [velocityJacobian, velocityRow, Entries.toCLM, spatialNumerator, Entries.scale,
      quotientEntry, atPoint, coordinates, proj, smul_eq_mul] <;> ring

/-- In signed elapsed angle the forward quotient matrix acquires exactly the time sign. -/
theorem velocityJacobian_spatial (phase sign t : ℝ) (x : PhysicalPlane) :
    velocityJacobian phase sign t x = sign • spatialMatrix (x 0 - dkR0) (x 1)
      (Real.cos (2 * (phase + sign * t))) (Real.sin (2 * (phase + sign * t))) := by
  rw [velocityJacobian_eq]
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;>
    simp [Entries.toCLM, spatialNumerator, Entries.scale, spatialMatrix, quotientEntry,
      atPoint, smul_eq_mul] <;> ring

/-- The sparse evaluation on the signed angular clock varies continuously in time and position. -/
def clockValue (p : SP) (phase sign : ℝ) (q : ℝ × PhysicalPlane) : ℝ :=
  atPoint p (q.2 0) (phase + sign * q.1) (q.2 1)

theorem continuous_clockValue (p : SP) (phase sign : ℝ) :
    Continuous (clockValue p phase sign) := by
  induction p with
  | nil =>
    change Continuous (fun _ : ℝ × PhysicalPlane => (0 : ℝ))
    exact continuous_const
  | cons m p ih =>
    change Continuous (fun q : ℝ × PhysicalPlane => _)
    simp only [clockValue, atPoint, evR_cons]
    apply Continuous.add _ ih
    unfold value
    fun_prop

/-- Joint continuity of the true field-line velocity at a regular point of the field. -/
theorem continuousAt_euclideanFlow (phase sign : ℝ) (q : ℝ × PhysicalPlane)
    (hr : 0 < q.2 0) (hd : clockValue dD phase sign q ≠ 0) :
    ContinuousAt (fun y : ℝ × PhysicalPlane => euclideanFlow phase sign y.1 y.2) q := by
  have cd := (continuous_clockValue dD phase sign).continuousAt (x := q)
  have h (n : SP) := continuousAt_const (y := sign) |>.mul
    (((continuous_clockValue n phase sign).continuousAt).div cd hd)
  have both : ContinuousAt (fun y : ℝ × PhysicalPlane => ratioFlow phase sign y.1
      (coordinates y.2)) q := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact h dnR
    · exact h dnZ
  have hp : Continuous (fun y : ℝ × PhysicalPlane => y.2 0) :=
    (proj 0).continuous.comp continuous_snd
  apply (coordinates.symm.continuous.continuousAt.comp both).congr
  filter_upwards [hp.continuousAt.eventually_const_lt hr, cd.eventually_ne hd] with y hR hden
  exact congrArg coordinates.symm (ratio_eq_physical phase sign y.1 (coordinates y.2) hR hden)

/-- Joint continuity of the spatial Jacobian on the regular denominator locus. -/
theorem continuousAt_velocityJacobian (phase sign : ℝ) (q : ℝ × PhysicalPlane)
    (hd : clockValue dD phase sign q ≠ 0) :
    ContinuousAt (fun y : ℝ × PhysicalPlane => velocityJacobian phase sign y.1 y.2) q := by
  let val (p : SP) := clockValue p phase sign
  have cv (p : SP) : ContinuousAt (val p) q := (continuous_clockValue p phase sign).continuousAt
  have denominator : ContinuousAt (fun y => sign / (val dD y * val dD y)) q :=
    continuousAt_const.div ((cv dD).mul (cv dD)) (mul_ne_zero hd hd)
  let num (n : SP) (d : SP → SP) (y : ℝ × PhysicalPlane) :=
    val (d n) y * val dD y - val n y * val (d dD) y
  have entry (n : SP) (d : SP → SP) :
      ContinuousAt (fun y => sign / (val dD y * val dD y) * num n d y) q :=
    denominator.mul (((cv (d n)).mul (cv dD)).sub ((cv n).mul (cv (d dD))))
  simp_rw [velocityJacobian_eq, Entries.toCLM, Entries.scale, spatialNumerator]
  conv in matrix _ _ _ _ => rw [matrix_basis]
  exact ((((entry dnR dU).smul continuousAt_const).add
    ((entry dnR dZ).smul continuousAt_const)).add ((entry dnZ dU).smul continuousAt_const)).add
    ((entry dnZ dZ).smul continuousAt_const)

end PlasmaLean.Design.DommaschkJacobian
