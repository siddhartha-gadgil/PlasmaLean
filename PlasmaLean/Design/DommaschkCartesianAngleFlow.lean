/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFirstMirrorWell

/-! # The autonomous Cartesian vector field for the QA2R angular clock -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCartesianAngleFlow
open Fields Contract Set
open Certificates.PositionFrameSlabs (Plane)
open DommaschkFirstMirrorWell DommaschkSignedTraceDomain DommaschkBounceField DommaschkKam
open DommaschkJacobian
set_option maxRecDepth 8000

abbrev B := DommaschkQA2R.field DommaschkQA2R.candidate

/-- The Cartesian numerator of the angular velocity of a field line. -/
def angular (x : Space) : ℝ := x 0 * B x 1 - x 1 * B x 0

def regular : Set Space := {x | x ∈ CylAlgebra.domain ∧ 0 < angular x}

/-- Multiplication by this positive factor chooses increasing geometric azimuth as time. -/
def factor (x : Space) : ℝ := CylAlgebra.r2 x / angular x

def velocity (x : Space) : Space := factor x • B x

def speed (x : Space) : ℝ := factor x * ‖B x‖

private theorem field_smooth {x : Space} (hx : x ∈ CylAlgebra.domain) : ContDiffAt ℝ 1 B x :=
  ((DommaschkQA2R.field_vacuum DommaschkQA2R.candidate).contDiffOn.of_le (by norm_num)).contDiffAt
    ((DommaschkQA2R.field_vacuum DommaschkQA2R.candidate).isOpen.mem_nhds hx)

private theorem coord (i : Fin 3) : ContDiff ℝ 1 (fun x : Space => x i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff

private theorem angular_smooth {x : Space} (hx : x ∈ CylAlgebra.domain) :
    ContDiffAt ℝ 1 angular x :=
  ((coord 0).contDiffAt.mul ((coord 1).contDiffAt.comp x (field_smooth hx))).sub
    ((coord 1).contDiffAt.mul ((coord 0).contDiffAt.comp x (field_smooth hx)))

theorem isOpen_regular : IsOpen regular := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.inter_mem ((DommaschkQA2R.field_vacuum DommaschkQA2R.candidate).isOpen.mem_nhds hx.1)
    ((angular_smooth hx.1).continuousAt.eventually_const_lt hx.2)

theorem field_ne_zero {x : Space} (hx : x ∈ regular) : B x ≠ 0 := by
  intro hz
  have ht := hx.2
  simp [angular, hz] at ht

theorem factor_smooth {x : Space} (hx : x ∈ regular) : ContDiffAt ℝ 1 factor x :=
  (((coord 0).contDiffAt.pow 2).add ((coord 1).contDiffAt.pow 2)).div (angular_smooth hx.1) hx.2.ne'

theorem velocity_smooth {x : Space} (hx : x ∈ regular) : ContDiffAt ℝ 1 velocity x :=
  (factor_smooth hx).smul (field_smooth hx.1)

theorem strength_smooth {x : Space} (hx : x ∈ regular) : ContDiffAt ℝ 1 (fun q => ‖B q‖) x :=
  (field_smooth hx.1).norm ℝ (field_ne_zero hx)

theorem speed_smooth {x : Space} (hx : x ∈ regular) : ContDiffAt ℝ 1 speed x :=
  (factor_smooth hx).mul (strength_smooth hx)

theorem speed_pos {x : Space} (hx : x ∈ regular) : 0 < speed x :=
  mul_pos (div_pos hx.1 hx.2) (norm_pos_iff.mpr (field_ne_zero hx))

theorem aligned {x : Space} (hx : x ∈ regular) :
    velocity x = speed x • Kinetic.GCLittlejohn.bhat B x := by
  rw [speed, Kinetic.GCLittlejohn.bhat, smul_smul, mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (field_ne_zero hx)), mul_one]
  rfl

theorem radial_at (R t z : ℝ) : CylAlgebra.r2 (cylPoint R t z) = R^2 := by
  simp only [CylAlgebra.r2, cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination R^2 * Real.cos_sq_add_sin_sq t

theorem angular_at (R t z : ℝ) : angular (cylPoint R t z) = R * cylBphi R t z := by
  unfold angular cylBphi
  change R * Real.cos t * _ - R * Real.sin t * _ = _
  ring

theorem in_regular {p : Plane} (reg : Region p) (t : ℝ) : cylPoint (p 0) t (p 1) ∈ regular := by
  have hr : 0 < p 0 := by linarith [reg.1.1]
  have hd := DommaschkSignedTraceDenominator.regular t reg.1 reg.2
  constructor
  · change 0 < CylAlgebra.r2 _
    rw [radial_at]
    positivity
  · rw [angular_at]
    exact mul_pos hr (toroidal_pos_of_den hr (by linarith))

theorem speed_at {p : Plane} (reg : Region p) (t : ℝ) :
    speed (cylPoint (p 0) t (p 1)) = DommaschkPhysicalActionPanel.arcDensity (p 0) t (p 1) := by
  have hr : 0 < p 0 := by linarith [reg.1.1]
  have hd := DommaschkSignedTraceDenominator.regular t reg.1 reg.2
  have hp : 0 < cylBphi (p 0) t (p 1) := toroidal_pos_of_den hr (by linarith)
  rw [speed, factor, radial_at, angular_at, DommaschkPhysicalActionPanel.arcDensity]
  field_simp [hr.ne', hp.ne']

/-- The archived, nonautonomous two-coordinate ODE is the autonomous three-dimensional
field line at positive physical speed. This uses no angular coordinate chart or inverse angle. -/
theorem cartesian_ode {y : ℝ → Plane} {t : ℝ}
    (ode : HasDerivAt y (euclideanFlow 0 1 t (y t)) t) (reg : Region (y t)) :
    HasDerivAt (point y) (velocity (point y t)) t := by
  have hr : 0 < y t 0 := by linarith [reg.1.1]
  have hd := DommaschkSignedTraceDenominator.regular t reg.1 reg.2
  have hp : 0 < cylBphi (y t 0) t (y t 1) := toroidal_pos_of_den hr (by linarith)
  have geom := Kinetic.MirrorWell.cylindrical_trace_speed B (fun s => y s 0) (fun s => y s 1) 0 t hr
  simp only [zero_add] at geom
  have az : -Real.sin t * B (point y t) 0 + Real.cos t * B (point y t) 1 =
      cylBphi (y t 0) t (y t 1) := by simp [cylBphi, point]
  unfold point at az
  rw [az] at geom
  have dr := (proj 0).hasFDerivAt.comp_hasDerivAt t ode
  have dz := (proj 1).hasFDerivAt.comp_hasDerivAt t ode
  change HasDerivAt (fun s => y s 0) ((physicalFlow 0 1 t (y t).ofLp) 0) t at dr
  change HasDerivAt (fun s => y s 1) ((physicalFlow 0 1 t (y t).ofLp) 1) t at dz
  have tang := (geom hp (by simpa [physicalFlow, cylBR] using dr)
    (by simpa [physicalFlow, cylBz] using dz)).2.2
  have hr' : point y t ∈ regular := in_regular reg t
  have hs : speed (point y t) = _ := speed_at reg t
  rw [aligned hr', hs]
  exact tang

end PlasmaLean.Design.DommaschkCartesianAngleFlow
