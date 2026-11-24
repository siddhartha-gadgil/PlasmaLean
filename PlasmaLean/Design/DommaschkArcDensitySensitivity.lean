/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CylindricalActionSensitivity
public import PlasmaLean.Design.DommaschkPhysicalActionPanel

/-! # Physical QA2R angular arclength sensitivity from field-line velocity -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkArcDensitySensitivity

open Kinetic.CylindricalActionSensitivity DommaschkPhysicalActionPanel DommaschkKam
open DommaschkBounceField DommaschkJacobian Certificates.PositionFrameSlabs Contract

/-- The actual QA2R density R|B|/Bφ is the Euclidean speed made from physical
radius and the two angular field-line velocities, at each point of positive clock. -/
theorem speed_eq {R φ z : ℝ} (hr : 0 < R) (ht : 0 < cylBphi R φ z) :
    arcDensity R φ z = speed R (R * cylBR R φ z / cylBphi R φ z)
      (R * cylBz R φ z / cylBphi R φ z) := by
  apply (sq_eq_sq₀ (show 0 ≤ arcDensity R φ z from
    div_nonneg (mul_nonneg hr.le (norm_nonneg _)) ht.le)
    (show 0 ≤ speed R (R * cylBR R φ z / cylBphi R φ z) (R * cylBz R φ z / cylBphi R φ z)
      from norm_nonneg _)).mp
  rw [arcDensity, div_pow, mul_pow, DommaschkKamC.norm_field_sq, speed_sq]
  field_simp [ht.ne']
  ring

/-- A spatial velocity estimate at two actual same-angle QA2R points bounds
the difference in true arclength per radian using only their physical separation. -/
theorem density_lipschitz (φ : ℝ) (x y : Plane) {L : ℝ} (hL : 0 ≤ L)
    (rx : 0 < x 0) (ry : 0 < y 0)
    (hx : 0 < cylBphi (x 0) φ (x 1)) (hy : 0 < cylBphi (y 0) φ (y 1))
    (velocity : ‖euclideanFlow 0 1 φ x - euclideanFlow 0 1 φ y‖ ≤ L * ‖x - y‖) :
    |arcDensity (x 0) φ (x 1) - arcDensity (y 0) φ (y 1)| ≤ Real.sqrt (1 + L ^ 2) * ‖x - y‖ := by
  rw [speed_eq rx hx, speed_eq ry hy]
  have values (p : Plane) :
      euclideanFlow 0 1 φ p 0 = p 0 * cylBR (p 0) φ (p 1) / cylBphi (p 0) φ (p 1) ∧
      euclideanFlow 0 1 φ p 1 = p 0 * cylBz (p 0) φ (p 1) / cylBphi (p 0) φ (p 1) := by
    change physicalFlow 0 1 φ p.ofLp 0 = _ ∧ physicalFlow 0 1 φ p.ofLp 1 = _
    simp [physicalFlow]
  have bound := density_of_velocity_lipschitz x y hL velocity
  rwa [(values x).1, (values x).2, (values y).1, (values y).2] at bound

end PlasmaLean.Design.DommaschkArcDensitySensitivity
