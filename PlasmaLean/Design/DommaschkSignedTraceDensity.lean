/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedTraceDomain
public import PlasmaLean.Design.DommaschkSignedTraceDenominator
public import PlasmaLean.Design.DommaschkArcDensitySensitivity

/-! # Continuity and positivity of genuine QA2R arclength on the pilot region -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedTraceDensity

open Certificates.PositionFrameSlabs DommaschkSignedTraceDomain DommaschkJacobian
open Kinetic.CylindricalActionSensitivity DommaschkBounceField DommaschkPhysicalActionPanel Set

/-- The positive-time field tangent represented by its angular, radial and axial components. -/
def angularSpeed (t : ℝ) (x : Plane) : ℝ :=
  speed (x 0) (euclideanFlow 0 1 t x 0) (euclideanFlow 0 1 t x 1)

theorem density_eq {x : Plane} (t : ℝ) (rx : Region x) :
    arcDensity (x 0) t (x 1) = angularSpeed t x := by
  have hr : 0 < x 0 := by linarith [rx.1.1]
  have hd := DommaschkSignedTraceDenominator.regular t rx.1 rx.2
  have hp := toroidal_pos_of_den hr (lt_trans (by norm_num : (0 : ℝ) < 1 / 64) hd)
  rw [DommaschkArcDensitySensitivity.speed_eq hr hp]
  change _ = speed (x 0) (physicalFlow 0 1 t x.ofLp 0) (physicalFlow 0 1 t x.ofLp 1)
  simp [physicalFlow]

/-- Independent of any derivative of y, the true field-line velocity varies continuously
along a continuous curve inside the pilot region. -/
theorem continuousOn_flow_region {y : ℝ → Plane} {s : Set ℝ} (cy : ContinuousOn y s)
    (region : ∀ t ∈ s, Region (y t)) : ContinuousOn (fun t => euclideanFlow 0 1 t (y t)) s := by
  intro t ht
  have hr : 0 < y t 0 := by linarith [(region t ht).1.1]
  have den := DommaschkSignedTraceDenominator.regular t (region t ht).1 (region t ht).2
  have nz : clockValue DommaschkKam.dD 0 1 (t, y t) ≠ 0 := by
    simpa only [clockValue, one_mul, zero_add] using
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 64) den).ne'
  exact (continuousAt_euclideanFlow 0 1 (t, y t) hr nz).comp_continuousWithinAt
    (f := fun u => (u, y u)) ((continuousWithinAt_id (s := s)).prodMk (cy t ht))

theorem continuousOn_speed_region {y : ℝ → Plane} {s : Set ℝ} (cy : ContinuousOn y s)
    (region : ∀ t ∈ s, Region (y t)) : ContinuousOn (fun t => angularSpeed t (y t)) s := by
  have cf := continuousOn_flow_region cy region
  have c0 := (proj 0).continuous.comp_continuousOn cy
  have f0 := (proj 0).continuous.comp_continuousOn cf
  have f1 := (proj 1).continuous.comp_continuousOn cf
  simpa only [angularSpeed, speed_formula, Pi.pow_apply, Pi.add_apply, Function.comp_apply,
    proj, PiLp.proj_apply] using ((c0.pow 2).add (f0.pow 2) |>.add (f1.pow 2)).sqrt

/-- The original physical field magnitude divided by its toroidal component gives
a continuous arclength density on every subset along a continuous curve in the envelope. -/
theorem continuousOn_density_region {y : ℝ → Plane} {s : Set ℝ} (cy : ContinuousOn y s)
    (region : ∀ t ∈ s, Region (y t)) :
    ContinuousOn (fun t => arcDensity (y t 0) t (y t 1)) s :=
  (continuousOn_speed_region cy region).congr (fun t ht => density_eq t (region t ht))

theorem radius_le_speed (t : ℝ) (x : Plane) : x 0 ≤ angularSpeed t x := by
  have sq := speed_sq (x 0) (euclideanFlow 0 1 t x 0) (euclideanFlow 0 1 t x 1)
  have nonneg : 0 ≤ angularSpeed t x := norm_nonneg _
  change angularSpeed t x ^ 2 = _ at sq
  nlinarith [sq_nonneg (euclideanFlow 0 1 t x 0), sq_nonneg (euclideanFlow 0 1 t x 1)]

/-- Physical arclength advances uniformly on the closed region, including the mirror points. -/
theorem density_lower {x : Plane} (t : ℝ) (rx : Region x) : 7 / 8 ≤ arcDensity (x 0) t (x 1) := by
  rw [density_eq t rx]
  exact rx.1.1.trans (radius_le_speed t x)

end PlasmaLean.Design.DommaschkSignedTraceDensity
