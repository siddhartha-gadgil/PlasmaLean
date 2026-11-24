/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkReflectedPath

/-! # Transfer uniform forward action bounds to backward physical launches

A birth away from the midplane has a different reflected seed. A bound proved
for every allowed forward seed still transfers to a backward solution from
each prescribed birth because all eight seed ellipsoids are invariant.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkReflectedActionBounds

open Certificates.PositionFrameSlabs DommaschkJacobianReflection DommaschkJacobian
open DommaschkMirrorLaunch DommaschkPhysicalActionPanel DommaschkMirrorTubeCrossing Set

/-- Physical angular action on a specified signed branch. -/
def branchAction (α sign a b h : ℝ) (y : ℝ → Plane) : ℝ :=
  Kinetic.MirrorHeightAction.action
    (fun t => strength (α + sign * t) (y t))
    (fun t => arcDensity (y t 0) (α + sign * t) (y t 1)) a b h

/-- Solving forward from the reflected seed transports every certified action
height simultaneously to the prescribed backward birth. The predicate may encode
bounds for the whole action profile, including relations between heights. -/
theorem transfer (e : MirrorEndpoint) {a b : ℝ} (ordered : a ≤ b)
    (P : (ℝ → ℝ) → Prop)
    (forward : ∀ x ∈ stateSet e.start, ∃ y : ℝ → Plane, y a = x ∧
      (∀ t ∈ Icc a b, 0 < y t 0 ∧ HasDerivWithinAt y
        (euclideanFlow (azimuth e.opposite) 1 t (y t)) (Icc a b) t) ∧
      P (fun h => branchAction (azimuth e.opposite) 1 a b h y)) :
    ∀ x ∈ stateSet e.start, ∃ y : ℝ → Plane, y a = x ∧
      (∀ t ∈ Icc a b, 0 < y t 0 ∧ HasDerivWithinAt y
        (euclideanFlow (azimuth e.opposite) (-1) t (y t)) (Icc a b) t) ∧
      P (fun h => branchAction (azimuth e.opposite) (-1) a b h y) := by
  intro x hx
  obtain ⟨y, initial, ode, actions⟩ := forward (flip x) ((DommaschkReflectedPath.seed_mem e x).2 hx)
  refine ⟨fun t => flip (y t), ?_, ?_, ?_⟩
  · simp only [initial, flip_twice]
  · intro t ht
    obtain ⟨hr, ht'⟩ := ode t ht
    exact ⟨by simpa only [flip_zero] using hr,
      DommaschkReflectedPath.trajectory (DommaschkReflectedPath.endpoint_axis e) hr ht'⟩
  · have profile : (fun h => branchAction (azimuth e.opposite) (-1) a b h (fun t => flip (y t))) =
        (fun h => branchAction (azimuth e.opposite) 1 a b h y) := by
      funext h
      have hr : ∀ t ∈ uIcc a b, 0 < y t 0 :=
        fun t ht => (ode t (uIcc_of_le ordered ▸ ht)).1
      simpa only [branchAction, one_mul, neg_one_mul, ← sub_eq_add_neg] using
        DommaschkReflectedPath.action (DommaschkReflectedPath.endpoint_axis e) y hr h
    rwa [profile]

end PlasmaLean.Design.DommaschkReflectedActionBounds
