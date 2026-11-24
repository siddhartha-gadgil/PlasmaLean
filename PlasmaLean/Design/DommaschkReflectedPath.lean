/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSymmetricSections
public import PlasmaLean.Design.DommaschkPhysicalActionPanel
public import PlasmaLean.Design.DommaschkMirrorEndpoints
public import PlasmaLean.Design.DommaschkMirrorLaunch
public import PlasmaLean.Theory.Kinetic.MirrorHeightAction

/-! # Exact path, arclength and action conjugacy at a QA2R symmetry section

A forward trajectory starting from the reflected entrance point supplies a
backward trajectory from the prescribed entrance point. The archived launch
ellipsoids are invariant under this reflection. The resulting enclosures are
the reflections of the forward tubes.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkReflectedPath

open Certificates.PositionFrameSlabs DommaschkJacobianReflection DommaschkSymmetricSections
open DommaschkMirrorLaunch DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel
open DommaschkBounceField Fields.TrajectorySlabs Set

theorem fixed_iff (x : Plane) : flip x = x ↔ x 1 = 0 := by
  constructor
  · intro same
    have h := congrArg (fun p : Plane => p 1) same
    simp only [flip_one] at h
    linarith
  · intro hz
    ext i
    fin_cases i <;> simp [hz]

/-- Every archived entrance contains the reflection of each of its points,
including off-midplane entrance states from a nonzero-width birth sector. -/
theorem seed_mem (e : MirrorEndpoint) (x : Plane) :
    flip x ∈ stateSet e.start ↔ x ∈ stateSet e.start := by
  have identity : e.start.frame = ⟨2^40, 0, 0, 2^40⟩ := by cases e <;> rfl
  have zero : e.start.point.y = 0 := by cases e <;> rfl
  simp only [mem_stateSet_identity identity, flip_zero, flip_one, zero, Int.cast_zero,
    zero_div, sub_zero, neg_sq]

theorem seed_image (e : MirrorEndpoint) : flip '' stateSet e.start = stateSet e.start := by
  ext p
  constructor
  · rintro ⟨q,h,rfl⟩
    exact (seed_mem e q).2 h
  · intro h
    exact ⟨flip p, (seed_mem e p).2 h, flip_twice p⟩

theorem endpoint_axis (e : MirrorEndpoint) : Axis (azimuth e.opposite) := by
  cases e <;> first | exact zero_axis | exact half_pi_axis

theorem flow {α : ℝ} (axis : Axis α) (t : ℝ) (p : Plane) (hR : 0 < p 0) :
    DommaschkJacobian.euclideanFlow α (-1) t (flip p) =
      flip (DommaschkJacobian.euclideanFlow α 1 t p) := by
  have same : DommaschkJacobian.coordinates (flip p) =
      DommaschkSectionReflection.reflect (DommaschkJacobian.coordinates p) := by
    ext i
    fin_cases i <;> simp [DommaschkJacobian.coordinates, DommaschkSectionReflection.reflect]
  have eq := DommaschkSymmetricSections.flow axis t (DommaschkJacobian.coordinates p) hR
  rw [DommaschkJacobian.euclideanFlow, same, eq]
  ext i
  fin_cases i <;> simp [DommaschkJacobian.euclideanFlow, DommaschkJacobian.coordinates,
    DommaschkSectionReflection.reflect]

/-- A true forward ODE solution transforms to the true backward ODE on exactly
the same elapsed-time domain. Its initial state is reflected along with it. -/
theorem trajectory {α t : ℝ} (axis : Axis α) {D : Set ℝ} {y : ℝ → Plane} (hR : 0 < y t 0)
    (ode : HasDerivWithinAt y (DommaschkJacobian.euclideanFlow α 1 t (y t)) D t) :
    HasDerivWithinAt (fun s => flip (y s))
      (DommaschkJacobian.euclideanFlow α (-1) t (flip (y t))) D t := by
  rw [flow axis t _ hR]
  exact flip.hasFDerivAt.comp_hasDerivWithinAt t ode

/-- The reflection of a given physical slab, including its entire tube. -/
def reflectedSlab (slab : Slab Plane) : Slab Plane :=
  ⟨slab.start, slab.stop, fun t => flip '' slab.tube t⟩

/-- Any certified forward solution from every admissible seed gives a backward
step on the reflected tube. Both entrance and exit sets are transported. -/
theorem step {α : ℝ} (axis : Axis α) {slab : Slab Plane} {entry exit : Set Plane}
    (forward : Fields.TrajectorySlabs.Step (DommaschkJacobian.euclideanFlow α 1) slab entry exit)
    (positive : ∀ t ∈ Icc slab.start slab.stop, ∀ p ∈ slab.tube t, 0 < p 0) :
    Fields.TrajectorySlabs.Step (DommaschkJacobian.euclideanFlow α (-1)) (reflectedSlab slab)
      (flip '' entry) (flip '' exit) := by
  refine ⟨forward.ordered, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, start, stop, ode⟩ := forward.solve x hx
  refine ⟨fun t => flip (y t), congrArg (fun p : Plane => flip p) start, ⟨_, stop, rfl⟩, ?_⟩
  intro t ht
  obtain ⟨der, inside⟩ := ode t ht
  exact ⟨trajectory axis (positive t ht _ inside) der, _, inside, rfl⟩

/-- Starting at the same prescribed section state in either direction is
possible from a forward entrance theorem quantified over the entire seed ball. -/
theorem endpoint_step {α : ℝ} (axis : Axis α) {slab : Slab Plane} (e : MirrorEndpoint)
    {exit : Set Plane}
    (forward : Fields.TrajectorySlabs.Step (DommaschkJacobian.euclideanFlow α 1)
      slab (stateSet e.start) exit)
    (positive : ∀ t ∈ Icc slab.start slab.stop, ∀ p ∈ slab.tube t, 0 < p 0) :
    Fields.TrajectorySlabs.Step (DommaschkJacobian.euclideanFlow α (-1)) (reflectedSlab slab)
      (stateSet e.start) (flip '' exit) := by
  simpa only [seed_image] using step axis forward positive

/-- An arbitrary finite chain of forward steps gives one chain on the reflected
tubes with all intermediate matching states transported by the same map. -/
theorem chain {α a b : ℝ} (axis : Axis α) {entry exit : Set Plane} {slabs : List (Slab Plane)}
    (forward : Fields.TrajectorySlabs.Chain (DommaschkJacobian.euclideanFlow α 1)
      a entry b exit slabs)
    (positive : ∀ slab ∈ slabs, ∀ t ∈ Icc slab.start slab.stop, ∀ p ∈ slab.tube t, 0 < p 0) :
    Fields.TrajectorySlabs.Chain (DommaschkJacobian.euclideanFlow α (-1)) a (flip '' entry) b
      (flip '' exit) (slabs.map reflectedSlab) := by
  induction forward with
  | nil => exact .nil _ _
  | cons first _ ih =>
    exact .cons (step axis first (positive _ (List.mem_cons_self ..)))
      (ih fun q hq => positive q (List.mem_cons_of_mem _ hq))

/-- The original physical section state launches a backward solution, using only
a forward chain covering the full admissible seed set. Every backward position
is enclosed by a reflected forward slab at the same elapsed angle. -/
theorem endpoint_trajectory {a b : ℝ} (e : MirrorEndpoint) {exit : Set Plane}
    {slabs : List (Slab Plane)}
    (forward : Fields.TrajectorySlabs.Chain (DommaschkJacobian.euclideanFlow (azimuth e.opposite) 1)
      a (stateSet e.start) b exit slabs)
    (positive : ∀ slab ∈ slabs, ∀ t ∈ Icc slab.start slab.stop, ∀ p ∈ slab.tube t, 0 < p 0)
    {x : Plane} (entry : x ∈ stateSet e.start) :
    ∃ y : ℝ → Plane, y a = x ∧ flip (y b) ∈ exit ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt y
        (DommaschkJacobian.euclideanFlow (azimuth e.opposite) (-1) t (y t)) (Icc a b) t) ∧
      ∀ s ∈ slabs, ∀ t ∈ Icc s.start s.stop, flip (y t) ∈ s.tube t := by
  have reflected := chain (endpoint_axis e) forward positive
  rw [seed_image] at reflected
  obtain ⟨y, initial, ⟨last, hl, eq⟩, ode, tubes⟩ := reflected.exists_trajectory entry
  refine ⟨y, initial, ?_, ode, ?_⟩
  · simpa only [← eq, flip_twice] using hl
  · intro s hs t ht
    obtain ⟨z, hz, eq⟩ := tubes (reflectedSlab s) (List.mem_map.mpr ⟨s,hs,rfl⟩) t ht
    simpa only [← eq, flip_twice] using hz

theorem density {α : ℝ} (axis : Axis α) (t : ℝ) (x : Plane) (hR : 0 < x 0) :
    arcDensity ((flip x) 0) (α - t) ((flip x) 1) = arcDensity (x 0) (α + t) (x 1) := by
  have h := DommaschkSymmetricSections.strength axis t x hR
  unfold DommaschkMirrorTubeCrossing.strength at h
  simp only [flip_zero, flip_one] at h ⊢
  rw [arcDensity, arcDensity, h, (cylindrical axis hR (x 1) t).1]

/-- The two reflected paths have identical accumulated arclength per radian. -/
theorem arclength {α a b : ℝ} (axis : Axis α) (y : ℝ → Plane) (hR : ∀ t ∈ uIcc a b, 0 < y t 0) :
    (∫ t in a..b, arcDensity ((flip (y t)) 0) (α - t) ((flip (y t)) 1)) =
      ∫ t in a..b, arcDensity (y t 0) (α + t) (y t 1) :=
  intervalIntegral.integral_congr (fun t ht => density axis t (y t) (hR t ht))

/-- Reflected paths have identical longitudinal action at every mirror height. -/
theorem action {α a b : ℝ} (axis : Axis α) (y : ℝ → Plane) (hR : ∀ t ∈ uIcc a b, 0 < y t 0)
    (h : ℝ) :
    Kinetic.MirrorHeightAction.action
      (fun t => DommaschkMirrorTubeCrossing.strength (α - t) (flip (y t)))
      (fun t => arcDensity ((flip (y t)) 0) (α - t) ((flip (y t)) 1)) a b h =
    Kinetic.MirrorHeightAction.action
      (fun t => DommaschkMirrorTubeCrossing.strength (α + t) (y t))
      (fun t => arcDensity (y t 0) (α + t) (y t 1)) a b h := by
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [density axis t (y t) (hR t ht), DommaschkSymmetricSections.strength axis t (y t) (hR t ht)]

end PlasmaLean.Design.DommaschkReflectedPath
