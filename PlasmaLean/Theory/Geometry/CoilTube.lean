/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.ParametricBounds
public import PlasmaLean.Theory.Fields.BiotSavart

/-!
# Conservative finite-thickness coil envelopes

A tube is the union of closed balls around a centerline. It encloses a winding
pack/casing only when that containment is separately established. No regular
swept-solid parametrization, reach, or Jacobian is asserted. The separation proof
is valid even for overapproximating tubes and includes every point, not samples.
-/
public section
namespace PlasmaLean.Geometry
open Fields

/-- A full-parameter radius-r envelope, without an unproved nearest-point choice. -/
@[expose] def CoilTube (c : ℝ → Space) (r : ℝ) : Set Space :=
  {x | ∃ t, dist (c t) x ≤ r}

/-- A nonnegative-radius tube contains its entire centerline. -/
theorem centerline_mem_tube (c : ℝ → Space) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    c t ∈ CoilTube c r := ⟨t, by simpa using hr⟩

/-- A zero-radius tube is exactly the range of the centerline. -/
theorem tube_zero (c : ℝ → Space) : CoilTube c 0 = Set.range c := by
  ext x
  simp [CoilTube, dist_le_zero]

/-- Tube envelopes inherit all-pairs separation with both thicknesses subtracted. -/
theorem tube_clearance (c₁ c₂ : ℝ → Space) {d r₁ r₂ : ℝ}
    (sep : ∀ t u, d ≤ dist (c₁ t) (c₂ u)) {x y : Space}
    (hx : x ∈ CoilTube c₁ r₁) (hy : y ∈ CoilTube c₂ r₂) :
    d - r₁ - r₂ ≤ dist x y := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨u, hu⟩ := hy
  exact clearance_of_nearby _ _ _ _ (sep t u) ht (by simpa only [dist_comm] using hu)

/-- A strictly positive residual gap proves disjointness of the entire envelopes. -/
theorem tubes_disjoint (c₁ c₂ : ℝ → Space) {d r₁ r₂ : ℝ}
    (sep : ∀ t u, d ≤ dist (c₁ t) (c₂ u)) (gap : r₁ + r₂ < d) :
    Disjoint (CoilTube c₁ r₁) (CoilTube c₂ r₂) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h := tube_clearance c₁ c₂ sep hx hy
  rw [dist_self] at h
  linarith

/-- A displaced centerline's entire tube fits in an enlarged nominal envelope. -/
theorem perturbed_tube_subset (c actual : ℝ → Space) {ε r : ℝ}
    (pos : ∀ t, dist (c t) (actual t) ≤ ε) :
    CoilTube actual r ⊆ CoilTube c (ε + r) := by
  rintro x ⟨t, ht⟩
  exact ⟨t, (dist_triangle _ _ _).trans (add_le_add (pos t) ht)⟩

end PlasmaLean.Geometry
