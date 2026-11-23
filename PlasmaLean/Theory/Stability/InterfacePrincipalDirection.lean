/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Ring

/-!
# A local obstruction to the toroidal pressure-step sign criterion

At each point of a surface arc, let `g` and `h` be the two covector rows
`g(V,·)` and `II(V,·)` in the same tangent basis, with `V` the field direction.
A sign change of their determinant locates a principal direction. If the normal
curvature there is positive, every variation with positive first-order pressure
has positive mixed curvature there. This excludes the strict negative curvature
condition in N-44 even for variations free to vary along the interface.
-/

@[expose] public section

namespace PlasmaLean.Stability.InterfacePrincipalDirection

/-- Pair a covector row with tangent components in the same basis. -/
def pair (a x : ℝ × ℝ) : ℝ := a.1 * x.1 + a.2 * x.2

/-- The determinant of two covector rows. -/
def det (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

/-- At a principal direction of positive curvature, the two covectors define the
same positive half-plane. Only the value on the field direction fixes the sign. -/
theorem positive_at_principal {g h v : ℝ × ℝ} (hdet : det g h = 0)
    (hg : 0 < pair g v) (hh : 0 < pair h v) (z : ℝ × ℝ) (hz : 0 < pair g z) :
    0 < pair h z := by
  have hid : pair g v * pair h z - pair h v * pair g z = det g h * det v z := by
    unfold pair det
    ring
  rw [hdet, zero_mul, sub_eq_zero] at hid
  exact pos_of_mul_pos_right (hid.symm ▸ mul_pos hh hz) hg.le

/-- Opposite determinant signs at the ends of an arc and positive normal curvature
throughout give one point obstructing all positive-pressure variations at once. -/
theorem exists_obstruction_of_sign_change {l r : ℝ} (hlr : l ≤ r)
    {g h v : ℝ → ℝ × ℝ} (hc : ContinuousOn (fun t => det (g t) (h t)) (Set.Icc l r))
    (hl : det (g l) (h l) ≤ 0) (hr : 0 ≤ det (g r) (h r))
    (hg : ∀ t ∈ Set.Icc l r, 0 < pair (g t) (v t))
    (hh : ∀ t ∈ Set.Icc l r, 0 < pair (h t) (v t)) :
    ∃ t ∈ Set.Icc l r, ∀ z, 0 < pair (g t) z → 0 < pair (h t) z := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc hlr hc (show 0 ∈ Set.Icc _ _ from ⟨hl, hr⟩)
  exact ⟨t, ht, positive_at_principal he (hg t ht) (hh t ht)⟩

end PlasmaLean.Stability.InterfacePrincipalDirection
