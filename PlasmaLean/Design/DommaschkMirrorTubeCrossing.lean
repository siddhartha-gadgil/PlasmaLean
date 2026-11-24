/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceObservables
public import PlasmaLean.Design.DommaschkSectionReflection
public import PlasmaLean.Certificates.PositionFrameODE
public import PlasmaLean.Theory.Kinetic.MirrorWellCriterion

/-! # First encounter with a mirror height on a certified physical tube -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorTubeCrossing
open Contract Certificates.PositionFrameSlabs DommaschkBounceField Set

/-- Norm of the candidate field at the cylindrical position of a geometric-angle trace. -/
def strength (φ : ℝ) (x : Plane) : ℝ :=
  ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint (x 0) φ (x 1))‖

/-- The candidate field norm has the same value at the reflected physical point. -/
theorem strength_reflected {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R (-φ) (-z))‖ =
    ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  obtain ⟨p,r,v⟩ := DommaschkSectionReflection.field_reflect hR φ z
  rw [DommaschkKamC.norm_field_sq, DommaschkKamC.norm_field_sq, p, r, v, neg_sq]

set_option maxRecDepth 16000 in
/-- Continuity along an enclosed field line follows from positive cylindrical radius. -/
theorem continuousOn_strength {y : ℝ → Plane} {s : Set ℝ} (hy : ContinuousOn y s)
    (sign : ℝ) (hR : ∀ t ∈ s, 0 < y t 0) :
    ContinuousOn (fun t => strength (sign*t) (y t)) s := by
  intro t ht
  have hx := DommaschkQA2R.poloidalLoop_mem_domain
    (R := fun _ _ => y t 0) (z := fun _ _ => y t 1) (θ := 0) (φ₀ := sign*t) (hR t ht)
  change cylPoint (y t 0) (sign*t) (y t 1) ∈ Fields.CylAlgebra.domain at hx
  have hc : ContinuousWithinAt (fun u => cylPoint (y u 0) (sign*u) (y u 1)) s t := by
    have coord (i : Fin 2) : ContinuousWithinAt (fun u => y u i) s t :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).continuousAt.comp_continuousWithinAt
        (hy t ht)
    have angle : ContinuousWithinAt (fun u : ℝ => sign*u) s t :=
      (continuous_const.mul continuous_id).continuousWithinAt
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.comp_continuousWithinAt
    apply continuousWithinAt_pi.mpr
    intro i
    fin_cases i
    · exact (coord 0).mul (Real.continuous_cos.continuousAt.comp_continuousWithinAt angle)
    · exact (coord 0).mul (Real.continuous_sin.continuousAt.comp_continuousWithinAt angle)
    · exact coord 1
  change ContinuousWithinAt (fun u => ‖DommaschkQA2R.field DommaschkQA2R.candidate
    (cylPoint (y u 0) (sign*u) (y u 1))‖) s t
  apply ContinuousWithinAt.norm
  exact (DommaschkQA2R.continuousAt_field DommaschkQA2R.candidate hx).comp_continuousWithinAt
    (f := fun u => cylPoint (y u 0) (sign*u) (y u 1)) hc

/-- If the entire prefix through the left bracket is below the height and the right
endpoint is above it, the earliest equal-height point lies strictly inside the bracket.
The conclusion allows a tangent contact at this earliest point. -/
theorem first_of_prefix_signs {f : ℝ → ℝ} {a b h : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hf : ContinuousOn f (Icc 0 b)) (below : ∀ t ∈ Icc 0 a, f t < h) (above : h < f b) :
    ∃ r ∈ Ioo a b, f r = h ∧ ∀ t ∈ Ico 0 r, f t < h := by
  have has := intermediate_value_Ioo hab.le (hf.mono (Icc_subset_Icc_left ha))
    (show h ∈ Ioo (f a) (f b) from ⟨below a ⟨ha,le_rfl⟩,above⟩)
  obtain ⟨w,hw,hew⟩ := has
  let hits := Icc 0 b ∩ f ⁻¹' {h}
  have compact : IsCompact hits := isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨r,hr⟩ := compact.exists_isLeast ⟨w, ⟨⟨ha.trans hw.1.le,hw.2.le⟩,hew⟩⟩
  have mem := hr.1.1
  have eq : f r = h := hr.1.2
  have ra : a < r := lt_of_not_ge fun he => (below r ⟨mem.1,he⟩).ne eq
  have rb := (hr.2 (show w ∈ hits from ⟨⟨ha.trans hw.1.le,hw.2.le⟩,hew⟩)).trans_lt hw.2
  refine ⟨r,⟨ra,rb⟩,eq,?_⟩
  intro t ht
  by_contra! he
  have sub := hf.mono (Icc_subset_Icc_right (ht.2.le.trans rb.le))
  obtain ⟨u,hu,eu⟩ := intermediate_value_Icc ht.1 sub
    (show h ∈ Icc (f 0) (f t) from ⟨(below 0 ⟨le_rfl,ha⟩).le,he⟩)
  have le := hr.2 (show u ∈ hits from ⟨⟨hu.1, hu.2.trans (ht.2.le.trans rb.le)⟩,eu⟩)
  exact ht.2.not_ge (le.trans hu.2)

/-- Two strict endpoint signs suffice to bracket a physical equal-height point. -/
theorem exists_on_tube {a b h sign : ℝ} {y : ℝ → Plane} {tube : ℝ → Set Plane}
    (hab : a < b) (hy : ContinuousOn y (Icc a b)) (inside : ∀ t ∈ Icc a b, y t ∈ tube t)
    (radial : ∀ t ∈ Icc a b, ∀ x ∈ tube t, 0 < x 0)
    (below : ∀ x ∈ tube a, strength (sign * a) x < h)
    (above : ∀ x ∈ tube b, h < strength (sign * b) x) :
    ∃ r ∈ Ioo a b, strength (sign * r) (y r) = h := by
  exact intermediate_value_Ioo hab.le
    (continuousOn_strength hy sign (fun t ht => radial t ht _ (inside t ht)))
    ⟨below _ (inside a ⟨le_rfl,hab.le⟩), above _ (inside b ⟨hab.le,le_rfl⟩)⟩

/-- Attach signs on the actual spatial tubes to the continuous norm of the same
field line. Separate closed tubes can be used on different parts of the prefix. -/
theorem first_on_tube {a b h sign : ℝ} {y : ℝ → Plane} {tube : ℝ → Set Plane}
    (ha : 0 ≤ a) (hab : a < b) (hy : ContinuousOn y (Icc 0 b))
    (inside : ∀ t ∈ Icc 0 b, y t ∈ tube t)
    (radial : ∀ t ∈ Icc 0 b, ∀ x ∈ tube t, 0 < x 0)
    (below : ∀ t ∈ Icc 0 a, ∀ x ∈ tube t, strength (sign * t) x < h)
    (above : ∀ x ∈ tube b, h < strength (sign * b) x) :
    ∃ r ∈ Ioo a b, strength (sign*r) (y r) = h ∧
      ∀ t ∈ Ico 0 r, strength (sign*t) (y t) < h := by
  apply first_of_prefix_signs ha hab (continuousOn_strength hy sign (fun t ht =>
    radial t ht _ (inside t ht)))
  · exact fun t ht => below t ht _ (inside t ⟨ht.1,ht.2.trans hab.le⟩)
  · exact above _ (inside b ⟨ha.trans hab.le,le_rfl⟩)

end PlasmaLean.Design.DommaschkMirrorTubeCrossing
