/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorSublevelAction

/-! # Sublevel arclength from directed panel lengths and parallel speeds

Upper bounds require a cover. Lower bounds require disjoint panels inside the well.
The upper test includes a tie at speed zero. A positive lower threshold ensures
that the clipped square root cannot include points above the mirror height.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Kinetic.MirrorSublevelPartition
open Set MeasureTheory MirrorSublevelAction

/-- Equality at a positive speed threshold belongs to its sublevel set. -/
theorem sublevel_iff_speed {B h v : ℝ} (hv : 0 < v) :
    B ≤ h - v^2 / 2 ↔ v ≤ Real.sqrt (2 * (h-B)) := by
  rw [Real.le_sqrt' hv]
  constructor <;> intro h' <;> linarith

/-- Above the mirror height the clipped speed is zero, although the field
sublevel at speed zero is empty. Counting these points on a lower sum is invalid. -/
theorem zero_lower_counterexample {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    sublevelLength μ (fun _ => 2) 1 = 0 ∧
      μ.real { _x : X | 0 ≤ Real.sqrt (2 * ((1 : ℝ) - 2)) } = 1 := by
  norm_num [sublevelLength, Real.sqrt_nonneg]

/-- Add the panel weights whose speed witness reaches the closed threshold. -/
def tailWeight {ι : Type*} [Fintype ι] (speed weight : ι → ℝ) (v : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => v ≤ speed i), weight i

/-- A finite cover by upper speed and arclength witnesses bounds the sublevel from above. -/
theorem upper {X ι : Type*} [MeasurableSpace X] [Fintype ι] (μ : Measure X)
    [IsFiniteMeasure μ] {region : Set X} (region_meas : MeasurableSet region)
    (panel : ι → Set X) (cover : region ⊆ ⋃ i, panel i) {B : X → ℝ} {h v : ℝ}
    (speed weight : ι → ℝ)
    (cap : ∀ i, ∀ x ∈ panel i, Real.sqrt (2 * (h - B x)) ≤ speed i)
    (length : ∀ i, μ.real (panel i) ≤ weight i) :
    sublevelLength (μ.restrict region) B (h - v^2/2) ≤ tailWeight speed weight v := by
  classical
  let selected := Finset.univ.filter (fun i => v ≤ speed i)
  have inside : {x | B x ≤ h - v^2/2} ∩ region ⊆ ⋃ i ∈ selected, panel i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (cover hx.2)
    have hs : v ≤ Real.sqrt (2 * (h - B x)) :=
      Real.le_sqrt_of_sq_le (by linarith only [show B x ≤ h - v^2/2 from hx.1])
    exact Set.mem_iUnion₂.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.trans (cap i x hi)⟩, hi⟩
  rw [sublevelLength, measureReal_restrict_apply' region_meas]
  exact (measureReal_mono inside (measure_ne_top μ _)).trans
    ((measureReal_biUnion_finset_le selected panel).trans (Finset.sum_le_sum fun i _ => length i))

/-- Disjoint measurable panels with lower witnesses give the reverse inequality at v>0. -/
theorem lower {X ι : Type*} [MeasurableSpace X] [Fintype ι] (μ : Measure X)
    [IsFiniteMeasure μ] {region : Set X} (region_meas : MeasurableSet region)
    (panel : ι → Set X) (inside : ∀ i, panel i ⊆ region)
    (meas : ∀ i, MeasurableSet (panel i))
    (disj : Pairwise (fun i j => Disjoint (panel i) (panel j)))
    {B : X → ℝ} {h v : ℝ} (hv : 0 < v) (speed weight : ι → ℝ)
    (floor : ∀ i, ∀ x ∈ panel i, speed i ≤ Real.sqrt (2 * (h - B x)))
    (length : ∀ i, weight i ≤ μ.real (panel i)) :
    tailWeight speed weight v ≤ sublevelLength (μ.restrict region) B (h - v^2/2) := by
  classical
  let selected := Finset.univ.filter (fun i => v ≤ speed i)
  have sub : (⋃ i ∈ selected, panel i) ⊆ {x | B x ≤ h - v^2/2} ∩ region := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨(sublevel_iff_speed hv).mpr ((Finset.mem_filter.mp hi).2.trans (floor i x hx)),
      inside i hx⟩
  rw [sublevelLength, measureReal_restrict_apply' region_meas]
  calc
    _ ≤ ∑ i ∈ selected, μ.real (panel i) := Finset.sum_le_sum fun i _ => length i
    _ = μ.real (⋃ i ∈ selected, panel i) := (measureReal_biUnion_finset
      (fun _ _ _ _ hne => disj hne) (fun i _ => meas i)).symm
    _ ≤ _ := measureReal_mono sub

end PlasmaLean.Kinetic.MirrorSublevelPartition
