/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.TrajectorySlabs
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Observables on a chain of physical trajectory slabs -/

@[expose] public section
namespace PlasmaLean.Fields.TrajectorySlabs

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every time strictly after entry belongs to a slab of a chronological chain.
This also applies when some slabs have zero duration. -/
theorem Chain.covers_Ioc {F : ℝ → E → E} {a b : ℝ} {S T : Set E} {ss : List (Slab E)}
    (chain : Chain F a S b T ss) {t : ℝ} (ht : t ∈ Ioc a b) :
    ∃ s ∈ ss, t ∈ Icc s.start s.stop := by
  induction chain with
  | nil => exact (ht.1.not_ge ht.2).elim
  | @cons s _ _ _ _ _ step tail ih =>
    by_cases before : t ≤ s.stop
    · exact ⟨s, List.mem_cons_self, ht.1.le, before⟩
    · obtain ⟨slab, mem, time⟩ := ih ⟨lt_of_not_ge before, ht.2⟩
      exact ⟨slab, List.mem_cons_of_mem _ mem, time⟩

/-- Pointwise information on each tube holds on the whole enclosed path.
The initial value also covers the degenerate empty chain. -/
theorem Chain.property_on_Icc {F : ℝ → E → E} {a b : ℝ} {S T : Set E} {ss : List (Slab E)}
    (chain : Chain F a S b T ss) {y : ℝ → E} {P : ℝ → E → Prop}
    (initial : P a (y a))
    (inside : ∀ s ∈ ss, ∀ t ∈ Icc s.start s.stop, y t ∈ s.tube t)
    (bound : ∀ s ∈ ss, ∀ t ∈ Icc s.start s.stop, ∀ x ∈ s.tube t, P t x) :
    ∀ t ∈ Icc a b, P t (y t) := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | after
  · exact initial
  · obtain ⟨s, hs, time⟩ := chain.covers_Ioc ⟨after, ht.2⟩
    exact bound s hs t time _ (inside s hs t time)

/-- A strictly sublevel prefix and continuity on the final bracket suffice to
locate the earliest level contact. No regularity of the observable before that
bracket is needed. -/
theorem first_contact_in_bracket {f : ℝ → ℝ} {a l r h : ℝ} (ordered : a ≤ l) (lr : l < r)
    (below : ∀ t ∈ Icc a l, f t < h) (cont : ContinuousOn f (Icc l r)) (above : h < f r) :
    ∃ c ∈ Ioo l r, f c = h ∧ ∀ t ∈ Ico a c, f t < h := by
  have left := below l ⟨ordered, le_rfl⟩
  obtain ⟨w, hw, fw⟩ := intermediate_value_Ioo lr.le cont (show h ∈ Ioo (f l) (f r) from
    ⟨left, above⟩)
  let hits := Icc l r ∩ f ⁻¹' {h}
  have compact : IsCompact hits := isCompact_Icc.of_isClosed_subset
    (cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨c, hc⟩ := compact.exists_isLeast ⟨w, ⟨⟨hw.1.le, hw.2.le⟩, fw⟩⟩
  have eq : f c = h := hc.1.2
  have lc : l < c := lt_of_le_of_ne hc.1.1.1 (fun e => left.ne (e ▸ eq))
  have cr : c < r := (hc.2 (show w ∈ hits from ⟨⟨hw.1.le, hw.2.le⟩, fw⟩)).trans_lt hw.2
  refine ⟨c, ⟨lc, cr⟩, eq, ?_⟩
  intro t ht
  by_cases early : t ≤ l
  · exact below t ⟨ht.1, early⟩
  · have lt' : l ≤ t := (lt_of_not_ge early).le
    by_contra! high
    obtain ⟨u, hu, fu⟩ := intermediate_value_Icc lt'
      (cont.mono (Icc_subset_Icc_right (ht.2.trans cr).le)) (show h ∈ Icc (f l) (f t) from
        ⟨left.le, high⟩)
    have uc := hc.2 (show u ∈ hits from ⟨⟨hu.1, hu.2.trans (ht.2.trans cr).le⟩, fu⟩)
    exact ht.2.not_ge (uc.trans hu.2)

end PlasmaLean.Fields.TrajectorySlabs
