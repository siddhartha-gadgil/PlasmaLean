/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBackwardPrefix

/-! # Uniform physical error on a certified frame prefix

The radius cap is compared with each row in the stored trajectory. Time and the
trajectory remain continuous across changes of the reference polynomial.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkBackwardPrefix
open Certificates.PositionFrameSlabs

private theorem reference_of_slab {s : State} {a : ℝ} {rows : List Step}
    {slab : Fields.TrajectorySlabs.Slab Plane} (hs : slab ∈ physicalSlabs s a rows) :
    ∃ r ∈ rows, ∀ t y, y ∈ slab.tube t →
      dist y (reference slab.start r t) ≤ r.physicalOut / (2 : ℝ)^80 := by
  induction rows generalizing s a with
  | nil => simp [physicalSlabs] at hs
  | cons r tail ih =>
    rcases List.mem_cons.mp hs with rfl | rest
    · exact ⟨r,List.Mem.head _,fun _ _ h => h.2⟩
    · obtain ⟨q,hq,h⟩ := ih rest
      exact ⟨q,List.Mem.tail _ hq,h⟩

/-- A uniform integer cap on every outgoing radius bounds the real error on
every closed slab of the same physical trajectory. -/
theorem tube_error {rows : List Step} {s : State} {a : ℝ} {cap : ℕ} {path : ℝ → Plane}
    (bounds : ∀ r ∈ rows, r.physicalOut ≤ cap)
    (inside : ∀ slab ∈ physicalSlabs s a rows, ∀ t ∈ Set.Icc slab.start slab.stop,
      path t ∈ slab.tube t) :
    ∀ slab ∈ physicalSlabs s a rows, ∃ r ∈ rows, ∀ t ∈ Set.Icc slab.start slab.stop,
      dist (path t) (reference slab.start r t) ≤ cap / (2 : ℝ)^80 := by
  intro slab hs
  obtain ⟨r,hr,h⟩ := reference_of_slab hs
  refine ⟨r,hr,fun t ht => (h t _ (inside slab hs t ht)).trans ?_⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast bounds r hr) (by positivity)

end PlasmaLean.Design.DommaschkBackwardPrefix
