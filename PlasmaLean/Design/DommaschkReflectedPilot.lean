/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkReflectedPath
public import PlasmaLean.Design.DommaschkPositionFramesFwd
public import PlasmaLean.Certificates.PositionFrameChain

/-! # Positive cylindrical radius on the full pilot archive and its reflected prefixes -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkReflectedPilot

open Certificates.PositionFrameSlabs Certificates.TrajectoryTaylorModel Set

/-- The two inexpensive conditions used by the physical mirror-bracket radius proof. -/
def radialCheck (r : Step) : Bool :=
  leQ (magnitude (difference (polynomial r 0) [1])) (1 / 2) && r.physicalOut.ble (2 ^ 78)

/-- This coordinate check covers every elapsed angle and every point in every tube. -/
theorem tubes {rows : List Step} (valid : ∀ r ∈ rows, radialCheck r = true) (s : State) (a : ℝ) :
    ∀ slab ∈ physicalSlabs s a rows, ∀ t ∈ Icc slab.start slab.stop,
      ∀ p ∈ slab.tube t, 0 < p 0 := by
  induction rows generalizing s a with
  | nil => simp [physicalSlabs]
  | cons r rs ih =>
    intro slab hs t ht p hp
    change slab ∈ physicalSlab s r a :: physicalSlabs (next r) (a + 1 / 64) rs at hs
    rcases List.mem_cons.mp hs with eq | later
    · subst slab
      obtain ⟨radius,error⟩ := Bool.and_eq_true_iff.mp (valid r (List.mem_cons_self ..))
      exact DommaschkMirrorBracketSlab.positive_radius ht hp (leQ_true.mp radius)
        (Nat.le_of_ble_eq_true error)
    · exact ih (fun q hq => valid q (List.mem_cons_of_mem _ hq)) _ _ _ later t ht p hp

set_option maxRecDepth 2048 in
/-- Every one of the 391 forward rows in the tracked u=0.470 archive is radial-positive. -/
theorem archive : DommaschkPositionFramesFwd.blocks.flatten.all radialCheck = true := by
  with_unfolding_all rfl

/-- Positive radius is available uniformly on any prefix taken from the physical archive. -/
theorem prefix_positive (n : ℕ) (s : State) (a : ℝ) :
    ∀ slab ∈ physicalSlabs s a (DommaschkPositionFramesFwd.blocks.flatten.take n),
      ∀ t ∈ Icc slab.start slab.stop, ∀ p ∈ slab.tube t, 0 < p 0 :=
  tubes (fun r hr => List.all_eq_true.mp archive r (List.mem_of_mem_take hr)) s a

end PlasmaLean.Design.DommaschkReflectedPilot
