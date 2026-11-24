/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# A single physical trajectory on consecutive certified time slabs

Each local existence proof starts from any state in its prescribed entrance set.
Its exit set can contain a reference jump or a change of coordinates already
charged by the local verifier. At the common endpoint the construction passes
the actual state into the next existence proof. All slabs use the same
absolute-time vector field, so their one-sided derivatives agree there.
-/

@[expose] public section

namespace PlasmaLean.Fields.TrajectorySlabs

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed time slab with its time-dependent physical enclosure. -/
structure Slab (E : Type*) where
  start : ℝ
  stop : ℝ
  tube : ℝ → Set E

/-- Local field-line existence from each admissible initial state, with an exit enclosure. -/
structure Step (F : ℝ → E → E) (s : Slab E) (entry exit : Set E) : Prop where
  ordered : s.start ≤ s.stop
  solve : ∀ x ∈ entry, ∃ v : ℝ → E, v s.start = x ∧ v s.stop ∈ exit ∧
    ∀ t ∈ Icc s.start s.stop,
      HasDerivWithinAt v (F t (v t)) (Icc s.start s.stop) t ∧ v t ∈ s.tube t

/-- The time and set at each exit are the time and set at the next entrance. -/
inductive Chain (F : ℝ → E → E) : ℝ → Set E → ℝ → Set E → List (Slab E) → Prop where
  | nil (t : ℝ) (states : Set E) : Chain F t states t states []
  | cons {s : Slab E} {entry middle exit : Set E} {endTime : ℝ} {rest : List (Slab E)}
      (first : Step F s entry middle) (tail : Chain F s.stop middle endTime exit rest) :
      Chain F s.start entry endTime exit (s :: rest)

/-- The chain's final time is at least its initial time. -/
theorem Chain.ordered {F : ℝ → E → E} {a b : ℝ} {S T : Set E} {ss : List (Slab E)}
    (h : Chain F a S b T ss) : a ≤ b := by
  induction h with
  | nil => exact le_rfl
  | cons step _ ih => exact step.ordered.trans ih

/-- Each recorded slab is contained in the full time interval. -/
theorem Chain.subinterval {F : ℝ → E → E} {a b : ℝ} {S T : Set E} {ss : List (Slab E)}
    (h : Chain F a S b T ss) {s : Slab E} (hs : s ∈ ss) :
    Icc s.start s.stop ⊆ Icc a b := by
  induction h with
  | nil => simp at hs
  | cons step tail ih =>
    rcases List.mem_cons.mp hs with rfl | hm
    · exact Icc_subset_Icc_right tail.ordered
    · exact (ih hm).trans (Icc_subset_Icc_left step.ordered)

private theorem glue {F : ℝ → E → E} {a b c : ℝ} {u v : ℝ → E}
    (hab : a ≤ b) (hbc : b ≤ c) (join : u b = v b)
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (F t (u t)) (Icc a b) t)
    (hv : ∀ t ∈ Icc b c, HasDerivWithinAt v (F t (v t)) (Icc b c) t) :
    ∃ w : ℝ → E, EqOn w u (Icc a b) ∧ EqOn w v (Icc b c) ∧
      ∀ t ∈ Icc a c, HasDerivWithinAt w (F t (w t)) (Icc a c) t := by
  let w := fun t => if t ≤ b then u t else v t
  have left : EqOn w u (Icc a b) := fun _ ht => ite_eq_left ht.2
  have right : EqOn w v (Icc b c) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | h
    · simpa [w] using join
    · exact ite_eq_right h.not_ge
  refine ⟨w, left, right, fun t _ => ?_⟩
  have side {l r : ℝ} {z : ℝ → E} (he : EqOn w z (Icc l r))
      (hd : ∀ y ∈ Icc l r, HasDerivWithinAt z (F y (z y)) (Icc l r) y) :
      HasDerivWithinAt w (F t (w t)) (Icc l r) t := by
    by_cases hit : t ∈ Icc l r
    · rw [he hit]
      exact (hd t hit).congr_of_mem (fun _ h => he h) hit
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [isClosed_Icc.closure_eq])
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact (side left hu).union (side right hv)

/-- All pointwise slab enclosures hold for one solution of the physical ODE, with a
derivative within the whole interval even at internal joins and exact initial value. -/
theorem Chain.exists_trajectory {F : ℝ → E → E} {a b : ℝ} {entry exit : Set E}
    {ss : List (Slab E)} (h : Chain F a entry b exit ss) {x : E} (hx : x ∈ entry) :
    ∃ v : ℝ → E, v a = x ∧ v b ∈ exit ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt v (F t (v t)) (Icc a b) t) ∧
      ∀ s ∈ ss, ∀ t ∈ Icc s.start s.stop, v t ∈ s.tube t := by
  induction h generalizing x with
  | nil t states =>
    refine ⟨fun _ => x, rfl, hx, ?_, by simp⟩
    intro y _
    rw [Icc_self]
    exact HasFDerivWithinAt.singleton
  | @cons s entry middle exit finish rest step tail ih =>
    obtain ⟨u, start, next, first⟩ := step.solve x hx
    obtain ⟨v, join, last, ode, enclosures⟩ := ih next
    obtain ⟨w, left, right, global⟩ := glue step.ordered tail.ordered join.symm
      (fun t ht => (first t ht).1) ode
    refine ⟨w, (left (left_mem_Icc.mpr step.ordered)).trans start, ?_, global, ?_⟩
    · rwa [right (right_mem_Icc.mpr tail.ordered)]
    · intro p hp t ht
      rcases List.mem_cons.mp hp with rfl | other
      · rw [left ht]
        exact (first t ht).2
      · rw [right (tail.subinterval other ht)]
        exact enclosures p other t ht

/-- A fixed field of zero admits a constant physical state across any ordered slab. -/
theorem zero_step (a b : ℝ) (ab : a ≤ b) (S : Set E) :
    Step (fun _ _ => 0) ⟨a, b, fun _ => S⟩ S S := by
  refine ⟨ab, fun x hx => ⟨fun _ => x, rfl, hx, fun t _ => ?_⟩⟩
  exact ⟨(hasDerivAt_const t x).hasDerivWithinAt, hx⟩

/-- An inhabited entrance cannot have an empty exit for a certified chain. -/
theorem Chain.nonempty_exit {F : ℝ → E → E} {a b : ℝ} {S T : Set E} {ss : List (Slab E)}
    (h : Chain F a S b T ss) (hs : S.Nonempty) : T.Nonempty := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨v, _, hv, _⟩ := h.exists_trajectory hx
  exact ⟨v b, hv⟩

end PlasmaLean.Fields.TrajectorySlabs
