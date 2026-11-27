/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameWide
public import PlasmaLean.Certificates.PositionFrameChain

/-! # A physical field line through a chain of wide position-frame steps

The steps are checked by `PositionFrameWide.valid`, which has no small-radius
limits. The field bounds and the slabs are those of the narrow chain.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameWideChain

open Set PositionFrameSlabs

/-- Every record is a valid wide step from the state left by its predecessor,
and the last record leaves the declared final state. -/
def Steps : State → List Step → State → Prop
  | s, [], e => s = e
  | s, r :: rs, e => PositionFrameWide.valid s r = true ∧ Steps (next r) rs e

/-- Executable form of the same check, returning the final state. -/
def run : State → List Step → Bool × State
  | s, [] => (true, s)
  | s, r :: rs => (PositionFrameWide.valid s r && (run (next r) rs).1, (run (next r) rs).2)

theorem Steps.of_run {s e : State} {rows : List Step} (h : run s rows = (true, e)) :
    Steps s rows e := by
  induction rows generalizing s with
  | nil => exact congrArg Prod.snd h
  | cons r rs ih =>
    have check := congrArg Prod.fst h
    change (PositionFrameWide.valid s r && (run (next r) rs).1) = true at check
    obtain ⟨ok,tail⟩ := Bool.and_eq_true_iff.mp check
    have endState := congrArg Prod.snd h
    change (run (next r) rs).2 = e at endState
    exact ⟨ok, ih (Prod.ext tail endState)⟩

/-- When all analytic inputs have been discharged for the records, the wide
checks prove one physical ODE chain on exactly `rows.length / 64` units of angle. -/
theorem Steps.physical {domain : RegularityDomain} {s e : State} {a : ℝ} {rows : List Step}
    {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (h : Steps s rows e) (bounds : FieldBoundsOn F J s a rows domain) :
    Fields.TrajectorySlabs.Chain F a (stateSet s) (a + rows.length/64) (stateSet e)
      (physicalSlabs s a rows) := by
  induction rows generalizing s a with
  | nil =>
    change s = e at h
    cases h
    simpa only [List.length_nil, Nat.cast_zero, zero_div, add_zero, physicalSlabs] using
      Fields.TrajectorySlabs.Chain.nil (F := F) a (stateSet _)
  | cons r rs ih =>
    have step := PositionFrameWide.physical_step_on h.1 bounds.1
    have rest := ih h.2 bounds.2
    have time : (a+1/64) + rs.length/64 = a + (r::rs).length/64 := by
      rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    rw [← time]
    exact .cons step rest

/-- Every entry point launches one solution of the ODE through all the wide
slabs, ending in the declared final set and lying in every recorded tube. -/
theorem Steps.trajectory {domain : RegularityDomain} {s e : State} {a : ℝ} {rows : List Step}
    {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (h : Steps s rows e) (bounds : FieldBoundsOn F J s a rows domain)
    {x : Plane} (entry : x ∈ stateSet s) :
    ∃ v : ℝ → Plane, v a = x ∧ v (a+rows.length/64) ∈ stateSet e ∧
      (∀ t ∈ Icc a (a+rows.length/64),
        HasDerivWithinAt v (F t (v t)) (Icc a (a+rows.length/64)) t) ∧
      ∀ slab ∈ physicalSlabs s a rows,
        ∀ t ∈ Icc slab.start slab.stop, v t ∈ slab.tube t :=
  (h.physical bounds).exists_trajectory entry

/-- The same statement with the number of steps named, as in the narrow chain. -/
theorem Steps.trajectory_of_length {domain : RegularityDomain} {s e : State} {a : ℝ}
    {rows : List Step} {n : ℕ} {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (h : Steps s rows e) (len : rows.length = n) (bounds : FieldBoundsOn F J s a rows domain)
    {x : Plane} (entry : x ∈ stateSet s) :
    ∃ v : ℝ → Plane, v a = x ∧ v (a+n/64) ∈ stateSet e ∧
      (∀ t ∈ Icc a (a+n/64), HasDerivWithinAt v (F t (v t)) (Icc a (a+n/64)) t) ∧
      ∀ slab ∈ physicalSlabs s a rows,
        ∀ t ∈ Icc slab.start slab.stop, v t ∈ slab.tube t := by
  subst len
  exact h.trajectory bounds entry

end PlasmaLean.Certificates.PositionFrameWideChain
