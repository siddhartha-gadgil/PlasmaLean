/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameObservables

/-! # Restrict an observable certificate to the first slabs of its physical archive -/

@[expose] public section
namespace PlasmaLean.Certificates.PositionFrameSlabs
open Set

/-- Keeping the first slabs preserves their entry state, physical clocks and pointwise predicate. -/
theorem OnTubes.take {P : ℝ → Plane → Prop} {s : State} {a : ℝ} {rs : List Step}
    (cert : OnTubes P s a rs) (n : ℕ) : OnTubes P s a (rs.take n) := by
  induction n generalizing s a rs with
  | zero => trivial
  | succ n ih =>
    cases rs with
    | nil => trivial
    | cons r rs => exact ⟨cert.1, ih cert.2⟩

/-- A shorter observation window can be applied to a longer physical path without changing it. -/
theorem OnTubes.on_initial {P : ℝ → Plane → Prop} {s : State} {a : ℝ} {rs : List Step}
    {y : ℝ → Plane} {n : ℕ} (cert : OnTubes P s a (rs.take n)) (hn : 0 < n)
    (size : n ≤ rs.length)
    (inside : ∀ u ∈ physicalSlabs s a rs, ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t) :
    ∀ t ∈ Icc a (a + n / 64), P t (y t) := by
  have len : (rs.take n).length = n := by simp [List.length_take, Nat.min_eq_left size]
  have nonempty : rs.take n ≠ [] := by
    intro h
    rw [h, List.length_nil] at len
    omega
  have all := cert.on_nonempty_prefix (post := rs.drop n) nonempty
    (by simpa only [List.take_append_drop] using inside)
  simpa only [len] using all

end PlasmaLean.Certificates.PositionFrameSlabs
