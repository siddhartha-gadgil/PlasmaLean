/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameChain
public import PlasmaLean.Theory.Fields.TrajectorySlabObservable

/-! # Pointwise observables on an initial part of a packed trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameSlabs
open Set

/-- A predicate certified on every point of every listed physical tube. -/
def OnTubes (P : ℝ → Plane → Prop) : State → ℝ → List Step → Prop
  | _, _, [] => True
  | s, a, r :: rs =>
    (∀ t ∈ Icc a (a + 1 / 64), ∀ x ∈ (physicalSlab s r a).tube t, P t x) ∧
    OnTubes P (next r) (a + 1 / 64) rs

/-- One certificate at the absolute time i/64 and the adjacent suffix give a
certificate for the extended list. Integer indexing avoids large clock terms. -/
theorem OnTubes.cons_at {P : ℝ → Plane → Prop} {s : State} {r : Step} {rs : List Step} (i : ℕ)
    (head : ∀ t ∈ Icc (i / 64 : ℝ) (((i + 1 : ℕ) : ℝ) / 64),
      ∀ x ∈ (physicalSlab s r (i / 64)).tube t, P t x)
    (tail : OnTubes P (next r) (((i + 1 : ℕ) : ℝ) / 64) rs) :
    OnTubes P s (i / 64) (r :: rs) := by
  have eq : (i : ℝ) / 64 + 1 / 64 = ((i + 1 : ℕ) : ℝ) / 64 := by push_cast; ring
  exact ⟨by simpa only [eq] using head, eq ▸ tail⟩

/-- A prefix certificate applies to the same enclosed path even if its
trajectory was supplied on a longer list. All endpoints are included. -/
theorem OnTubes.on_prefix {P : ℝ → Plane → Prop} {s : State} {a : ℝ}
    {pre post : List Step} {y : ℝ → Plane} (cert : OnTubes P s a pre) (entry : P a (y a))
    (inside : ∀ u ∈ physicalSlabs s a (pre ++ post), ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t) :
    ∀ t ∈ Icc a (a + pre.length / 64), P t (y t) := by
  induction pre generalizing s a with
  | nil => simpa using entry
  | cons r rs ih =>
    have head : ∀ t ∈ Icc a (a + 1 / 64), P t (y t) :=
      fun t ht => cert.1 t ht _ (inside _ List.mem_cons_self t ht)
    have tail := ih cert.2 (head _ ⟨by linarith, le_rfl⟩)
      (fun u hu => inside u (List.mem_cons_of_mem _ hu))
    intro t ht
    by_cases early : t ≤ a + 1 / 64
    · exact head t ⟨ht.1, early⟩
    · apply tail t
      constructor
      · exact (lt_of_not_ge early).le
      · have endpoint := ht.2
        rw [List.length_cons, Nat.cast_add, Nat.cast_one] at endpoint
        linarith

/-- When the certified prefix contains a slab, its first tube proves the
observable at the common entry too. -/
theorem OnTubes.on_nonempty_prefix {P : ℝ → Plane → Prop} {s : State} {a : ℝ}
    {pre post : List Step} {y : ℝ → Plane} (cert : OnTubes P s a pre) (hne : pre ≠ [])
    (inside : ∀ u ∈ physicalSlabs s a (pre ++ post), ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t) :
    ∀ t ∈ Icc a (a + pre.length / 64), P t (y t) := by
  cases pre with
  | nil => contradiction
  | cons r rs =>
    apply cert.on_prefix _ inside
    have start : a ∈ Icc a (a + 1 / 64) := ⟨le_rfl, by linarith⟩
    exact cert.1 a start _ (inside _ List.mem_cons_self a start)

/-- Row certificates and a single continuous final bracket locate the earliest
level contact along an actual enclosed trajectory. The observable can vary
with both elapsed time and spatial position. -/
theorem first_contact_after_prefix {G : ℝ → Plane → ℝ} {h a b : ℝ} {s : State}
    {pre post : List Step} {y : ℝ → Plane}
    (cert : OnTubes (fun t x => G t x < h) s a pre) (entry : G a (y a) < h)
    (inside : ∀ u ∈ physicalSlabs s a (pre ++ post), ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t)
    (ordered : a + pre.length / 64 < b)
    (cont : ContinuousOn (fun t => G t (y t)) (Icc (a + pre.length / 64) b))
    (above : h < G b (y b)) :
    ∃ c ∈ Ioo (a + pre.length / 64) b, G c (y c) = h ∧ ∀ t ∈ Ico a c, G t (y t) < h :=
  Fields.TrajectorySlabs.first_contact_in_bracket (le_add_of_nonneg_right (by positivity))
    ordered (cert.on_prefix entry inside) cont above

end PlasmaLean.Certificates.PositionFrameSlabs
