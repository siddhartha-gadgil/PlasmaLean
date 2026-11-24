/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameObservables

/-! # Relations between two physical paths on a common azimuthal clock -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameSlabs
open Set

/-- Each pair of rows certifies the relation at the same time and on the two
independent spatial tubes. Unequal numbers of certified rows are rejected. -/
def OnPairedTubes (P : ℝ → Plane → Plane → Prop) : State → State → ℝ → List Step → List Step → Prop
  | _, _, _, [], [] => True
  | s, v, a, r :: rs, q :: qs =>
    (∀ t ∈ Icc a (a + 1 / 64), ∀ x ∈ (physicalSlab s r a).tube t,
      ∀ y ∈ (physicalSlab v q a).tube t, P t x y) ∧
      OnPairedTubes P (next r) (next q) (a + 1 / 64) rs qs
  | _, _, _, _, _ => False

theorem OnPairedTubes.cons_at {P : ℝ → Plane → Plane → Prop} {s v : State}
    {r q : Step} {rs qs : List Step} (i : ℕ)
    (head : ∀ t ∈ Icc (i / 64 : ℝ) (((i + 1 : ℕ) : ℝ) / 64),
      ∀ x ∈ (physicalSlab s r (i / 64)).tube t,
      ∀ y ∈ (physicalSlab v q (i / 64)).tube t, P t x y)
    (tail : OnPairedTubes P (next r) (next q) (((i + 1 : ℕ) : ℝ) / 64) rs qs) :
    OnPairedTubes P s v (i / 64) (r :: rs) (q :: qs) := by
  have eq : (i : ℝ) / 64 + 1 / 64 = ((i + 1 : ℕ) : ℝ) / 64 := by push_cast; ring
  exact ⟨by simpa only [eq] using head, eq ▸ tail⟩

/-- Two independent paths may continue through different suffixes. Every time in the
closed certified prefix, including each row boundary, satisfies the relation. -/
theorem OnPairedTubes.on_prefix {P : ℝ → Plane → Plane → Prop} {s v : State} {a : ℝ}
    {rs qs moreR moreQ : List Step} {x y : ℝ → Plane}
    (cert : OnPairedTubes P s v a rs qs) (entry : P a (x a) (y a))
    (inner : ∀ u ∈ physicalSlabs s a (rs ++ moreR), ∀ t ∈ Icc u.start u.stop, x t ∈ u.tube t)
    (outer : ∀ u ∈ physicalSlabs v a (qs ++ moreQ), ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t) :
    ∀ t ∈ Icc a (a + rs.length / 64), P t (x t) (y t) := by
  induction rs generalizing s v a qs with
  | nil => simpa using entry
  | cons r rs ih =>
    cases qs with
    | nil => exact False.elim cert
    | cons q qs =>
      have head (t : ℝ) (ht : t ∈ Icc a (a + 1 / 64)) : P t (x t) (y t) :=
        cert.1 t ht _ (inner _ List.mem_cons_self t ht) _ (outer _ List.mem_cons_self t ht)
      have tail := ih cert.2 (head _ ⟨by linarith, le_rfl⟩)
        (fun u hu => inner u (List.mem_cons_of_mem _ hu))
        (fun u hu => outer u (List.mem_cons_of_mem _ hu))
      intro t ht
      by_cases h : t ≤ a + 1 / 64
      · exact head t ⟨ht.1, h⟩
      · apply tail t
        refine ⟨(lt_of_not_ge h).le, ?_⟩
        have stop := ht.2
        rw [List.length_cons, Nat.cast_add, Nat.cast_one] at stop
        linarith

theorem OnPairedTubes.on_nonempty_prefix {P : ℝ → Plane → Plane → Prop} {s v : State} {a : ℝ}
    {rs qs moreR moreQ : List Step} {x y : ℝ → Plane}
    (cert : OnPairedTubes P s v a rs qs) (hne : rs ≠ [])
    (inner : ∀ u ∈ physicalSlabs s a (rs ++ moreR), ∀ t ∈ Icc u.start u.stop, x t ∈ u.tube t)
    (outer : ∀ u ∈ physicalSlabs v a (qs ++ moreQ), ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t) :
    ∀ t ∈ Icc a (a + rs.length / 64), P t (x t) (y t) := by
  cases rs with
  | nil => contradiction
  | cons r rs =>
    cases qs with
    | nil => exact False.elim cert
    | cons q qs =>
      apply cert.on_prefix _ inner outer
      have ha : a ∈ Icc a (a + 1 / 64) := ⟨le_rfl, by linarith⟩
      exact cert.1 a ha _ (inner _ List.mem_cons_self a ha) _ (outer _ List.mem_cons_self a ha)

end PlasmaLean.Certificates.PositionFrameSlabs
