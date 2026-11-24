/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.WeakenLowerActionCells

/-! # Transport of a full chronological lower action cover to weaker digits -/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorActionQuadrature

/-- Match the lengths and the two physical lower columns in chronological order. -/
def blocksLowerLE : List (Block false) → List (Block false) → Bool
  | [], [] => true
  | c::cs, f::fs => lowerColumnsLE 48 c.packed f.packed && blocksLowerLE cs fs
  | _,_ => false

theorem covers_of_blocksLowerLE {coarse fine : List (Block false)} {w f : ℝ → ℝ} {h a : ℝ}
    (ok : blocksLowerLE coarse fine = true) (original : Covers false w f h a fine) :
    Covers false w f h a coarse := by
  induction coarse generalizing fine a with
  | nil => trivial
  | cons c cs ih =>
    cases fine with
    | nil => simp [blocksLowerLE] at ok
    | cons b bs =>
      simp only [blocksLowerLE,Bool.and_eq_true] at ok
      exact ⟨cells_of_lowerColumnsLE ok.1 original.1,ih ok.2 original.2⟩

theorem blocksLowerLE_append {c f c' f' : List (Block false)}
    (left : blocksLowerLE c f = true) (right : blocksLowerLE c' f' = true) :
    blocksLowerLE (c ++ c') (f ++ f') = true := by
  induction c generalizing f with
  | nil =>
    cases f with
    | nil => exact right
    | cons => simp [blocksLowerLE] at left
  | cons b bs ih =>
    cases f with
    | nil => simp [blocksLowerLE] at left
    | cons g gs =>
      simp only [blocksLowerLE,Bool.and_eq_true] at left
      simp only [List.cons_append,blocksLowerLE,Bool.and_eq_true]
      exact ⟨left.1,ih left.2⟩

end PlasmaLean.Certificates.MirrorActionQuadrature
