/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionQuadrature

/-! # Transport of physical quadrature covers on their closed interval -/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorActionQuadrature
open Set

private theorem cells_congr {u : Bool} {w f W F : ℝ → ℝ} {h a : ℝ} {n p : ℕ}
    (cells : Cells u w f h a n p)
    (same : ∀ t ∈ Icc a (a + n / 3072), W t = w t ∧ F t = f t) : Cells u W F h a n p := by
  induction n generalizing a p with
  | zero => trivial
  | succ n ih =>
    obtain ⟨c,rest⟩ := cells
    have eq : ∀ t ∈ Icc a (a + (n+1:ℝ) / 3072), W t = w t ∧ F t = f t := by
      simpa only [Nat.cast_succ] using same
    constructor
    · intro t ht
      obtain ⟨aW,aF⟩ := eq t ⟨ht.1,by linarith [ht.2,Nat.cast_nonneg (α := ℝ) n]⟩
      rw [aW,aF]
      exact c t ht
    · apply ih rest
      intro t ht
      exact eq t ⟨by linarith [ht.1],by linarith [ht.2]⟩

theorem Covers.congr_on {u : Bool} {w f W F : ℝ → ℝ} {h a : ℝ} {bs : List (Block u)}
    (cells : Covers u w f h a bs)
    (same : ∀ t ∈ Icc a (a + bs.length / 64), W t = w t ∧ F t = f t) : Covers u W F h a bs := by
  induction bs generalizing a with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨c,rest⟩ := cells
    simp only [List.length_cons,Nat.cast_succ] at same
    constructor
    · apply cells_congr c
      intro t ht
      have hi := ht.2
      norm_num at hi
      exact same t ⟨ht.1,by linarith [Nat.cast_nonneg (α := ℝ) bs.length]⟩
    · apply ih rest
      intro t ht
      exact same t ⟨by linarith [ht.1],by linarith [ht.2]⟩

end PlasmaLean.Certificates.MirrorActionQuadrature
