/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.DyadicTaylorModel

/-! # Covering the error interval of a dyadic Taylor model

The two children retain every nonconstant coefficient. Integer endpoint checks
therefore give coverage for every real time, including the joining boundary.
-/

@[expose] public section
namespace PlasmaLean.Certificates.TrajectoryTaylorModel

/-- Two shifted error intervals cover the original dyadic remainder interval
when the outer endpoints are covered and the two closed intervals intersect. -/
theorem dyadic_cover {bits : ℕ} {c e l u el eu : ℤ} {tail : List ℤ} {t y : ℝ}
    (left : l - el ≤ -e) (join : u - eu ≤ l + el) (right : e ≤ u + eu)
    (h : (ofDyadic bits (c :: tail) e).Mem t y) :
    (ofDyadic bits ((c+l) :: tail) el).Mem t y ∨
      (ofDyadic bits ((c+u) :: tail) eu).Mem t y := by
  simp only [mem_ofDyadic_iff, List.map_cons, QPoly.eval_cons, Rat.cast_intCast,
    Rat.cast_add, Int.cast_add, abs_le] at h ⊢
  have hl : (l : ℝ) - el ≤ -e := by exact_mod_cast left
  have hj : (u : ℝ) - eu ≤ l + el := by exact_mod_cast join
  have hr : (e : ℝ) ≤ u + eu := by exact_mod_cast right
  by_cases cut : (2 : ℝ) ^ bits * y - (c +
      t * QPoly.eval (tail.map fun (a : ℤ) => (a : ℚ)) t) ≤ (l : ℝ) + el
  · exact Or.inl ⟨by linarith [h.1], by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith [h.2]⟩

end PlasmaLean.Certificates.TrajectoryTaylorModel
