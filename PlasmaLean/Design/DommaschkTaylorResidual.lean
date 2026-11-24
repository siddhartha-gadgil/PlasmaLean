/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceTaylor

/-! # Reference-curve residual polynomials

The normalized reference slope and the field numerator are evaluated in the
same clock. Subtraction happens in the polynomial before the residual is bounded.
-/

@[expose] public section
namespace PlasmaLean.Design.TaylorResidual
open Certificates.TrajectoryTaylorModel Certificates.QPoly DommaschkBounceTaylor

/-- Negation preserves the uniform model error radius. -/
def neg (m : Model) : Model := ⟨scale (-1) m.poly, m.radius⟩

theorem neg_mem {m : Model} {t v : ℝ} (h : m.Mem t v) : (neg m).Mem t (-v) := by
  change |-v - eval (scale (-1) m.poly) t| ≤ _
  rw [eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_sub_neg, abs_sub_comm]
  exact h

/-- Angular slope of the central polynomial with affine clock of rate k. -/
def slope (k : ℚ) (p : Model) : Model := exactPoly (scale k (deriv p.poly))

theorem slope_mem (k : ℚ) (p : Model) (s : ℝ) :
    (slope k p).Mem s ((k : ℝ) * eval (deriv p.poly) s) := by
  simpa only [slope, eval_scale] using mem_exact (scale k (deriv p.poly)) s

/-- Signed defect numerator for the increasing physical angular clock. -/
def numerator (F : Format) (k : ℚ) (N D p : Model) : Model :=
  F.add N (neg (F.mul (slope k p) D))

theorem numerator_mem {F : Format} (k : ℚ) (p : Model) {N D : Model} {s v d : ℝ}
    (hs : |s| ≤ 1) (hv : N.Mem s v) (hd : D.Mem s d) :
    (numerator F k N D p).Mem s (v - ((k : ℝ) * eval (deriv p.poly) s) * d) := by
  simpa only [numerator, sub_eq_add_neg] using
    F.add_mem hs hv (neg_mem (F.mul_mem hs (slope_mem k p s) hd))

/-- Lower Horner checks on a partition for the polynomial and its negative
give a uniform absolute bound after adding the model error. -/
theorem abs_bound {m : Model} {q : ℚ} {t y : ℝ} {pts : List ℚ} (ht : |t| ≤ 1)
    (h : m.Mem t y)
    (lo : checkOn m.poly (m.radius - q) (-1) 1 pts = true)
    (hi : checkOn (scale (-1) m.poly) (m.radius - q) (-1) 1 pts = true) :
    |y| ≤ (q : ℝ) := by
  have hI : t ∈ Set.Icc ((-1 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
    simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using abs_le.mp ht
  have left := checkOn_sound lo t hI
  have right := checkOn_sound hi t hI
  rw [eval_scale] at right
  push_cast at left right
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PlasmaLean.Design.TaylorResidual
