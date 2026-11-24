/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PolyInterval

/-! # Rational Taylor models for checked trajectory residuals
A model consists of a rational polynomial in normalized time and a uniform error.
Equations and inequalities for the proposed output coefficients can be checked
independently of the real functions to which a model is applied.
-/

@[expose] public section

namespace PlasmaLean.Certificates.TrajectoryTaylorModel
open QPoly

/-- Coefficient ℓ¹ norm of a polynomial in ascending powers. -/
def magnitude : List ℚ → ℚ
  | [] => 0
  | a :: p => |a| + magnitude p

/-- The ℓ¹ coefficient norm encloses every evaluation on the closed unit interval. -/
theorem abs_eval_le {s : ℝ} (hs : |s| ≤ 1) (p : List ℚ) :
    |eval p s| ≤ (magnitude p : ℝ) := by
  induction p with
  | nil => simp [magnitude]
  | cons a p ih =>
    change |(a : ℝ) + s * eval p s| ≤ ((|a| + magnitude p : ℚ) : ℝ)
    push_cast
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add le_rfl ((mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans
      (by simpa using ih))

/-- Difference of proposed and exact polynomials. -/
def difference (p q : List ℚ) : List ℚ := add p (scale (-1) q)

@[simp] theorem eval_difference (p q : List ℚ) (s : ℝ) :
    eval (difference p q) s = eval p s - eval q s := by simp [difference, sub_eq_add_neg]

/-- A polynomial and a proposed nonnegative radius. Membership witnesses imply nonnegativity. -/
structure Model where
  poly : List ℚ
  radius : ℚ

/-- The value is within the certified radius at the given normalized time. -/
def Model.Mem (m : Model) (s y : ℝ) : Prop := |y - eval m.poly s| ≤ (m.radius : ℝ)

/-- Exact point model. -/
def exactPoly (p : List ℚ) : Model := ⟨p, 0⟩

theorem mem_exact (p : List ℚ) (s : ℝ) : (exactPoly p).Mem s (eval p s) := by
  simp [exactPoly, Model.Mem]

/-- Change coefficients, accounting for the entire coefficient difference. -/
theorem enclose {a c : Model} {s x : ℝ} (hs : |s| ≤ 1) (ha : a.Mem s x)
    (hc : a.radius + magnitude (difference a.poly c.poly) ≤ c.radius) : c.Mem s x := by
  have h := abs_eval_le hs (difference a.poly c.poly)
  rw [eval_difference] at h
  calc
    |x - eval c.poly s| ≤ |x - eval a.poly s| + |eval a.poly s - eval c.poly s| :=
      abs_sub_le _ _ _
    _ ≤ (a.radius : ℝ) + magnitude (difference a.poly c.poly) := add_le_add ha h
    _ ≤ c.radius := by exact_mod_cast hc

/-- Sum of two models before optional coefficient rounding. -/
def addModel (a b : Model) : Model := ⟨add a.poly b.poly, a.radius + b.radius⟩

theorem mem_add {a b : Model} {s x y : ℝ} (ha : a.Mem s x) (hb : b.Mem s y) :
    (addModel a b).Mem s (x + y) := by
  change |x + y - eval (add a.poly b.poly) s| ≤ ((a.radius + b.radius : ℚ) : ℝ)
  rw [eval_add, show x + y - (eval a.poly s + eval b.poly s) =
    (x - eval a.poly s) + (y - eval b.poly s) by ring, Rat.cast_add]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

/-- Exact product polynomial with a uniform input-error allowance. -/
def mulModel (a b : Model) : Model :=
  ⟨mul a.poly b.poly, a.radius * (magnitude b.poly + b.radius) + b.radius * magnitude a.poly⟩

theorem mem_mul {a b : Model} {s x y : ℝ} (hs : |s| ≤ 1)
    (ha : a.Mem s x) (hb : b.Mem s y) : (mulModel a b).Mem s (x * y) := by
  have hy : |y| ≤ (magnitude b.poly : ℝ) + b.radius := by
    calc
      |y| = |eval b.poly s + (y - eval b.poly s)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_eval_le hs _) hb)
  change |x * y - eval (mul a.poly b.poly) s| ≤ _
  rw [eval_mul, show x * y - eval a.poly s * eval b.poly s =
    (x - eval a.poly s) * y + (y - eval b.poly s) * eval a.poly s by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  simpa only [mulModel, Rat.cast_add, Rat.cast_mul] using
    add_le_add (mul_le_mul ha hy (abs_nonneg y) ((abs_nonneg _).trans ha))
      (mul_le_mul hb (abs_eval_le hs _) (abs_nonneg _) ((abs_nonneg _).trans hb))

/-- Membership of a rounded and truncated product is certified by a rational inequality. -/
theorem mem_product_fit {a b c : Model} {s x y : ℝ} (hs : |s| ≤ 1)
    (ha : a.Mem s x) (hb : b.Mem s y)
    (hc : (mulModel a b).radius + magnitude (difference (mul a.poly b.poly) c.poly) ≤ c.radius) :
    c.Mem s (x * y) := enclose hs (mem_mul hs ha hb) hc

end PlasmaLean.Certificates.TrajectoryTaylorModel
