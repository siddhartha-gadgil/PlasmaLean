/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeLowerAction
public import PlasmaLean.Certificates.PolyInterval

/-! # A polynomial lower bound for the physical mirror action density -/

@[expose] public section
namespace PlasmaLean.Certificates.PolynomialActionFloor

/-- A denominator-cleared test avoids evaluating a square root at each time.
`G/P` bounds the physical squared-strength gap from below, and `U = D²w²`. -/
theorem point {h B P G U D w p : ℝ} (hh : 0 < h) (hb : 0 ≤ B)
    (hp : 0 < P) (hd : 0 < D) (hw : 0 ≤ w) (gap : G ≤ P * (h ^ 2 - B ^ 2))
    (weight : U = D ^ 2 * w ^ 2)
    (margin : 0 ≤ 2 * U * G - p ^ 2 * (D ^ 2 * (2 * h * P - G / (2 * h)))) :
    p ≤ w * Real.sqrt (2 * (h - B)) := by
  have charge : G / (2 * h) ≤ P * (h - B) := by
    apply (div_le_iff₀ (by positivity)).2
    calc G ≤ P*(h^2-B^2) := gap
      _ ≤ P*(h-B)*(2*h) := by nlinarith only [mul_nonneg hp.le (sq_nonneg (h-B))]
  have den : P*(h+B) ≤ 2*h*P-G/(2*h) := by linarith only [charge]
  have common : 0 < D^2*(P*(h+B)) := by positivity
  have left := mul_le_mul_of_nonneg_left den (mul_nonneg (sq_nonneg p) (sq_nonneg D))
  have right := mul_le_mul_of_nonneg_left gap (show 0 ≤ 2*U by rw [weight]; positivity)
  have both : p^2*(D^2*(P*(h+B))) ≤ (w^2*(2*(h-B)))*(D^2*(P*(h+B))) := by
    calc p^2*(D^2*(P*(h+B))) ≤ p^2*(D^2*(2*h*P-G/(2*h))) := by linarith only [left]
      _ ≤ 2*U*G := sub_nonneg.mp margin
      _ ≤ 2*U*(P*(h^2-B^2)) := right
      _ = _ := by rw [weight]; ring
  have sq := le_of_mul_le_mul_right both common
  apply le_of_sq_le_sq _ (mul_nonneg hw (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt']
  exact sq.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg w))

/-- Integrate the proposed lower polynomial exactly on a group with an affine time coordinate. -/
theorem integral_group {a b : ℝ} (ab : a < b) (p antideriv : List ℚ)
    (der : ∀ s : ℝ, QPoly.eval (QPoly.deriv antideriv) s = QPoly.eval p s) :
    (∫ t in a..b, QPoly.eval p ((2 * t - (a + b)) / (b - a))) =
      (b - a) / 2 * (QPoly.eval antideriv 1 - QPoly.eval antideriv (-1)) := by
  have sub : b - a ≠ 0 := (sub_pos.mpr ab).ne'
  let c := 2 / (b - a)
  let d := -(a + b) / (b - a)
  have hc : c ≠ 0 := div_ne_zero (by norm_num) sub
  have affine (t : ℝ) : (2 * t - (a + b)) / (b - a) = c * t + d := by dsimp [c,d]; ring
  simp_rw [affine]
  rw [intervalIntegral.integral_comp_mul_add (QPoly.eval p) hc d]
  have left : c * a + d = -1 := by dsimp [c,d]; field_simp; ring
  have right : c * b + d = 1 := by dsimp [c,d]; field_simp; ring
  rw [left,right,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (der x) ▸ QPoly.hasDerivAt_eval antideriv x)
    ((QPoly.continuous_eval p).intervalIntegrable _ _)]
  simp [c,div_eq_mul_inv, mul_comm]

end PlasmaLean.Certificates.PolynomialActionFloor
