/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCAdmFrame
public import PlasmaLean.Design.DommaschkBounceTaylor

/-! # Transfer a central field-polynomial enclosure to a physical position tube

The radius and height can change independently, while their trigonometric inputs
have exactly the same values. The rational majorant is shared with the KAM proof.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkPhysicalPolynomialError
open DommaschkKam DommaschkKam.DkPoly DommaschkKamC Certificates.TrajectoryTaylorModel

private theorem product_error {x y x' y' A B e d : ℝ}
    (hx : |x| ≤ A) (hy : |y| ≤ B) (ex : |x' - x| ≤ e) (ey : |y' - y| ≤ d) :
    |x' * y' - x * y| ≤ (A + e) * (B + d) - A * B := by
  have ne : 0 ≤ e := (abs_nonneg _).trans ex
  have na : 0 ≤ A := (abs_nonneg _).trans hx
  have by' : |y'| ≤ B + d := by
    calc
      _ = |y + (y' - y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hy ey
  calc
    _ = |(x' - x) * y' + x * (y' - y)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ = |x' - x| * |y'| + |x| * |y' - y| := by rw [abs_mul, abs_mul]
    _ ≤ e * (B + d) + A * d := by gcongr
    _ = _ := by ring

private theorem power_error {x y A e : ℝ} (hx : |x| ≤ A) (he : |y - x| ≤ e) (n : ℕ) :
    |y ^ n - x ^ n| ≤ (A + e) ^ n - A ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : |x ^ n| ≤ A ^ n := by rw [abs_pow]; gcongr
    have p := product_error h hx ih he
    simpa only [pow_succ, add_sub_cancel] using p

/-- The existing KAM majorant at angular bound one applies to the actual sparse
real polynomial used by the physical ODE, with no derivatives of the flow. -/
theorem field_error (p : SP) {u z v w c s U Z e d : ℝ}
    (hu : |u| ≤ U) (hz : |z| ≤ Z) (eu : |v - u| ≤ e) (ez : |w - z| ≤ d)
    (hc : |c| ≤ 1) (hs : |s| ≤ 1) :
    |evR v w c s p - evR u z c s p| ≤ lipR U Z e d 1 p := by
  induction p with
  | nil => simp [evR,lipR]
  | cons m p ih =>
    have hu' : |u ^ m.a| ≤ U ^ m.a := by rw [abs_pow]; gcongr
    have hz' : |z ^ m.b| ≤ Z ^ m.b := by rw [abs_pow]; gcongr
    have hm := product_error hu' hz' (power_error hu eu m.a) (power_error hz ez m.b)
    simp only [add_sub_cancel] at hm
    have wave : |c ^ m.c * s ^ m.d| ≤ 1 := by
      rw [abs_mul, abs_pow, abs_pow]
      calc |c| ^ m.c * |s| ^ m.d ≤ 1 ^ m.c * 1 ^ m.d := by gcongr
           _ = _ := by simp
    have term :
        |(m.q : ℝ) * ((v ^ m.a * w ^ m.b - u ^ m.a * z ^ m.b) * (c ^ m.c * s ^ m.d))| ≤
        |(m.q : ℝ)| * ((U + e) ^ m.a * (Z + d) ^ m.b - U ^ m.a * Z ^ m.b) := by
      rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (mul_le_mul_of_nonneg_left wave (abs_nonneg _)).trans (by simpa using hm)
    change |(m.q : ℝ) * (v ^ m.a * w ^ m.b * c ^ m.c * s ^ m.d)
      + evR v w c s p - ((m.q : ℝ) * (u ^ m.a * z ^ m.b * c ^ m.c * s ^ m.d) + evR u z c s p)| ≤ _
    rw [show (m.q : ℝ) * (v ^ m.a * w ^ m.b * c ^ m.c * s ^ m.d)
      + evR v w c s p - ((m.q : ℝ) * (u ^ m.a * z ^ m.b * c ^ m.c * s ^ m.d)
      + evR u z c s p) =
      (m.q : ℝ) * ((v ^ m.a * w ^ m.b - u ^ m.a * z ^ m.b)
        * (c ^ m.c * s ^ m.d)) + (evR v w c s p - evR u z c s p) by ring]
    exact (abs_add_le _ _).trans (by simpa [lipR] using add_le_add term ih)

/-- Enlarge an existing central Taylor model by a fixed certified spatial error. -/
theorem widen {m n : Model} {t x y : ℝ} {d : ℚ} (h : m.Mem t x) (delta : |y - x| ≤ (d : ℝ))
    (poly : m.poly = n.poly) (radius : m.radius + d ≤ n.radius) : n.Mem t y := by
  rw [Model.Mem, ← poly]
  calc
    _ = |(y - x) + (x - Certificates.QPoly.eval m.poly t)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add delta h
    _ ≤ _ := by simpa only [add_comm, Rat.cast_add] using (Rat.cast_le.mpr radius :
      ((m.radius + d : ℚ) : ℝ) ≤ (n.radius : ℝ))

end PlasmaLean.Design.DommaschkPhysicalPolynomialError
