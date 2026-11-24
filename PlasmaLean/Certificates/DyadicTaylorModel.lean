/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.TrajectoryTaylorModel

/-! # Reading a common-denominator trajectory witness

Column zero is the constant coefficient. A single power of two scales all
coefficient numerators and the additive error from the trajectory exporter.
-/

@[expose] public section
namespace PlasmaLean.Certificates.TrajectoryTaylorModel

/-- Read ascending integer coefficients and the error with common denominator 2^bits. -/
def ofDyadic (bits : ℕ) (coefficients : List ℤ) (error : ℤ) : Model :=
  ⟨QPoly.scale (1 / 2 ^ bits) (coefficients.map fun (a : ℤ) => (a : ℚ)),
   (error : ℚ) / 2 ^ bits⟩

/-- Membership is equivalent to the error comparison in the numerator units of the witness. -/
theorem mem_ofDyadic_iff (bits : ℕ) (coefficients : List ℤ) (error : ℤ) (t y : ℝ) :
    (ofDyadic bits coefficients error).Mem t y ↔
    |2 ^ bits * y - QPoly.eval (coefficients.map fun (a : ℤ) => (a : ℚ)) t| ≤ (error : ℝ) := by
  simp only [Model.Mem, ofDyadic, QPoly.eval_scale, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_intCast]
  have hs : (0 : ℝ) < 2 ^ bits := by positivity
  have rearr (v : ℝ) : |y - 1 / 2 ^ bits * v| * 2 ^ bits = |2 ^ bits * y - v| := by
    calc
      _ = |(y - 1 / 2 ^ bits * v) * 2 ^ bits| := by rw [abs_mul, abs_of_pos hs]
      _ = _ := by congr 1; field_simp
  rw [le_div_iff₀ hs, rearr]

/-- Range of a dyadic model throughout the slab. The nonconstant coefficients
and model error are charged in the same integer units. -/
theorem dyadic_range {bits : ℕ} {a : ℤ} {p : List ℤ} {e : ℤ} {t y : ℝ} (ht : |t| ≤ 1)
    (hy : (ofDyadic bits (a :: p) e).Mem t y) :
    |(2 : ℝ) ^ bits * y - a| ≤ (e : ℝ) + magnitude (p.map fun (z : ℤ) => (z : ℚ)) := by
  have tail := abs_eval_le ht (p.map fun (z : ℤ) => (z : ℚ))
  let v := QPoly.eval (p.map fun (z : ℤ) => (z : ℚ)) t
  have hy' : |2 ^ bits * y - ((a : ℝ) + t * v)| ≤ (e : ℝ) := by
    simpa only [List.map_cons, QPoly.eval_cons, Rat.cast_intCast, v] using
      (mem_ofDyadic_iff bits (a :: p) e t y).mp hy
  calc
    _ ≤ |2 ^ bits * y - ((a : ℝ) + t * v)| + |((a : ℝ) + t * v) - a| := abs_sub_le _ _ _
    _ ≤ _ := by
      rw [add_sub_cancel_left, abs_mul]
      exact add_le_add hy' ((mul_le_mul_of_nonneg_right ht (abs_nonneg v)).trans
        (by simpa [v] using tail))

end PlasmaLean.Certificates.TrajectoryTaylorModel
