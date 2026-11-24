/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.DyadicTaylorModel

/-! # Spatial subdivision of a dyadic trajectory tube

Only the constant coefficient changes when a spatial uncertainty is subdivided.
Both children retain the original time polynomial and the same physical clock.
-/

@[expose] public section
namespace PlasmaLean.Certificates.TrajectoryTaylorModel

/-- Two possibly overlapping dyadic error intervals cover the original interval
whenever their outer endpoints reach its endpoints and there is no interior gap. -/
theorem cover_spatial_radius {bits : ℕ} {a e l dl r dr : ℤ} {p : List ℤ} {t y : ℝ}
    (hl : l - dl ≤ -e) (hm : r - dr ≤ l + dl) (hr : e ≤ r + dr)
    (h : (ofDyadic bits (a :: p) e).Mem t y) :
    (ofDyadic bits ((a+l) :: p) dl).Mem t y ∨ (ofDyadic bits ((a+r) :: p) dr).Mem t y := by
  simp only [mem_ofDyadic_iff, List.map_cons, QPoly.eval_cons, Rat.cast_intCast,
    Int.cast_add, Rat.cast_add, abs_le] at h ⊢
  have lo : (l : ℝ) - dl ≤ -e := by exact_mod_cast hl
  have meet : (r : ℝ) - dr ≤ l + dl := by exact_mod_cast hm
  have hi : (e : ℝ) ≤ r + dr := by exact_mod_cast hr
  rcases le_total ((2 : ℝ)^bits*y - (a + t*QPoly.eval (p.map fun z : ℤ => (z : ℚ)) t))
      ((l : ℝ) + dl) with hleft | hright
  · left
    constructor <;> linarith only [h.1, lo, hleft]
  · right
    constructor <;> linarith only [h.2, hi, meet, hright]

end PlasmaLean.Certificates.TrajectoryTaylorModel
