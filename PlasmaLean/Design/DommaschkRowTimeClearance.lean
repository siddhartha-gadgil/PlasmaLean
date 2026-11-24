/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCoreClearance

/-! # Row-dependent mirror strength clearances that certify inverse-speed bounds -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkRowTimeClearance
open DommaschkMirrorEndpointSign DommaschkFirstMirrorLaunchSign

def testHeight (q : ℕ) : ℚ := height false - 1 / (2 * (q : ℚ) ^ 2)

/-- Raising the old polynomial by the exact height correction preserves its strict sign
whenever the archived upper enclosure absorbs that correction. -/
theorem of_gap {R D nr nz L H : ℝ} (nonneg : 0 ≤ R) (cap : R ≤ 1)
    (diff : 0 ≤ L ^ 2 - H ^ 2)
    (margin : gap R L D nr nz + (L ^ 2 - H ^ 2) < 0) :
    oriented false (gap R H D nr nz) 0 := by
  have corr := mul_le_of_le_one_left diff (pow_le_one₀ nonneg cap (n := 16))
  have eq : gap R H D nr nz = gap R L D nr nz + R ^ 16 * (L ^ 2 - H ^ 2) := by
    unfold gap
    ring
  change gap R H D nr nz < 0
  linarith only [eq, corr, margin]

theorem reciprocal_le {h f : ℝ} {q : ℕ} (positive : 0 < q)
    (lo : (height false : ℝ) ≤ h) (below : f < (testHeight q : ℝ)) :
    1 / Real.sqrt (2 * (h - f)) ≤ q := by
  have pos : (0 : ℝ) < q := by exact_mod_cast positive
  push_cast [testHeight] at below
  have gap : (1 / (q : ℝ)) ^ 2 ≤ 2 * (h - f) := by
    have frac : (1 / (q : ℝ)) ^ 2 = 2 * (1 / (2 * (q : ℝ) ^ 2)) := by field_simp
    rw [frac]
    linarith
  have root : 1 / (q : ℝ) ≤ Real.sqrt (2 * (h - f)) := by
    simpa only [Real.sqrt_sq (one_div_nonneg.mpr pos.le)] using Real.sqrt_le_sqrt gap
  exact (div_le_iff₀ ((one_div_pos.mpr pos).trans_le root)).mpr ((div_le_iff₀' pos).mp root)

end PlasmaLean.Design.DommaschkRowTimeClearance
