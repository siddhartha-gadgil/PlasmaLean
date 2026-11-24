/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorEndpointSign

/-! # A quantitative strength clearance on the physical core before the first mirrors -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCoreClearance

open DommaschkMirrorEndpointSign

/-- A test height below the lowest energy in the action archive. -/
def height : ℚ := DommaschkFirstMirrorLaunchSign.height false - 1 / 270000

/-- Reuse the certified margin of the cancelled physical polynomial. The power
of radius converts the original clearance at the archived height to the new test. -/
theorem of_gap {R D nr nz : ℝ} (nonneg : 0 ≤ R) (cap : R ≤ 1)
    (margin : gap R (DommaschkFirstMirrorLaunchSign.height false) D nr nz ≤ -(1 / 125000)) :
    oriented false (gap R height D nr nz) 0 := by
  let h : ℝ := DommaschkFirstMirrorLaunchSign.height false
  have diff : 0 ≤ h ^ 2 - (height : ℝ) ^ 2 ∧
      h ^ 2 - (height : ℝ) ^ 2 < 1 / 125000 := by
    norm_num [h, height, DommaschkFirstMirrorLaunchSign.height]
  have delta : gap R height D nr nz = gap R h D nr nz + R ^ 16 * (h ^ 2 - (height : ℝ) ^ 2) := by
    unfold gap
    ring
  have corr := mul_le_of_le_one_left diff.1 (pow_le_one₀ nonneg cap (n := 16))
  change gap R height D nr nz < 0
  change gap R h D nr nz ≤ _ at margin
  linarith [diff.2]

end PlasmaLean.Design.DommaschkCoreClearance
