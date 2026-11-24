/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorEndpointSign

/-! # Convert a certified physical gap using the local cylindrical radius -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkGroupGapRadius
open DommaschkMirrorEndpointSign

/-- A smaller test height remains above the field if the original signed margin
absorbs the full correction on the spatial radius of this enclosure. -/
theorem at_lower {R D nr nz h k radius upper : ℝ} (hR : 0 ≤ R) (cap : R ≤ radius)
    (ordered : 0 ≤ h ^ 2 - k ^ 2) (gap_bound : gap R h D nr nz ≤ upper)
    (room : upper + radius ^ 16 * (h ^ 2 - k ^ 2) < 0) :
    oriented false (gap R k D nr nz) 0 := by
  have correction := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR cap 16) ordered
  have identity : gap R k D nr nz = gap R h D nr nz + R ^ 16 * (h ^ 2 - k ^ 2) := by
    unfold gap
    ring
  exact identity.trans_lt ((add_le_add gap_bound correction).trans_lt room)

end PlasmaLean.Design.DommaschkGroupGapRadius
