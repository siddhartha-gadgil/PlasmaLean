/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRegionGrid

/-! # Sanity fixtures of the box check of `DommaschkRegionEnclosure`

* `good_fixture`: a box of the grid on which the check holds with the thresholds of the grid.
* `good_reject`: a box of the grid on which it fails (the generator subdivides it), so the check
  is not vacuous.
* `good_reject_threshold`: on the accepted box the check fails for a speed threshold below the
  true value of the speed there.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkRegionEnclosure
open DommaschkRegionGrid

/-- **Sanity**: an accepted box. -/
theorem good_fixture : good b₀ c₁ M (cell 1 0 0 0) = true := by kernel_fact

/-- **Sanity**: a rejected box (too wide for the thresholds). -/
theorem good_reject : good b₀ c₁ M (cell 0 0 2 10) = false := by kernel_fact

/-- **Sanity**: the accepted box is rejected when the speed threshold is `1/1000`. -/
theorem good_reject_threshold : good b₀ c₁ (1 / 1000) (cell 1 0 0 0) = false := by kernel_fact

end PlasmaLean.Design.DommaschkRegionEnclosure
