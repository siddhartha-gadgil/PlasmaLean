/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamIdentCheck

/-!
# Kernel check: `D = R⁷ B_φ` for `field candidate`

One of the Cartesian identities of `Design/DommaschkKamIdentCheck`, in its own module to keep
each Lean process within the laptop memory budget: the sliced normal form (`degCheck`) of
`L · convAll N p − N · G` is empty (kernel evaluation, `kernel_fact`).
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKam

open DkPoly PlasmaLean.Fields.CylAlgebra

/-- **`D = R⁷ B_φ`** as a Cartesian identity (kernel check of the sliced normal form). -/
theorem ident_D :
    degCheck zs rs (cscale Lw (convAll NDn dDR) ++ cscale (-NDn) Gphi) = true := by
  kernel_fact

end PlasmaLean.Design.DommaschkKam
