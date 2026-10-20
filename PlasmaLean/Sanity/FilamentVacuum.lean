/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.Vacuum
public import PlasmaLean.Theory.Fields.FilamentSmooth

/-!
# Closed filament fields are vacuum fields (sanity)

Combines `Sanity.filamentField_vacuumField` with the smoothness theorem
`Fields.filamentField_contDiffOn_two`, so closed `C¹` filament fields are instances of the
kernel predicate `VacuumField` without a separate `C²` hypothesis.
-/

public section

namespace PlasmaLean.Sanity
open PlasmaLean.Vacuum PlasmaLean.Fields

/-- **Closed filament fields are vacuum fields** on any open region avoiding the
coil, with no separate regularity hypothesis: the curve is differentiable on
`[a, b]` with continuous tangent (a closed `C¹` curve, `c a = c b`), carrying a
constant current `I`. The `C²` hypothesis of `filamentField_vacuumField` is
discharged by `Fields.filamentField_contDiffOn_two`. -/
theorem filamentField_vacuumField' (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) {Ω : Set Space}
    (hΩ : IsOpen Ω) (hc : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ c t)
    (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    (sep : ∀ x ∈ Ω, ∀ t ∈ Set.uIcc a b, x - c t ≠ 0) (closed : c a = c b) :
    VacuumField Ω (filamentField μ₀ I c a b) :=
  filamentField_vacuumField μ₀ I c a b hΩ hc ht sep closed
    (filamentField_contDiffOn_two μ₀ I c a b hΩ
      (fun t htm => (hc t htm).continuousAt.continuousWithinAt) ht sep)

end PlasmaLean.Sanity
