/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkGradientCheck

/-! # Sanity fixtures of the box check of `DommaschkGradientCheck`

The box `fixture` is a neighbourhood of the QA2R label-0.474 field line near the toroidal angle
`1/128`: `R − 29/32 ∈ [0.08897, 0.08958]`, `z ∈ [−0.00149, 0.00030]`, `cos 2φ ∈ [0.99951, 1]`,
`sin 2φ ∈ [0, 0.03125]`. Untrusted sampling gives `‖∇|B|‖ ≈ 1.106`, `|B| ≈ 1.044` and the planar
speed `≈ 0.076` there.

* `fine_fixture`: the check holds with the gradient bound `6/5`, the strength bound `26/25`
  and the speed bound `1/10`.
* `fine_reject_gradient`: it fails for the gradient bound `1`, below the true value.
* `fine_reject_strength`: it fails for the strength bound `21/20`, above the true value.
* `fine_reject_speed`: it fails for the speed bound `1/20`, below the true value.
* `fine_reject_wide`: it fails on a box forty times wider in `R`.

Each fixture is one evaluation by the kernel (about 40 s and 12 GB).
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkGradientCheck
open DommaschkBounceField

set_option maxRecDepth 100000

/-- A box around the field line of label 0.474 near the toroidal angle `1/128`. -/
def fixture : Box :=
  ⟨⟨382123165, 384758117, true⟩, ⟨-6379147, 1294336, true⟩, ⟨4292870312, 4294967298, true⟩,
    ⟨-2, 134195886, true⟩⟩

/-- **Sanity**: an accepted box. -/
theorem fine_fixture :
    fine (6 / 5) (26 / 25) (103 / 100) (21 / 20) (1 / 10) (1039 / 1000) fixture = true := by
  kernel_fact

/-- **Sanity**: the gradient bound `1` is rejected. -/
theorem fine_reject_gradient :
    fine 1 (26 / 25) (103 / 100) (21 / 20) (1 / 10) (1039 / 1000) fixture = false := by
  kernel_fact

/-- **Sanity**: the strength bound `21/20` is rejected. -/
theorem fine_reject_strength :
    fine (6 / 5) (21 / 20) (103 / 100) (21 / 20) (1 / 10) (1039 / 1000) fixture = false := by
  kernel_fact

/-- **Sanity**: the speed bound `1/20` is rejected. -/
theorem fine_reject_speed :
    fine (6 / 5) (26 / 25) (103 / 100) (21 / 20) (1 / 20) (1039 / 1000) fixture = false := by
  kernel_fact

/-- **Sanity**: a box that is too wide in the radius is rejected. -/
theorem fine_reject_wide :
    fine (6 / 5) (26 / 25) (103 / 100) (21 / 20) (1 / 10) (1039 / 1000)
      ⟨⟨282123165, 384758117, true⟩, fixture.z, fixture.c, fixture.s⟩ = false := by
  kernel_fact

end PlasmaLean.Design.DommaschkGradientCheck
