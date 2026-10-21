/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowFrame
public import PlasmaLean.Design.KamNewtonField

/-!
# The symplectic frame for the rational stellarator field (KAM route, K3d)

The instance `F = field14` (`field (1/4)`, `Design/KamNewtonField`) of the frame of an
approximate torus and its exact identities (`Design/KamFlowFrame`). The frame hypotheses, the
inverse `D⁻¹` and the algebraic torsion density `T₀ = R³ P / (D³ W₀²)` of `field (1/4)` are
`FrameHyp`, `Di`, `Talg`; every identity of `Design/KamFlowFrame` applies to them through the
instance (for example `FrameHyp.eta2_flux` below, the exact flux identity).

**Sanity.** `Talg_eq` (the torsion density written with the polynomials of `field (1/4)`) and
`FrameHyp.avg_eta2` (`⟨η₂⟩ = 0` exactly for `field (1/4)`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM

/-- The frame hypotheses for `field (1/4)`. -/
abbrev FrameHyp (u z : FA) : Prop := field14.FrameHyp u z

/-- `D⁻¹` for `field (1/4)`. -/
abbrev Di (u z : FA) : FA := field14.Di u z

/-- The algebraic torsion density `T₀ = R³ P / (D³ W₀²)` of `field (1/4)`. -/
abbrev Talg (u z : FA) : FA := field14.Talg u z

/-- **Sanity**: the torsion density of `field (1/4)` in terms of its polynomials. -/
theorem Talg_eq (u z : FA) :
    Talg u z = (1 + u) ^ 3 * Ring.inverse (Dof u z) ^ 3 * Ring.inverse (W0of u z) ^ 2 * Pof u z :=
  rfl

namespace FrameHyp

variable {ι : ℝ} {u z : FA} (H : FrameHyp u z)
include H

/-- **Flux identity for `field (1/4)`**: `η₂ = ∂_θ B − ∂_φ A`. -/
theorem eta2_flux : field14.eta2 ι u z = dTh (field14.BF u z) - dPh (field14.AF u z) :=
  FlowField.FrameHyp.eta2_flux H

/-- **`⟨η₂⟩ = 0` exactly for `field (1/4)`** (zero flux through the torus). -/
theorem avg_eta2 : avg (field14.eta2 ι u z) = 0 := FlowField.FrameHyp.avg_eta2 H

end FrameHyp

end PlasmaLean.Design.KamNewton
