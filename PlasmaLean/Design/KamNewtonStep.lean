/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowStep
public import PlasmaLean.Design.KamNewtonFrame

/-!
# One Newton step for the rational stellarator field (KAM route, K3d, `kam_step`)

The instance `F = field14` (`field (1/4)`) of the quasi-Newton step with explicit estimates
(`Design/KamFlowStep`). With the step constants `c : SC` and the hypotheses `StepH c ι u z e δ`
(the frame, the Diophantine frequency, the torus/field/inverse/torsion bounds, the twist and the
Taylor constant `C₂` for the residual polynomials `resRp`, `resZp` of `field (1/4)`), one step
satisfies `‖ΔK‖ ≤ cK e/δ²`, `‖𝓛ΔK‖ ≤ cL e/δ²` and `‖E(K + ΔK)‖ ≤ κ e²/δ⁴` on the strip `ρ − 2δ`
(`kam_step`), stated with the residuals `resR`, `resZ` of `field (1/4)`.

**Sanity.** `StepH.hC2R_eq`: the Taylor hypothesis of the instance is the one for `resRp`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM

/-- The hypotheses of one Newton step for `field (1/4)`. -/
abbrev StepH (c : SC) (ι : ℝ) (u z : FA) (e δ : ℝ) : Prop := field14.StepH c ι u z e δ

/-- **Sanity**: the Taylor hypothesis of a step for `field (1/4)` concerns `resRp`. -/
theorem StepH.hC2R_eq {c : SC} {ι : ℝ} {u z : FA} {e δ : ℝ} (h : StepH c ι u z e δ) :
    PolyExpr.majD2 (c.avec + c.Tq • c.mvec) c.mvec resRp / 2 ≤ c.C2 :=
  FlowField.StepH.hC2R h

/-- **One Newton step for `field (1/4)` (`kam_step`).** The correction `ΔK` is analytic,
`‖ΔK‖_{ρ−2δ} ≤ cK e/δ²`, `‖𝓛ΔK‖_{ρ−2δ} ≤ cL e/δ²`, and the residuals of `field (1/4)` at the new
torus satisfy `‖E(K + ΔK)‖_{ρ−2δ} ≤ κ e²/δ⁴`. -/
theorem kam_step {c : SC} {ι : ℝ} {u z : FA} {e δ : ℝ} (h : StepH c ι u z e δ) :
    Ana (field14.dRs ι u z) ∧ Ana (field14.dZs ι u z) ∧
      Bd (c.ρ - 2 * δ) (field14.dRs ι u z) (c.cK * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (field14.dZs ι u z) (c.cK * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (Lt ι (field14.dRs ι u z)) (c.cL * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (Lt ι (field14.dZs ι u z)) (c.cL * e / δ ^ 2) ∧
      Bd (c.ρ - 2 * δ) (resR ι (u + field14.dRs ι u z) (z + field14.dZs ι u z))
        (c.kap * e ^ 2 / δ ^ 4) ∧
      Bd (c.ρ - 2 * δ) (resZ ι (u + field14.dRs ι u z) (z + field14.dZs ι u z))
        (c.kap * e ^ 2 / δ ^ 4) :=
  FlowField.StepH.kam_step h

end PlasmaLean.Design.KamNewton
