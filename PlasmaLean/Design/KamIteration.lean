/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowIteration
public import PlasmaLean.Design.KamNewtonStep

/-!
# The KAM iteration for the rational stellarator field (KAM route, K3d, `kam_flow_torus`)

The instance `F = field14` (`field (1/4)`) of the abstract KAM theorem for fields in flow form
(`Design/KamFlowIteration`). The admissibility bounds, the global numerical conditions and the
hypotheses of the iteration for `field (1/4)` are `AdmBounds`, `GlobalH` and `KamH`; the
conclusion `KamH.kam_flow_torus` is stated with the residuals `resR`, `resZ` of `field (1/4)`.

**Sanity.** `iterK_zero`: the iteration starts at the initial torus.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM

/-- The torus and frame bounds of a Newton step for `field (1/4)`. -/
abbrev AdmBounds (c : SC) (ι ρ : ℝ) (u z : FA) : Prop := field14.AdmBounds c ι ρ u z

/-- The global numerical conditions for `field (1/4)`. -/
abbrev GlobalH (c : SC) (ι : ℝ) : Prop := field14.GlobalH c ι

/-- The hypotheses of the KAM iteration for `field (1/4)`. -/
abbrev KamH (c : SC) (ι : ℝ) (u₀ z₀ : FA) (e₀ μ : ℝ) : Prop := field14.KamH c ι u₀ z₀ e₀ μ

/-- The KAM iterates for `field (1/4)`. -/
abbrev iterK (ι : ℝ) (u₀ z₀ : FA) : ℕ → FA × FA := field14.iterK ι u₀ z₀

/-- **Sanity**: the iteration starts at the initial torus. -/
theorem iterK_zero (ι : ℝ) (u₀ z₀ : FA) : iterK ι u₀ z₀ 0 = (u₀, z₀) := rfl

/-- **The KAM theorem for the flow form of `field (1/4)` (`kam_flow_torus`).** Under the
hypotheses `KamH` the iteration converges on the strip `ρ_∞ = ρ₀ − 6δ₀` to an analytic, real
torus `(u, z)` that solves the flow-form invariance equation of `field (1/4)` **exactly**,
`D 𝓛K = n` (`resR = resZ = 0`), and stays `μ`-close to the initial torus in
`u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z`. -/
theorem KamH.kam_flow_torus {c : SC} {ι : ℝ} {u₀ z₀ : FA} {e₀ μ : ℝ}
    (K : KamH c ι u₀ z₀ e₀ μ) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ resR ι u z = 0 ∧ resZ ι u z = 0 ∧
      Close (rInf c) ι u z u₀ z₀ μ := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := FlowField.KamH.kam_flow_torus K
  exact ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩

end PlasmaLean.Design.KamNewton
