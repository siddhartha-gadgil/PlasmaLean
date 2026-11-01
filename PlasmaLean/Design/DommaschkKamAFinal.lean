/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamAContract
public import PlasmaLean.Design.DommaschkKamARes

/-!
# Contract clause C1 for the Dommaschk target from torus A (final assembly)

On-demand top module (not imported by `PlasmaLean.lean`): build with
`lake build PlasmaLean.Design.DommaschkKamAFinal` after its on-demand dependencies
(`DommaschkKamAAdm`, `DommaschkKamAConsts`, `DommaschkKamANest`, `DommaschkKamARes`,
`DommaschkKamAContract`; build stale dependencies one at a time).

The certified initial residual bounds of the high-resolution chain of torus A (`dk_e0R`, `dk_e0Z`,
`e₀ = 6.2 · 10⁻²⁶` at `ρ = 9/200`, `Design/DommaschkKamARes`) are weakened to the budget
`e0qDK = 10⁻²⁵` of the constants record `cDK` of `Design/DommaschkKamAConsts` and fed into
`dommaschkA_C1`:

* **`dommaschkA_C1_unconditional`**: for every `μ₀ > 0` there is a family `S` with
  `CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S 0 0.2386`;
* **`dommaschkA_iotaOnTorus_unconditional`**: the exact field has a certified invariant torus with
  transform `ι_A = −(19 + √5)/89 ≈ −0.2386`.

`|ι_A| < 0.24`, so the transform bound is `0.2386`, not `6/25` (`not_C1_iotaMin_A`).
-/

public section
noncomputable section
namespace PlasmaLean.Design.DommaschkKamA
open PlasmaLean.Design.DommaschkKamC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract

/-- The certified initial error of torus A fits the budget of `cDK`: `6.2 · 10⁻²⁶ ≤ 10⁻²⁵`. -/
theorem e0q_le_budget : ((e0q : ℚ) : ℝ) ≤ ((e0qDK : ℚ) : ℝ) := by
  have : e0q ≤ e0qDK := by norm_num [e0q, e0qDK]
  exact_mod_cast this

/-- The certified `R`-residual of torus A within the budget. -/
theorem dk_e0R' : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ) :=
  ⟨dk_e0R.1, dk_e0R.2.trans e0q_le_budget⟩

/-- The certified `z`-residual of torus A within the budget. -/
theorem dk_e0Z' : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ) :=
  ⟨dk_e0Z.1, dk_e0Z.2.trans e0q_le_budget⟩

/-- **The exact torus A exists**: a real analytic exact invariant torus of the flow form with
transform `ι_A`, `10⁻¹²`-close to the data torus A. -/
theorem exists_exactTorusA : ∃ u z : FA, ExactTorusA u z := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := dk_exact_of_res dk_e0R' dk_e0Z'
  exact ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩

/-- **Contract clause C1 for the exact Dommaschk field from torus A, unconditionally**: zero net
toroidal current and rotational transform `|ι| ≥ 0.2386` on a certified invariant torus. -/
theorem dommaschkA_C1_unconditional {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S 0 (1193 / 5000) :=
  dommaschkA_C1 dk_e0R' dk_e0Z' hμ

/-- **The exact Dommaschk field has a certified invariant torus with transform `ι_A`**
(`ι_A = −(19 + √5)/89 ≈ −0.2386`), unconditionally. -/
theorem dommaschkA_iotaOnTorus_unconditional :
    ∃ R z, IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R z
      DommaschkKamDio.dkIotaA :=
  dommaschkA_iotaOnTorus dk_e0R' dk_e0Z'

end PlasmaLean.Design.DommaschkKamA
