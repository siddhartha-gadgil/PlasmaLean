/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCContract
public import PlasmaLean.Design.DommaschkKamCRes

/-!
# Contract clause C1 for the Dommaschk quasi-axisymmetric target (N-33, final assembly)

On-demand top module (not imported by `PlasmaLean.lean`): build with
`lake build PlasmaLean.Design.DommaschkKamCFinal` after its on-demand dependencies
(`DommaschkKamCAdm`, `DommaschkKamCConsts`, `DommaschkKamCRes`, `DommaschkKamCContract`; build
stale dependencies one at a time). Axioms are checked in `scripts/check_axioms_heavy.lean`.

The certified initial residual bounds of the high-resolution chain (`dk_e0R`, `dk_e0Z`,
`e₀ = 1.23 · 10⁻²⁷` at `ρ = 9/200`) are weakened to the budget `e0qDK = 10⁻²⁴` of the constants
record `cDK` and fed into `dommaschk_C1`. The result is unconditional:

**`dommaschk_C1_unconditional`**: for every `μ₀ > 0` there is a family `S` of surfaces with
`CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S 0 (6/25)`, i.e. the exact
Dommaschk vacuum field (N-31 §24) has a certified invariant torus with rotational transform
`|ι| ≥ 0.24` and zero net toroidal current (Ampère circulation around its poloidal loop).

Scope: contract clause C1 only. Not proved here: confinement of the field lines inside the torus
(the all-time confinement argument used for the rational field), nested families of surfaces,
the certified quasi-axisymmetry defect and C2 (the fit's QS numbers are untrusted numerics).
-/

public section
noncomputable section
namespace PlasmaLean.Design.DommaschkKamC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract

/-- Weakening the bound of `Bd`. -/
theorem Bd_weaken {ρ B B' : ℝ} {x : FA} (h : Bd ρ x B) (hB : B ≤ B') : Bd ρ x B' :=
  ⟨h.1, h.2.trans hB⟩

/-- The certified initial error fits the budget of `cDK`: `1.23 · 10⁻²⁷ ≤ 10⁻²⁴`. -/
theorem e0q_le_budget : ((e0q : ℚ) : ℝ) ≤ ((e0qDK : ℚ) : ℝ) := by
  have : e0q ≤ e0qDK := by norm_num [e0q, e0qDK]
  exact_mod_cast this

/-- **Contract clause C1 for the exact Dommaschk field, unconditionally**: zero net toroidal
current and rotational transform `|ι| ≥ 6/25` on a certified invariant torus. -/
theorem dommaschk_C1_unconditional {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S 0 (6 / 25) :=
  dommaschk_C1 (Bd_weaken dk_e0R e0q_le_budget) (Bd_weaken dk_e0Z e0q_le_budget) hμ

/-- **The exact Dommaschk field has a certified invariant torus with transform `ι_C`**
(`ι_C = −(85 + √5)/361 ≈ −0.2417`), unconditionally. -/
theorem dommaschk_iotaOnTorus_unconditional :
    ∃ R z, IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R z
      DommaschkKamDio.dkIotaC :=
  dommaschk_iotaOnTorus (Bd_weaken dk_e0R e0q_le_budget) (Bd_weaken dk_e0Z e0q_le_budget)

end PlasmaLean.Design.DommaschkKamC
