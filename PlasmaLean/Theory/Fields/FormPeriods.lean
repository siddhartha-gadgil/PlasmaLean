/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormTopology
public import PlasmaLean.Theory.Contract.StellaratorContract
public import TauCeti.Geometry.Manifold.DeRham.Period
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Circulation as a de Rham period (TauCeti v4.36.0)

The contract layer measures the net current through a loop by the circulation
`Contract.lineIntegral B γ a b = ∫ ⟪B(γ t), γ'(t)⟫ dt` (Ampère's law). TauCeti integrates a
1-form on a manifold along a curve (`TauCeti.pathIntegral`) and, for closed forms, defines the
period homomorphism `TauCeti.periodHom` on the fundamental group. This file identifies them for
`β = B♭` on an open region `U` of `ℝ³`, through the bridge `onOpens`.

* `pathIntegral_onOpens_flat`: TauCeti's line integral of `B♭` along a curve in `U` is the
  circulation of `B` along the same curve in `ℝ³`. No hypothesis.
* `periodHom_onOpens_flat`: for a curl-free `C¹` field on `U`, the period of `B♭` on the class
  of a `C¹` loop is the circulation of `B` around the loop. So the Ampère current through a loop
  is `μ₀⁻¹` times a de Rham period, and depends only on the homotopy class of the loop in `U`.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped Manifold RealInnerProductSpace

/-- **TauCeti's line integral of `B♭` is the circulation of `B`.** -/
theorem pathIntegral_onOpens_flat (U : Opens Space) (B : Space → Space) (c : ℝ → U)
    (a b : ℝ) :
    pathIntegral (onOpens U fun y => flat (B y)) c a b
      = lineIntegral B (fun t => (c t : Space)) a b := by
  rw [pathIntegral_def, lineIntegral]
  congr 1
  funext t
  have hv : (Manifold.curveVelocity 𝓘(ℝ, Space) c t : Space)
      = deriv (fun t => (c t : Space)) t := by
    rw [← Manifold.curveVelocity_eq_deriv (γ := fun t => (c t : Space)),
      Manifold.curveVelocity_apply, Manifold.curveVelocity_apply]
    exact (Manifold.mfderiv_subtype_val_comp_apply (f := c) (1 : ℝ)).symm
  exact congrArg (fun v : Space => ⟪B (c t), v⟫) hv

/-- **The period of `B♭` on a loop class is the circulation of `B`.** Here `B` is `C¹` and
curl-free on the open region `U`, and the loop `γ` follows a curve `c` that is `C¹` as a curve
in `ℝ³`. -/
theorem periodHom_onOpens_flat {U : Opens Space} {B : Space → Space}
    (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0) {x : U} {c : ℝ → U}
    (hc : ContDiff ℝ 1 fun t => (c t : Space)) {γ : Path x x}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    periodHom (onOpens U fun y => flat (B y)) x (Additive.ofMul (.of (.mk γ)))
      = lineIntegral B (fun t => (c t : Space)) 0 1 := by
  have hsm : IsSmoothForm 𝓘(ℝ, Space) 1 (onOpens U fun y => flat (B y)) :=
    (isSmoothForm_onOpens_iff U _).2 (flat.toContinuousLinearEquiv.contDiff.comp_contDiffOn hB)
  have hcl : mextDeriv (onOpens U fun y => flat (B y)) = 0 :=
    (mextDeriv_onOpens_eq_zero_iff U _).2 fun y hy => by
      rw [extDeriv_flat, hcurl y hy, map_zero]
  have hcm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Space) 1 c :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Space)) (n := 1) U c).1
      hc.contMDiff
  rw [periodHom_ofMul_eq_pathIntegral hsm hcl hcm hγ, pathIntegral_onOpens_flat]

end PlasmaLean.Forms
