/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.NoetherRotation
public import PlasmaLean.Theory.Fields.WeakQuasisymmetry
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite symmetries, and the bridge from the Noether route to the direct proofs

`Theory/Kinetic/NoetherRotation` derives the canonical angular momentum from TauCeti's Noether
theorem under the infinitesimal hypothesis `DA(y)(K y) = K(A y)`. This file closes two gaps.

**Finite symmetry gives the infinitesimal one.**

* `fderiv_eq_of_equivariant`: if `A` is differentiable at `y` and `A (g s y) = g s (A y)` for a
  family of maps `g s` with `g 0 = id` on the two points involved and velocities `K y`,
  `K (A y)` at `s = 0`, then `DA(y)(K y) = K(A y)`. The maps `g s` need not be linear.
* `fderiv_eq_of_equivariant_clm`: the same for a family of continuous linear maps `g s` with
  `g 0 = 1` and derivative `K` at `0`.
* `rotZ_hasDerivAt_rotGenZ`, `fderiv_rotGenZ_of_rotZ_equivariant`: the rotations
  `PlasmaLean.Fields.rotZ` about the `z`-axis have generator `rotGenZ`.
* `canonicalMomentum_conserved_of_rotZ_equivariant`: if `B = ∇ × A` and `A` is equivariant
  under all rotations about the `z`-axis, then `m (x × v)_z + q⟪A, e_z × x⟫` is constant along
  every Lorentz orbit.

**Bridge to the direct proofs** (`Theory/Kinetic/Noether`, `Theory/Kinetic/CanonicalMomentum`).
For a skew continuous linear `K`, the function `ψ(y) = ⟪A(y), K y⟫` has gradient
`symmetryFluxGrad A K y = DA(y)†(K y) − K(A y)` (`hasFDerivAt_symmetryFlux`).

* `symmetricFlux_symmetryFluxGrad_iff`: with `B = ∇ × A`, the hypothesis
  `SymmetricFlux B G K` of the direct proof, for this `G`, is equivalent to infinitesimal
  equivariance of `A` under `K`. This direction does not use skewness of `K`.
* `symmetricFlux_of_equivariant`, `isKilling_linear`, `axisymmetricFlux_of_equivariant`,
  `axisymmetricFlux_iff_symmetricFlux_rotGenZ`: the hypotheses of `noetherMomentum_conserved`
  and of `canonicalMomentum_conserved`.
* `noetherMomentum_linear_conserved_direct`, `canonicalMomentum_rotGenZ_conserved_direct`:
  the statements of `noetherMomentum_linear_conserved` and
  `canonicalMomentum_rotGenZ_conserved`, proved a second time from the direct theorems,
  without TauCeti's Noether theorem.

Scope: `A` time-independent and differentiable on all of space, `B = ∇ × A` everywhere, no
electric field. Not proved: the gauge-term case (`A` equivariant up to a gradient) is not
bridged; the converse "infinitesimal equivariance implies equivariance under the finite
rotations" is not proved; no statement is made for symmetries that are not linear
(translations are in `Theory/Kinetic/NoetherLagrangian`).
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms WithLp
open TauCeti Topology
open scoped RealInnerProductSpace

/-! ### Finite equivariance gives infinitesimal equivariance -/

/-- **Finite equivariance gives infinitesimal equivariance.** Let `g s` be maps of space
(not necessarily linear) with `A (g s y) = g s (A y)` for all `s`, with `g 0 y = y`, and with
velocities `K y` at `y` and `K (A y)` at `A y` for `s = 0`. If `A` is differentiable at `y`,
then `DA(y)(K y) = K(A y)`. -/
theorem fderiv_eq_of_equivariant {A : Space → Space} {g : ℝ → Space → Space}
    {K : Space → Space} {y : Space} (hA : DifferentiableAt ℝ A y) (hg0 : g 0 y = y)
    (hgy : HasDerivAt (fun s => g s y) (K y) 0)
    (hgA : HasDerivAt (fun s => g s (A y)) (K (A y)) 0)
    (hequiv : ∀ s, A (g s y) = g s (A y)) :
    fderiv ℝ A y (K y) = K (A y) := by
  have h1 : HasDerivAt (fun s => A (g s y)) (fderiv ℝ A y (K y)) 0 :=
    hA.hasFDerivAt.comp_hasDerivAt_of_eq 0 hgy hg0.symm
  have h2 : (fun s => A (g s y)) = fun s => g s (A y) := funext hequiv
  rw [h2] at h1
  exact h1.unique hgA

/-- A family of continuous linear maps with derivative `K` at `0` moves every point `y` with
velocity `K y` at `0`. -/
theorem hasDerivAt_clm_apply {g : ℝ → Space →L[ℝ] Space} {K : Space →L[ℝ] Space}
    (hg : HasDerivAt g K 0) (y : Space) : HasDerivAt (fun s => g s y) (K y) 0 :=
  (hg.clm_apply (hasDerivAt_const (0 : ℝ) y)).congr_deriv (by simp)

/-- **Finite equivariance under a linear family gives infinitesimal equivariance.** If `g s`
are continuous linear maps with `g 0 = 1` and derivative `K` at `0`, and the differentiable
field `A` satisfies `A (g s y) = g s (A y)`, then `DA(y)(K y) = K(A y)` for all `y`. -/
theorem fderiv_eq_of_equivariant_clm {A : Space → Space} {g : ℝ → Space →L[ℝ] Space}
    {K : Space →L[ℝ] Space} (hA : Differentiable ℝ A) (hg0 : g 0 = 1)
    (hg : HasDerivAt g K 0) (hequiv : ∀ s y, A (g s y) = g s (A y)) (y : Space) :
    fderiv ℝ A y (K y) = K (A y) :=
  fderiv_eq_of_equivariant (g := fun s z => g s z) (K := fun z => K z) (hA y)
    (by simp [hg0]) (hasDerivAt_clm_apply hg y) (hasDerivAt_clm_apply hg (A y))
    (fun s => hequiv s y)

/-- The rotations `rotZ` about the `z`-axis have generator `rotGenZ`. -/
theorem rotZ_hasDerivAt_rotGenZ (y : Space) :
    HasDerivAt (fun s => rotZ s y) (rotGenZ y) 0 := by
  rw [rotGenZ_eq_cross]
  exact rotZ_hasDerivAt y

/-- A differentiable field equivariant under all rotations about the `z`-axis is
infinitesimally equivariant: `DA(y)(e_z × y) = e_z × A(y)`. -/
theorem fderiv_rotGenZ_of_rotZ_equivariant {A : Space → Space} (hA : Differentiable ℝ A)
    (hequiv : ∀ s y, A (rotZ s y) = rotZ s (A y)) (y : Space) :
    fderiv ℝ A y (rotGenZ y) = rotGenZ (A y) :=
  fderiv_eq_of_equivariant (g := rotZ) (K := fun z => rotGenZ z) (hA y) (rotZ_zero y)
    (rotZ_hasDerivAt_rotGenZ y) (rotZ_hasDerivAt_rotGenZ (A y)) (fun s => hequiv s y)

/-- **Canonical angular momentum from rotational symmetry of the potential.** If `B = ∇ × A`
with `A` differentiable and equivariant under all rotations about the `z`-axis,
`A (R_s y) = R_s (A y)`, then `m (x × v)_z + qψ` with `ψ(y) = ⟪A(y), e_z × y⟫` is constant
along every Lorentz orbit. -/
theorem canonicalMomentum_conserved_of_rotZ_equivariant {m q : ℝ} {A B : Space → Space}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y)
    (hequiv : ∀ s y, A (rotZ s y) = rotZ s (A y)) (s t : ℝ) :
    canonicalMomentum m q (fun y => ⟪A y, rotGenZ y⟫) x v s
      = canonicalMomentum m q (fun y => ⟪A y, rotGenZ y⟫) x v t :=
  canonicalMomentum_rotGenZ_conserved h hA hcurl
    (fderiv_rotGenZ_of_rotZ_equivariant hA hequiv) s t

/-! ### Bridge to the direct proofs -/

/-- The gradient of `ψ(y) = ⟪A(y), K y⟫` for a skew linear `K`:
`G(y) = DA(y)†(K y) − K(A y)`, with `†` the adjoint. -/
noncomputable def symmetryFluxGrad (A : Space → Space) (K : Space →L[ℝ] Space)
    (y : Space) : Space :=
  ContinuousLinearMap.adjoint (fderiv ℝ A y) (K y) - K (A y)

/-- `⟪G(y), w⟫ = ⟪DA(y) w, K y⟫ − ⟪K(A y), w⟫` for `G = symmetryFluxGrad A K`. -/
theorem inner_symmetryFluxGrad (A : Space → Space) (K : Space →L[ℝ] Space) (y w : Space) :
    ⟪symmetryFluxGrad A K y, w⟫ = ⟪fderiv ℝ A y w, K y⟫ - ⟪K (A y), w⟫ := by
  rw [symmetryFluxGrad, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_comm]

/-- For skew `K` and `A` differentiable at `y`, the function `ψ(y) = ⟪A(y), K y⟫` has
gradient `symmetryFluxGrad A K y` at `y`. -/
theorem hasFDerivAt_symmetryFlux {A : Space → Space} {K : Space →L[ℝ] Space}
    (hK : ∀ w, ⟪K w, w⟫ = 0) {y : Space} (hA : DifferentiableAt ℝ A y) :
    HasFDerivAt (fun z => ⟪A z, K z⟫) (innerSL ℝ (symmetryFluxGrad A K y)) y := by
  have h := hA.hasFDerivAt.inner ℝ (K.hasFDerivAt (x := y))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  have h1 := inner_add_inner_eq_zero_of_skew hK (A y) w
  rw [innerSL_apply_apply, inner_symmetryFluxGrad, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply]
  simp only [ContinuousLinearMap.prod_apply]
  rw [real_inner_comm (A y) (K w)] at h1
  linarith

/-- **Equivalence of the hypotheses.** With `B = ∇ × A` at `y`, the identity
`⟪K y, v × B(y)⟫ = −⟪G(y), v⟫` for all `v` (the hypothesis of the direct proof at `y`), for
`G = symmetryFluxGrad A K`, holds if and only if `DA(y)(K y) = K(A y)`. -/
theorem symmetricFlux_at_iff {A B : Space → Space} {K : Space →L[ℝ] Space} {y : Space}
    (hcurl : B y = fieldCurl A y) :
    (∀ v, ⟪K y, cross v (B y)⟫ = -⟪symmetryFluxGrad A K y, v⟫)
      ↔ fderiv ℝ A y (K y) = K (A y) := by
  have key : ∀ v, ⟪K y, cross v (B y)⟫ + ⟪symmetryFluxGrad A K y, v⟫
      = ⟪fderiv ℝ A y (K y) - K (A y), v⟫ := fun v => by
    rw [hcurl, fieldCurl, real_inner_comm, inner_cross_curlOp, inner_symmetryFluxGrad,
      inner_sub_left]
    ring
  constructor
  · intro h
    have h0 : fderiv ℝ A y (K y) - K (A y) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℝ), ← key, h]
      ring
    exact sub_eq_zero.mp h0
  · intro h v
    have := key v
    rw [h, sub_self, inner_zero_left] at this
    linarith

/-- **Equivalence of the hypotheses, globally.** With `B = ∇ × A`, the hypothesis
`SymmetricFlux B G K` of `noetherMomentum_conserved`, for `G = symmetryFluxGrad A K`, is
equivalent to infinitesimal equivariance of `A` under `K`. -/
theorem symmetricFlux_symmetryFluxGrad_iff {A B : Space → Space} {K : Space →L[ℝ] Space}
    (hcurl : ∀ y, B y = fieldCurl A y) :
    SymmetricFlux B (symmetryFluxGrad A K) (fun y => K y)
      ↔ ∀ y, fderiv ℝ A y (K y) = K (A y) :=
  forall_congr' fun y => symmetricFlux_at_iff (hcurl y)

/-- Infinitesimal equivariance of `A` under `K` gives the hypothesis `SymmetricFlux` of the
direct proof, with `G = symmetryFluxGrad A K`. -/
theorem symmetricFlux_of_equivariant {A B : Space → Space} {K : Space →L[ℝ] Space}
    (hcurl : ∀ y, B y = fieldCurl A y) (hequiv : ∀ y, fderiv ℝ A y (K y) = K (A y)) :
    SymmetricFlux B (symmetryFluxGrad A K) (fun y => K y) :=
  (symmetricFlux_symmetryFluxGrad_iff hcurl).mpr hequiv

/-- A skew continuous linear map is a Killing field, with constant derivative. -/
theorem isKilling_linear {K : Space →L[ℝ] Space} (hK : ∀ w, ⟪K w, w⟫ = 0) :
    IsKilling (fun y => K y) (fun _ => K) :=
  ⟨fun _ => K.hasFDerivAt, fun _ v => hK v⟩

/-- `AxisymmetricFlux B G` is `SymmetricFlux B G` for the generator `rotGenZ`. -/
theorem axisymmetricFlux_iff_symmetricFlux_rotGenZ (B G : Space → Space) :
    AxisymmetricFlux B G ↔ SymmetricFlux B G (fun y => rotGenZ y) := by
  unfold AxisymmetricFlux SymmetricFlux
  simp only [inner_rotGenZ]

/-- Infinitesimal equivariance of `A` under the rotations about the `z`-axis gives the
hypothesis `AxisymmetricFlux` of `canonicalMomentum_conserved`, with
`G = symmetryFluxGrad A rotGenZ`. -/
theorem axisymmetricFlux_of_equivariant {A B : Space → Space}
    (hcurl : ∀ y, B y = fieldCurl A y)
    (hequiv : ∀ y, fderiv ℝ A y (rotGenZ y) = rotGenZ (A y)) :
    AxisymmetricFlux B (symmetryFluxGrad A rotGenZ) :=
  (axisymmetricFlux_iff_symmetricFlux_rotGenZ B _).mpr
    (symmetricFlux_of_equivariant hcurl hequiv)

/-- **Consistency check.** The statement of `noetherMomentum_linear_conserved`, proved from
the direct theorem `noetherMomentum_conserved` instead of TauCeti's Noether theorem. -/
theorem noetherMomentum_linear_conserved_direct {m q : ℝ} {A B : Space → Space}
    {x v : ℝ → Space} {K : Space →L[ℝ] Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : ∀ w, ⟪K w, w⟫ = 0)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hequiv : ∀ y, fderiv ℝ A y (K y) = K (A y)) (s t : ℝ) :
    noetherMomentum m q (fun y => K y) (fun y => ⟪A y, K y⟫) x v s
      = noetherMomentum m q (fun y => K y) (fun y => ⟪A y, K y⟫) x v t :=
  noetherMomentum_conserved h (isKilling_linear hK)
    (fun y => hasFDerivAt_symmetryFlux hK (hA y)) (symmetricFlux_of_equivariant hcurl hequiv)
    s t

/-- **Consistency check.** The statement of `canonicalMomentum_rotGenZ_conserved`, proved
from the direct theorem `canonicalMomentum_conserved` instead of TauCeti's Noether theorem. -/
theorem canonicalMomentum_rotGenZ_conserved_direct {m q : ℝ} {A B : Space → Space}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y)
    (hequiv : ∀ y, fderiv ℝ A y (rotGenZ y) = rotGenZ (A y)) (s t : ℝ) :
    canonicalMomentum m q (fun y => ⟪A y, rotGenZ y⟫) x v s
      = canonicalMomentum m q (fun y => ⟪A y, rotGenZ y⟫) x v t :=
  canonicalMomentum_conserved h (fun y => hasFDerivAt_symmetryFlux inner_rotGenZ_self (hA y))
    (axisymmetricFlux_of_equivariant hcurl hequiv) s t

end PlasmaLean.Kinetic
