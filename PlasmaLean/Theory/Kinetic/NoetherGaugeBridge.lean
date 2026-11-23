/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.NoetherSymmetryBridge
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The gauge-term bridge, gauge invariance, and finite symmetry for linear potentials

`Theory/Kinetic/NoetherSymmetryBridge` compares the Noether route and the direct route to the
conservation of canonical momentum when the potential `A` is equivariant under the symmetry.
This file treats the case with a gauge term, `DA(y)(K y) = K(A y) + ∇χ(y)`.

**Gauge-term bridge.** For a skew continuous linear `K` and `G = ∇χ`, the function
`ψ(y) = ⟪A(y), K y⟫ − χ(y)` has gradient `symmetryFluxGrad A K y − G y`
(`hasFDerivAt_symmetryFlux_gauge`).

* `symmetricFlux_gauge_at_iff`, `symmetricFlux_gauge_iff`: with `B = ∇ × A`, the hypothesis
  `SymmetricFlux B (symmetryFluxGrad A K − G) K` of the direct proof is equivalent to
  `DA(y)(K y) = K(A y) + G(y)` for all `y`. `G` need not be a gradient here.
* `axisymmetricFlux_gauge_iff`: the same for `AxisymmetricFlux` and `K = rotGenZ`.
* `noetherMomentum_linear_gauge_conserved_direct`,
  `canonicalMomentum_rotGenZ_gauge_conserved_direct`: the statements of
  `noetherMomentum_linear_gauge_conserved` and `canonicalMomentum_rotGenZ_gauge_conserved`,
  proved a second time from the direct theorems, without TauCeti's Noether theorem.
* `symmetricFlux_translation_gauge_iff`, `noetherMomentum_translation_gauge_conserved_direct`:
  the same for a translation (constant generator `e`), with `ψ(y) = ⟪A(y), e⟫ − χ(y)`.

**Gauge invariance.** Let `A' = A + H` with `H = ∇Λ`. The regularity used is: `Λ` has
gradient `H` at every point (`HasFDerivAt Λ (innerSL ℝ (H z)) z`), and `H` is differentiable
at the point considered (so `Λ` is twice differentiable there; no continuity of the second
derivative is assumed).

* `inner_fderiv_gradient_symm`, `fieldCurl_gradient`, `fieldCurl_add_gradient`: the Hessian
  `DH` is symmetric, `∇ × H = 0`, and `∇ × A' = ∇ × A`.
* `equivariant_gauge_add_gradient`: if `DA(K y) = K(A y) + G(y)`, then
  `DA'(K y) = K(A' y) + G'(y)` with `G' = G + (DH(K y) − K(H y))`.
* `hasFDerivAt_gauge_term_add_gradient`: `G'` is the gradient of
  `χ' = χ + ⟪∇Λ, K y⟫`, that is, `χ' = χ + L_K Λ`.
* `gauge_potential_add_gradient`, `noetherMomentum_add_gradient`: with this `χ'` the
  potential `⟪A', K y⟫ − χ'` equals `⟪A, K y⟫ − χ`, and the two conserved momenta are equal.
* `gauge_term_sub_const`, `noetherMomentum_add_gradient_of_gauge_term`: any other gauge term
  `χ'` with gradient `G'` differs from `χ + L_K Λ` by the constant `χ'(0) − χ(0)`, and the
  momentum changes by `−q (χ'(0) − χ(0))`. So the momenta coincide exactly when
  `q (χ'(0) − χ(0)) = 0`.
* `noetherMomentum_add_gradient_naive`: without the gauge term the momentum is not gauge
  invariant: it changes by `q ⟪∇Λ(x), K x⟫`.
* `noetherMomentum_linear_gauge_conserved_add_gradient`: conservation in the gauge `A'`.
* `equivariant_translation_add_gradient`, `hasFDerivAt_translation_gauge_term`: the same
  transformation rule for a translation `e`: `G' = G + DH(e)`, `χ' = χ + ⟪∇Λ, e⟫`.

**Infinitesimal symmetry gives finite symmetry, for linear potentials.**

* `clm_fderiv_equivariant_iff`: for a continuous linear `A`, the infinitesimal condition is
  `A (K y) = K (A y)`.
* `rotZ_eq_rodrigues`: `R_s y = y + sin s • J y + (1 − cos s) • J² y` with `J = rotGenZ`.
* `rotZ_equivariant_of_commute`, `rotZ_equivariant_iff_commute`: a continuous linear `A`
  commutes with `rotGenZ` if and only if `A (R_s y) = R_s (A y)` for all `s`, `y`.
* `exp_smul_equivariant_of_commute`: for any continuous linear `K`, if `A` commutes with `K`
  then `A` commutes with `exp (s K)` for all `s`.

Scope: `A` time-independent, no electric field, `B = ∇ × A` everywhere. Not proved: the
converse "infinitesimal equivariance implies finite equivariance" for a potential `A` that is
not linear (it needs uniqueness of solutions of an ODE); finite equivariance up to a gauge
term; the identification of `exp (s • rotGenZ)` with `rotZ s`; gauge transformations with a
time-dependent `Λ`.
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms WithLp
open TauCeti Topology
open scoped RealInnerProductSpace

/-! ### The gauge-term bridge -/

/-- For skew `K`, `A` differentiable at `y` and `χ` with gradient `G y` at `y`, the function
`ψ(y) = ⟪A(y), K y⟫ − χ(y)` has gradient `symmetryFluxGrad A K y − G y` at `y`. -/
theorem hasFDerivAt_symmetryFlux_gauge {A G : Space → Space} {χ : Space → ℝ}
    {K : Space →L[ℝ] Space} (hK : ∀ w, ⟪K w, w⟫ = 0) {y : Space}
    (hA : DifferentiableAt ℝ A y) (hχ : HasFDerivAt χ (innerSL ℝ (G y)) y) :
    HasFDerivAt (fun z => ⟪A z, K z⟫ - χ z)
      (innerSL ℝ (symmetryFluxGrad A K y - G y)) y := by
  rw [map_sub]
  exact (hasFDerivAt_symmetryFlux hK hA).sub hχ

/-- **Equivalence of the hypotheses with a gauge term, at a point.** With `B = ∇ × A` at `y`,
the identity `⟪K y, v × B(y)⟫ = −⟪symmetryFluxGrad A K y − g, v⟫` for all `v` holds if and
only if `DA(y)(K y) = K(A y) + g`. -/
theorem symmetricFlux_gauge_at_iff {A B : Space → Space} {K : Space →L[ℝ] Space} {y : Space}
    (g : Space) (hcurl : B y = fieldCurl A y) :
    (∀ v, ⟪K y, cross v (B y)⟫ = -⟪symmetryFluxGrad A K y - g, v⟫)
      ↔ fderiv ℝ A y (K y) = K (A y) + g := by
  have key : ∀ v, ⟪K y, cross v (B y)⟫ + ⟪symmetryFluxGrad A K y - g, v⟫
      = ⟪fderiv ℝ A y (K y) - (K (A y) + g), v⟫ := fun v => by
    rw [hcurl, fieldCurl, real_inner_comm, inner_cross_curlOp]
    simp only [inner_sub_left, inner_add_left, inner_symmetryFluxGrad]
    ring
  constructor
  · intro h
    have h0 : fderiv ℝ A y (K y) - (K (A y) + g) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℝ), ← key, h]
      ring
    exact sub_eq_zero.mp h0
  · intro h v
    have := key v
    rw [h, sub_self, inner_zero_left] at this
    linarith

/-- **Equivalence of the hypotheses with a gauge term.** With `B = ∇ × A`, the hypothesis
`SymmetricFlux B (symmetryFluxGrad A K − G) K` of `noetherMomentum_conserved` is equivalent to
equivariance of `A` under `K` up to `G`: `DA(y)(K y) = K(A y) + G(y)`. -/
theorem symmetricFlux_gauge_iff {A B G : Space → Space} {K : Space →L[ℝ] Space}
    (hcurl : ∀ y, B y = fieldCurl A y) :
    SymmetricFlux B (fun y => symmetryFluxGrad A K y - G y) (fun y => K y)
      ↔ ∀ y, fderiv ℝ A y (K y) = K (A y) + G y :=
  forall_congr' fun y => symmetricFlux_gauge_at_iff (G y) (hcurl y)

/-- With `B = ∇ × A`, the hypothesis `AxisymmetricFlux B (symmetryFluxGrad A rotGenZ − G)` of
`canonicalMomentum_conserved` is equivalent to equivariance of `A` under the rotations about
the `z`-axis up to `G`. -/
theorem axisymmetricFlux_gauge_iff {A B G : Space → Space}
    (hcurl : ∀ y, B y = fieldCurl A y) :
    AxisymmetricFlux B (fun y => symmetryFluxGrad A rotGenZ y - G y)
      ↔ ∀ y, fderiv ℝ A y (rotGenZ y) = rotGenZ (A y) + G y :=
  (axisymmetricFlux_iff_symmetricFlux_rotGenZ B _).trans (symmetricFlux_gauge_iff hcurl)

/-- **Consistency check.** The statement of `noetherMomentum_linear_gauge_conserved`, proved
from the direct theorem `noetherMomentum_conserved` instead of TauCeti's Noether theorem. -/
theorem noetherMomentum_linear_gauge_conserved_direct {m q : ℝ} {A B G : Space → Space}
    {χ : Space → ℝ} {x v : ℝ → Space} {K : Space →L[ℝ] Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : ∀ w, ⟪K w, w⟫ = 0)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hχ : ∀ y, HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hequiv : ∀ y, fderiv ℝ A y (K y) = K (A y) + G y) (s t : ℝ) :
    noetherMomentum m q (fun y => K y) (fun y => ⟪A y, K y⟫ - χ y) x v s
      = noetherMomentum m q (fun y => K y) (fun y => ⟪A y, K y⟫ - χ y) x v t :=
  noetherMomentum_conserved h (isKilling_linear hK)
    (fun y => hasFDerivAt_symmetryFlux_gauge hK (hA y) (hχ y))
    ((symmetricFlux_gauge_iff hcurl).mpr hequiv) s t

/-- **Consistency check.** The statement of `canonicalMomentum_rotGenZ_gauge_conserved`,
proved from the direct theorem `canonicalMomentum_conserved` instead of TauCeti's Noether
theorem. -/
theorem canonicalMomentum_rotGenZ_gauge_conserved_direct {m q : ℝ} {A B G : Space → Space}
    {χ : Space → ℝ} {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hχ : ∀ y, HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hequiv : ∀ y, fderiv ℝ A y (rotGenZ y) = rotGenZ (A y) + G y) (s t : ℝ) :
    canonicalMomentum m q (fun y => ⟪A y, rotGenZ y⟫ - χ y) x v s
      = canonicalMomentum m q (fun y => ⟪A y, rotGenZ y⟫ - χ y) x v t :=
  canonicalMomentum_conserved h
    (fun y => hasFDerivAt_symmetryFlux_gauge inner_rotGenZ_self (hA y) (hχ y))
    ((axisymmetricFlux_gauge_iff hcurl).mpr hequiv) s t

/-! ### Translations with a gauge term -/

/-- For `A` differentiable at `y` and `χ` with gradient `G y` at `y`, the function
`ψ(y) = ⟪A(y), e⟫ − χ(y)` has gradient `DA(y)†e − G y` at `y`. -/
theorem hasFDerivAt_translationFlux_gauge {A G : Space → Space} {χ : Space → ℝ} (e : Space)
    {y : Space} (hA : DifferentiableAt ℝ A y) (hχ : HasFDerivAt χ (innerSL ℝ (G y)) y) :
    HasFDerivAt (fun z => ⟪A z, e⟫ - χ z)
      (innerSL ℝ (ContinuousLinearMap.adjoint (fderiv ℝ A y) e - G y)) y := by
  have h := (hA.hasFDerivAt.inner ℝ (hasFDerivAt_const e y)).sub hχ
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [sub_apply, innerSL_apply_apply, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, zero_apply, inner_zero_right,
    zero_add]
  rw [real_inner_comm]

/-- **Equivalence of the hypotheses for a translation with a gauge term.** With `B = ∇ × A`,
the hypothesis `SymmetricFlux B (DA†e − G) e` of `noetherMomentum_conserved` for the constant
generator `e` is equivalent to `DA(y)(e) = G(y)` for all `y`. -/
theorem symmetricFlux_translation_gauge_iff {A B G : Space → Space} (e : Space)
    (hcurl : ∀ y, B y = fieldCurl A y) :
    SymmetricFlux B (fun y => ContinuousLinearMap.adjoint (fderiv ℝ A y) e - G y)
        (fun _ => e)
      ↔ ∀ y, fderiv ℝ A y e = G y := by
  refine forall_congr' fun y => ?_
  have key : ∀ v, ⟪e, cross v (B y)⟫
      + ⟪ContinuousLinearMap.adjoint (fderiv ℝ A y) e - G y, v⟫
      = ⟪fderiv ℝ A y e - G y, v⟫ := fun v => by
    rw [hcurl, fieldCurl, real_inner_comm, inner_cross_curlOp]
    simp only [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
    rw [real_inner_comm e (fderiv ℝ A y v)]
    ring
  constructor
  · intro h
    have h0 : fderiv ℝ A y e - G y = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℝ), ← key, h]
      ring
    exact sub_eq_zero.mp h0
  · intro h v
    have := key v
    rw [h, sub_self, inner_zero_left] at this
    linarith

/-- **Canonical momentum along a translation with a gauge term, by the direct route.** If
`B = ∇ × A` with `A` differentiable and `DA(y)(e) = ∇χ(y)`, then
`m⟪e, v⟫ + q(⟪A(x), e⟫ − χ(x))` is constant along every Lorentz orbit. -/
theorem noetherMomentum_translation_gauge_conserved_direct {m q : ℝ} {A B G : Space → Space}
    {χ : Space → ℝ} {x v : ℝ → Space} {e : Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y) (hχ : ∀ y, HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hequiv : ∀ y, fderiv ℝ A y e = G y) (s t : ℝ) :
    noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫ - χ y) x v s
      = noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫ - χ y) x v t :=
  noetherMomentum_conserved h (translation_killing e)
    (fun y => hasFDerivAt_translationFlux_gauge e (hA y) (hχ y))
    ((symmetricFlux_translation_gauge_iff e hcurl).mpr hequiv) s t

/-! ### Gauge invariance -/

/-- **Symmetry of the Hessian.** If `Λ` has gradient `H` near `y` and `H` is differentiable
at `y`, then `⟪DH(y) v, w⟫ = ⟪DH(y) w, v⟫`. -/
theorem inner_fderiv_gradient_symm {Λ : Space → ℝ} {H : Space → Space} {y : Space}
    (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z) (hH : DifferentiableAt ℝ H y)
    (v w : Space) : ⟪fderiv ℝ H y v, w⟫ = ⟪fderiv ℝ H y w, v⟫ := by
  have h2 : HasFDerivAt (fun z => (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) (H z))
      ((innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).comp (fderiv ℝ H y)) y :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp y hH.hasFDerivAt
  exact second_derivative_symmetric (f := Λ) hΛ h2 v w

/-- A gradient field is curl free: if `Λ` has gradient `H` and `H` is differentiable at `y`,
then `∇ × H = 0` at `y`. -/
theorem fieldCurl_gradient {Λ : Space → ℝ} {H : Space → Space} {y : Space}
    (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z) (hH : DifferentiableAt ℝ H y) :
    fieldCurl H y = 0 := by
  rw [fieldCurl, curlOp_eq_zero_iff]
  intro i j
  have h := inner_fderiv_gradient_symm hΛ hH (coordVec j) (coordVec i)
  simpa [EuclideanSpace.inner_single_right] using h

/-- **A gauge transformation does not change the field.** If `A` and `H = ∇Λ` are
differentiable at `y`, then `∇ × (A + ∇Λ) = ∇ × A` at `y`. -/
theorem fieldCurl_add_gradient {A H : Space → Space} {Λ : Space → ℝ} {y : Space}
    (hA : DifferentiableAt ℝ A y) (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z)
    (hH : DifferentiableAt ℝ H y) :
    fieldCurl (fun z => A z + H z) y = fieldCurl A y := by
  have h0 := fieldCurl_gradient hΛ hH
  rw [fieldCurl] at h0
  have hc : curlOp (fderiv ℝ A y + fderiv ℝ H y)
      = curlOp (fderiv ℝ A y) + curlOp (fderiv ℝ H y) := by
    ext k
    fin_cases k <;> simp [curlOp] <;> ring
  rw [fieldCurl, fieldCurl, fderiv_fun_add hA hH, hc, h0, add_zero]

/-- For a gradient field `H = ∇Λ` the gradient `symmetryFluxGrad H K` of `⟪H, K y⟫` is
`DH(y)(K y) − K(H y)`: the adjoint of the Hessian is the Hessian. -/
theorem symmetryFluxGrad_gradient {Λ : Space → ℝ} {H : Space → Space} {y : Space}
    (K : Space →L[ℝ] Space) (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z)
    (hH : DifferentiableAt ℝ H y) :
    symmetryFluxGrad H K y = fderiv ℝ H y (K y) - K (H y) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_symmetryFluxGrad, inner_sub_left, inner_fderiv_gradient_symm hΛ hH w (K y)]

/-- **Transformation of the equivariance defect.** If `DA(y)(K y) = K(A y) + g`, then for
`A' = A + H` one has `DA'(y)(K y) = K(A' y) + g'` with `g' = g + (DH(y)(K y) − K(H y))`.
Only differentiability of `A` and `H` at `y` is used. -/
theorem equivariant_gauge_add_gradient {A H : Space → Space} {K : Space →L[ℝ] Space}
    {y g : Space} (hA : DifferentiableAt ℝ A y) (hH : DifferentiableAt ℝ H y)
    (hequiv : fderiv ℝ A y (K y) = K (A y) + g) :
    fderiv ℝ (fun z => A z + H z) y (K y)
      = K (A y + H y) + (g + (fderiv ℝ H y (K y) - K (H y))) := by
  rw [fderiv_fun_add hA hH, add_apply, hequiv, map_add]
  abel

/-- **Transformation of the gauge term.** If `χ` has gradient `G y` at `y`, `Λ` has gradient
`H`, `H` is differentiable at `y` and `K` is skew, then `χ' = χ + ⟪∇Λ, K y⟫` has gradient
`G y + (DH(y)(K y) − K(H y))` at `y`: the defect of `A + ∇Λ` is again a gradient. -/
theorem hasFDerivAt_gauge_term_add_gradient {G H : Space → Space} {χ Λ : Space → ℝ}
    {K : Space →L[ℝ] Space} (hK : ∀ w, ⟪K w, w⟫ = 0) {y : Space}
    (hχ : HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z) (hH : DifferentiableAt ℝ H y) :
    HasFDerivAt (fun z => χ z + ⟪H z, K z⟫)
      (innerSL ℝ (G y + (fderiv ℝ H y (K y) - K (H y)))) y := by
  rw [map_add, ← symmetryFluxGrad_gradient K hΛ hH]
  exact hχ.add (hasFDerivAt_symmetryFlux hK hH)

/-- **The potential of the conserved momentum is gauge invariant.** With the gauge term
`χ' = χ + ⟪H, K y⟫`, the potential `⟪A + H, K y⟫ − χ'` equals `⟪A, K y⟫ − χ`. -/
theorem gauge_potential_add_gradient (A H : Space → Space) (χ : Space → ℝ)
    (K : Space → Space) (y : Space) :
    ⟪A y + H y, K y⟫ - (χ y + ⟪H y, K y⟫) = ⟪A y, K y⟫ - χ y := by
  rw [inner_add_left]
  ring

/-- **The conserved momentum is gauge invariant.** The Noether momentum of `A' = A + H` with
gauge term `χ' = χ + ⟪H, K y⟫` equals the Noether momentum of `A` with gauge term `χ`. -/
theorem noetherMomentum_add_gradient (m q : ℝ) (A H : Space → Space) (χ : Space → ℝ)
    (K : Space → Space) (x v : ℝ → Space) (t : ℝ) :
    noetherMomentum m q K (fun y => ⟪A y + H y, K y⟫ - (χ y + ⟪H y, K y⟫)) x v t
      = noetherMomentum m q K (fun y => ⟪A y, K y⟫ - χ y) x v t := by
  simp only [noetherMomentum, gauge_potential_add_gradient]

/-- **Without the gauge term the momentum is not gauge invariant.** The momentum
`m⟪K x, v⟫ + q⟪A'(x), K x⟫` of `A' = A + H` differs from that of `A` by `q⟪H(x), K x⟫`. -/
theorem noetherMomentum_add_gradient_naive (m q : ℝ) (A H : Space → Space)
    (K : Space → Space) (x v : ℝ → Space) (t : ℝ) :
    noetherMomentum m q K (fun y => ⟪A y + H y, K y⟫) x v t
      = noetherMomentum m q K (fun y => ⟪A y, K y⟫) x v t + q * ⟪H (x t), K (x t)⟫ := by
  simp only [noetherMomentum, inner_add_left]
  ring

/-- Two functions with the same gradient everywhere differ by a constant:
`χ₂(y) − χ₁(y) = χ₂(0) − χ₁(0)`. -/
theorem gauge_term_sub_const {χ₁ χ₂ : Space → ℝ} {G : Space → Space}
    (h₁ : ∀ y, HasFDerivAt χ₁ (innerSL ℝ (G y)) y)
    (h₂ : ∀ y, HasFDerivAt χ₂ (innerSL ℝ (G y)) y) (y : Space) :
    χ₂ y - χ₁ y = χ₂ 0 - χ₁ 0 := by
  have hd : ∀ z, HasFDerivAt (fun w => χ₂ w - χ₁ w) (0 : Space →L[ℝ] ℝ) z := fun z => by
    have h := (h₂ z).sub (h₁ z)
    rwa [sub_self] at h
  exact is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun z => (hd z).differentiableAt)
    (fun z => (hd z).fderiv) y 0

/-- **Dependence of the conserved momentum on the gauge.** Let `A' = A + H` with `H = ∇Λ`,
let `χ` have gradient `G`, and let `χ'` be any function with gradient
`G' = G + (DH(K y) − K(H y))`, the defect of `A'`. Then the Noether momentum of `(A', χ')`
is that of `(A, χ)` minus the constant `q (χ'(0) − χ(0))`. -/
theorem noetherMomentum_add_gradient_of_gauge_term {m q : ℝ} {A G H : Space → Space}
    {χ χ' Λ : Space → ℝ} {K : Space →L[ℝ] Space} (hK : ∀ w, ⟪K w, w⟫ = 0)
    (hχ : ∀ y, HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z) (hH : Differentiable ℝ H)
    (hχ' : ∀ y, HasFDerivAt χ' (innerSL ℝ (G y + (fderiv ℝ H y (K y) - K (H y)))) y)
    (x v : ℝ → Space) (t : ℝ) :
    noetherMomentum m q (fun y => K y) (fun y => ⟪A y + H y, K y⟫ - χ' y) x v t
      = noetherMomentum m q (fun y => K y) (fun y => ⟪A y, K y⟫ - χ y) x v t
        - q * (χ' 0 - χ 0) := by
  have hc := gauge_term_sub_const
    (fun y => hasFDerivAt_gauge_term_add_gradient hK (hχ y) hΛ (hH y)) hχ' (x t)
  simp only [map_zero, inner_zero_right, add_zero] at hc
  simp only [noetherMomentum, inner_add_left]
  linear_combination (-q) * hc

/-- **Conservation in the transformed gauge.** If `B = ∇ × A`, `A` is equivariant under the
skew `K` up to `G = ∇χ`, and `A' = A + ∇Λ` with `∇Λ` differentiable, then the Noether
momentum of `A'` with gauge term `χ' = χ + ⟪∇Λ, K y⟫` is constant along every Lorentz
orbit. It is proved by applying the direct theorem to `A'`; by `noetherMomentum_add_gradient`
it is the same function as the momentum of `(A, χ)`. -/
theorem noetherMomentum_linear_gauge_conserved_add_gradient {m q : ℝ}
    {A B G H : Space → Space} {χ Λ : Space → ℝ} {x v : ℝ → Space} {K : Space →L[ℝ] Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : ∀ w, ⟪K w, w⟫ = 0)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hχ : ∀ y, HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hequiv : ∀ y, fderiv ℝ A y (K y) = K (A y) + G y)
    (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z) (hH : Differentiable ℝ H) (s t : ℝ) :
    noetherMomentum m q (fun y => K y)
        (fun y => ⟪A y + H y, K y⟫ - (χ y + ⟪H y, K y⟫)) x v s
      = noetherMomentum m q (fun y => K y)
        (fun y => ⟪A y + H y, K y⟫ - (χ y + ⟪H y, K y⟫)) x v t :=
  noetherMomentum_linear_gauge_conserved_direct (A := fun z => A z + H z)
    (G := fun y => G y + (fderiv ℝ H y (K y) - K (H y))) (χ := fun z => χ z + ⟪H z, K z⟫)
    h hK (hA.add hH)
    (fun y => (hcurl y).trans (fieldCurl_add_gradient (hA y) hΛ (hH y)).symm)
    (fun y => hasFDerivAt_gauge_term_add_gradient hK (hχ y) hΛ (hH y))
    (fun y => equivariant_gauge_add_gradient (hA y) (hH y) (hequiv y)) s t

/-- **Transformation of the defect for a translation.** If `DA(y)(e) = g`, then for
`A' = A + H` one has `DA'(y)(e) = g + DH(y)(e)`. -/
theorem equivariant_translation_add_gradient {A H : Space → Space} {y g : Space} (e : Space)
    (hA : DifferentiableAt ℝ A y) (hH : DifferentiableAt ℝ H y)
    (hequiv : fderiv ℝ A y e = g) :
    fderiv ℝ (fun z => A z + H z) y e = g + fderiv ℝ H y e := by
  rw [fderiv_fun_add hA hH, add_apply, hequiv]

/-- **Transformation of the gauge term for a translation.** If `χ` has gradient `G y` at
`y`, `Λ` has gradient `H` and `H` is differentiable at `y`, then `χ' = χ + ⟪∇Λ, e⟫` has
gradient `G y + DH(y)(e)` at `y`. -/
theorem hasFDerivAt_translation_gauge_term {G H : Space → Space} {χ Λ : Space → ℝ}
    (e : Space) {y : Space} (hχ : HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hΛ : ∀ z, HasFDerivAt Λ (innerSL ℝ (H z)) z) (hH : DifferentiableAt ℝ H y) :
    HasFDerivAt (fun z => χ z + ⟪H z, e⟫) (innerSL ℝ (G y + fderiv ℝ H y e)) y := by
  have h := hχ.add (hH.hasFDerivAt.inner ℝ (hasFDerivAt_const e y))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [add_apply, innerSL_apply_apply, inner_add_left, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, zero_apply, inner_zero_right,
    zero_add]
  rw [inner_fderiv_gradient_symm hΛ hH e w]

/-! ### Infinitesimal symmetry gives finite symmetry, for linear potentials -/

/-- For a continuous linear `A` the infinitesimal equivariance condition
`DA(y)(K y) = K(A y)` is the commutation `A (K y) = K (A y)`. -/
theorem clm_fderiv_equivariant_iff (A : Space →L[ℝ] Space) (K : Space → Space) (y : Space) :
    fderiv ℝ A y (K y) = K (A y) ↔ A (K y) = K (A y) := by
  rw [A.fderiv]

/-- The rotation about the `z`-axis in terms of its generator `J = rotGenZ`:
`R_s y = y + sin s • J y + (1 − cos s) • J² y`. -/
theorem rotZ_eq_rodrigues (s : ℝ) (y : Space) :
    rotZ s y = y + Real.sin s • rotGenZ y + (1 - Real.cos s) • rotGenZ (rotGenZ y) := by
  obtain ⟨r0, r1, r2⟩ := rotZ_coords s y
  obtain ⟨a0, a1, a2⟩ := rotGenZ_coords y
  obtain ⟨b0, b1, b2⟩ := rotGenZ_coords (rotGenZ y)
  have h0 : rotZ s y 0
      = (y + Real.sin s • rotGenZ y + (1 - Real.cos s) • rotGenZ (rotGenZ y)) 0 := by
    simp only [r0, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, a0, b0, a1]
    ring
  have h1 : rotZ s y 1
      = (y + Real.sin s • rotGenZ y + (1 - Real.cos s) • rotGenZ (rotGenZ y)) 1 := by
    simp only [r1, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, a1, b1, a0]
    ring
  have h2 : rotZ s y 2
      = (y + Real.sin s • rotGenZ y + (1 - Real.cos s) • rotGenZ (rotGenZ y)) 2 := by
    simp only [r2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, a2, b2]
    ring
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **Infinitesimal symmetry gives finite symmetry, for a linear potential.** A continuous
linear `A` that commutes with the generator `rotGenZ` is equivariant under every rotation
about the `z`-axis. -/
theorem rotZ_equivariant_of_commute (A : Space →L[ℝ] Space)
    (h : ∀ y, A (rotGenZ y) = rotGenZ (A y)) (s : ℝ) (y : Space) :
    A (rotZ s y) = rotZ s (A y) := by
  rw [rotZ_eq_rodrigues, rotZ_eq_rodrigues, map_add, map_add, map_smul, map_smul, h, h, h]

/-- For a continuous linear `A`, equivariance under all rotations about the `z`-axis is
equivalent to commutation with the generator `rotGenZ`. -/
theorem rotZ_equivariant_iff_commute (A : Space →L[ℝ] Space) :
    (∀ s y, A (rotZ s y) = rotZ s (A y)) ↔ ∀ y, A (rotGenZ y) = rotGenZ (A y) := by
  constructor
  · intro h y
    have h1 := fderiv_rotGenZ_of_rotZ_equivariant A.differentiable h y
    rwa [A.fderiv] at h1
  · intro h s y
    exact rotZ_equivariant_of_commute A h s y

/-- **Infinitesimal symmetry gives finite symmetry, for a linear potential and a general
linear generator.** If the continuous linear maps `A` and `K` commute, then `A` commutes with
`exp (s K)` for every `s`. Skewness of `K` is not used. -/
theorem exp_smul_equivariant_of_commute (A K : Space →L[ℝ] Space)
    (h : ∀ y, A (K y) = K (A y)) (s : ℝ) (y : Space) :
    A (NormedSpace.exp (s • K) y) = NormedSpace.exp (s • K) (A y) := by
  have hc : Commute A (s • K) := by
    refine ContinuousLinearMap.ext fun z => ?_
    simp [h]
  have he := hc.exp_right
  exact congrArg (fun L : Space →L[ℝ] Space => L y) he

end PlasmaLean.Kinetic
