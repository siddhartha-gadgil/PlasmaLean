/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Fields.VectorCalculus
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Lie-derivative/gradient commutator in Euclidean space

For a vector field `X` and a scalar field `f` on Euclidean space,

`[X, ∇f] = ∇(X f) - (DX + DXᵀ) ∇f`,

where `X f = ⟪X, ∇f⟫` is the derivative of `f` along `X` and `[V, W] = DW · V - DV · W` is
Mathlib's `VectorField.lieBracket`. The operator `DX + DXᵀ` is the metric Lie derivative
`L_X g` with one index raised, so this is the Euclidean case of the identity
`[X, grad_g f] = grad_g (X f) - (L_X g)^♯ (grad_g f)`.

Consequence: unless `X` is a
Killing field (`DX + DXᵀ = 0`), `X f = 0` does not make `∇f` invariant under `X`. The concrete
counterexample is in `LeanTheory.Sanity.QuasisymmetryNotSymmetry`.

Results.

* `hasGradientAt_inner_gradient`: the gradient of `y ↦ ⟪X y, ∇f y⟫` is `DXᵀ ∇f + D(∇f) X`,
  provided the Hessian `D(∇f)(x)` is self-adjoint.
* `dualToSpace`, `inner_dualToSpace`, `gradient_eq_dualToSpace`, `hasFDerivAt_gradient`: the
  gradient as the real-linear Riesz map applied to `Df`, and its derivative for `C²` fields.
* `isSelfAdjoint_fderiv_gradient`: the Hessian is self-adjoint when `f` is `C²` near `x`.
* `lieBracket_gradient`: the commutator identity, with the Hessian symmetry as a hypothesis.
* `lieBracket_gradient_of_contDiffAt`: the same identity for `C²` scalar fields.
* `lieBracket_gradient_of_killing`: sanity case, for `DX` skew-adjoint the bracket is `∇(X f)`.

The general Cartesian Laplacian commutator `[X·∇, Δ]` is not formalized here.
-/

open scoped RealInnerProductSpace
open InnerProductSpace ContinuousLinearMap VectorField

public section
noncomputable section
namespace LeanTheory.Fields

/-- The gradient of `y ↦ ⟪X y, ∇f y⟫` is `DX(x)ᵀ ∇f(x) + D(∇f)(x) X(x)` when `X` and `∇f` are
differentiable at `x` and the Hessian `D(∇f)(x)` is self-adjoint. -/
theorem hasGradientAt_inner_gradient {X : Space → Space} {f : Space → ℝ} {x : Space}
    (hX : DifferentiableAt ℝ X x) (hg : DifferentiableAt ℝ (gradient f) x)
    (hsymm : IsSelfAdjoint (fderiv ℝ (gradient f) x)) :
    HasGradientAt (fun y => ⟪X y, gradient f y⟫)
      (adjoint (fderiv ℝ X x) (gradient f x) + fderiv ℝ (gradient f) x (X x)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hX.hasFDerivAt.inner ℝ hg.hasFDerivAt using 1
  ext v
  have hH : ⟪fderiv ℝ (gradient f) x (X x), v⟫ = ⟪X x, fderiv ℝ (gradient f) x v⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsymm.adjoint_eq]
  simp only [toDual_apply_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, hH]
  rw [real_inner_comm (gradient f x), add_comm]

/-- The Riesz map `StrongDual ℝ Space → Space` as a real-linear continuous map:
`φ ↦ ∑ᵢ φ(eᵢ) eᵢ`. -/
@[expose] def dualToSpace : StrongDual ℝ Space →L[ℝ] Space :=
  ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ ℝ (basis i)).smulRight (basis i)

/-- `dualToSpace` is the Riesz representative: `⟪dualToSpace φ, w⟫ = φ w`. -/
theorem inner_dualToSpace (φ : StrongDual ℝ Space) (w : Space) : ⟪dualToSpace φ, w⟫ = φ w := by
  have hw : w = w 0 • basis 0 + w 1 • basis 1 + w 2 • basis 2 :=
    space_ext (by simp) (by simp) (by simp)
  conv_rhs => rw [hw]
  simp [dualToSpace, Fin.sum_univ_three, inner_add_left, inner_smul_left,
    EuclideanSpace.inner_single_left, map_add, map_smul]
  ring

/-- The gradient is the Riesz map applied to the derivative. -/
theorem gradient_eq_dualToSpace (f : Space → ℝ) :
    gradient f = fun y => dualToSpace (fderiv ℝ f y) := by
  funext y
  apply ext_inner_right ℝ
  intro w
  rw [inner_dualToSpace, inner_gradient_left]

/-- If `f` is `C²` at `x`, then `∇f` has derivative `dualToSpace ∘ D²f(x)` at `x`. -/
theorem hasFDerivAt_gradient {f : Space → ℝ} {x : Space} (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (dualToSpace.comp (fderiv ℝ (fderiv ℝ f) x)) x := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [gradient_eq_dualToSpace]
  exact dualToSpace.hasFDerivAt.comp x hdf.hasFDerivAt

/-- The Hessian `D(∇f)(x)` of a scalar field that is `C²` at `x` is self-adjoint. -/
theorem isSelfAdjoint_fderiv_gradient {f : Space → ℝ} {x : Space} (hf : ContDiffAt ℝ 2 f x) :
    IsSelfAdjoint (fderiv ℝ (gradient f) x) := by
  have hsym : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  simp only [ContinuousLinearMap.coe_coe, (hasFDerivAt_gradient hf).fderiv,
    ContinuousLinearMap.comp_apply]
  rw [inner_dualToSpace, real_inner_comm, inner_dualToSpace, hsym v w]

/-- **Lie-derivative/gradient commutator.** If `X` and `∇f` are differentiable at `x` and the
Hessian of `f` at `x` is self-adjoint, then
`∇(X f)(x) - [X, ∇f](x) = (DX(x) + DX(x)ᵀ) ∇f(x)`, with `X f = ⟪X, ∇f⟫`. -/
theorem lieBracket_gradient {X : Space → Space} {f : Space → ℝ} {x : Space}
    (hX : DifferentiableAt ℝ X x) (hg : DifferentiableAt ℝ (gradient f) x)
    (hsymm : IsSelfAdjoint (fderiv ℝ (gradient f) x)) :
    gradient (fun y => ⟪X y, gradient f y⟫) x - lieBracket ℝ X (gradient f) x =
      (fderiv ℝ X x + adjoint (fderiv ℝ X x)) (gradient f x) := by
  rw [(hasGradientAt_inner_gradient hX hg hsymm).gradient, lieBracket,
    add_apply]
  abel

/-- The commutator identity `lieBracket_gradient` for a scalar field `f` that is `C²` near `x`
and a vector field `X` differentiable at `x`. -/
theorem lieBracket_gradient_of_contDiffAt {X : Space → Space} {f : Space → ℝ} {x : Space}
    (hX : DifferentiableAt ℝ X x) (hf : ContDiffAt ℝ 2 f x) :
    gradient (fun y => ⟪X y, gradient f y⟫) x - lieBracket ℝ X (gradient f) x =
      (fderiv ℝ X x + adjoint (fderiv ℝ X x)) (gradient f x) :=
  lieBracket_gradient hX (hasFDerivAt_gradient hf).differentiableAt
    (isSelfAdjoint_fderiv_gradient hf)

/-- Sanity case: for a Killing field at `x` (`DX(x)` skew-adjoint, i.e. `L_X g = 0`) the
commutator with a gradient is the gradient of the derivative along `X`. -/
theorem lieBracket_gradient_of_killing {X : Space → Space} {f : Space → ℝ} {x : Space}
    (hX : DifferentiableAt ℝ X x) (hf : ContDiffAt ℝ 2 f x)
    (hkill : adjoint (fderiv ℝ X x) = -fderiv ℝ X x) :
    lieBracket ℝ X (gradient f) x = gradient (fun y => ⟪X y, gradient f y⟫) x := by
  have h := lieBracket_gradient_of_contDiffAt hX hf
  rw [hkill, add_neg_cancel, zero_apply, sub_eq_zero] at h
  exact h.symm

end LeanTheory.Fields
