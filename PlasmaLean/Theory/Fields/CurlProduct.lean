/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.Maxwell
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The curl product rule

For a scalar field `f` and a vector field `b`, both differentiable at `x`,
`∇ × (f b) = f ∇ × b + ∇f × b` at `x`.

Conventions are those of `PlasmaLean.Theory.Fields.Maxwell`: the curl is applied to the Fréchet
derivative, `curl (fderiv ℝ F x)`, with `(curl L)ₖ = (L e_{k+1})_{k+2} - (L e_{k+2})_{k+1}`;
the gradient is Mathlib's `gradient` (the Riesz representative of `fderiv ℝ f x`), and `cross` is
the Euclidean cross product on `Space`.

Results.

* `curl_add`, `curl_smul`: linearity of `curl`.
* `fderiv_apply_basis`: `Df(x) eᵢ = (∇f(x))ᵢ`.
* `curl_smulRight`: `curl (Df(x) ⊗ w) = ∇f(x) × w`.
* `curl_fderiv_smul`: the product rule.
* sanity: `curl_fderiv_const_smul` (constant `f`) and `curl_fderiv_smul_const` (constant `b`).

The companion identity `∇ · (∇ × b) = 0` for `C²` fields is
`PlasmaLean.Kinetic.GCLittlejohn.divergence_curl`.
-/

open scoped RealInnerProductSpace
public section
noncomputable section
namespace PlasmaLean.Fields

/-- `curl` is additive. -/
theorem curl_add (L M : Space →L[ℝ] Space) : curl (L + M) = curl L + curl M := by
  simp [curl, map_add]

/-- `curl` is homogeneous. -/
theorem curl_smul (c : ℝ) (L : Space →L[ℝ] Space) : curl (c • L) = c • curl L := by
  simp [curl, map_smul]

/-- The derivative of a scalar field along a coordinate vector is the gradient coordinate. -/
theorem fderiv_apply_basis (f : Space → ℝ) (x : Space) (i : Fin 3) :
    fderiv ℝ f x (basis i) = gradient f x i := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

/-- The curl of the rank-one operator `v ↦ (Df(x) v) w` is `∇f(x) × w`. -/
theorem curl_smulRight (f : Space → ℝ) (x : Space) (w : Space) :
    curl ((fderiv ℝ f x).smulRight w) = cross (gradient f x) w := by
  obtain ⟨h0, h1, h2⟩ := curl_coords ((fderiv ℝ f x).smulRight w)
  obtain ⟨c0, c1, c2⟩ := cross_coords (gradient f x) w
  simp only [ContinuousLinearMap.smulRight_apply, fderiv_apply_basis, PiLp.smul_apply,
    smul_eq_mul] at h0 h1 h2
  apply space_ext
  · rw [h0, c0]
  · rw [h1, c1]
  · rw [h2, c2]

/-- **Curl product rule**: `∇ × (f b) = f ∇ × b + ∇f × b` at a point where the scalar field `f` and
the vector field `b` are differentiable. -/
theorem curl_fderiv_smul {f : Space → ℝ} {b : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hb : DifferentiableAt ℝ b x) :
    curl (fderiv ℝ (fun y => f y • b y) x) =
      f x • curl (fderiv ℝ b x) + cross (gradient f x) (b x) := by
  have hd : HasFDerivAt (fun y => f y • b y)
      (f x • fderiv ℝ b x + (fderiv ℝ f x).smulRight (b x)) x :=
    hf.hasFDerivAt.smul hb.hasFDerivAt
  rw [hd.fderiv, curl_add, curl_smul, curl_smulRight]

/-- Sanity check: a constant factor commutes with the curl. -/
theorem curl_fderiv_const_smul (c : ℝ) {b : Space → Space} {x : Space}
    (hb : DifferentiableAt ℝ b x) :
    curl (fderiv ℝ (fun y => c • b y) x) = c • curl (fderiv ℝ b x) := by
  rw [curl_fderiv_smul (f := fun _ => c) (differentiableAt_const c) hb, gradient_fun_const]
  simp [cross]

/-- Sanity check: for a constant vector `w`, `∇ × (f w) = ∇f × w`. -/
theorem curl_fderiv_smul_const {f : Space → ℝ} (w : Space) {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    curl (fderiv ℝ (fun y => f y • w) x) = cross (gradient f x) w := by
  rw [curl_fderiv_smul (b := fun _ => w) hf (differentiableAt_const w), fderiv_const_apply]
  simp [curl]

end PlasmaLean.Fields
