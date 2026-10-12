/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.BiotSavart
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Spatial inverse-cube kernel: first derivative bound

The bound proved here is conservative (4/|r|³), not the optimal 2/|r|³ bound
from the radial/tangential eigenspaces. It opens a quantitative full-region
continuity route for filament fields while explicitly excluding the singularity.
-/
public section
noncomputable section
namespace PlasmaLean.Fields

/-- The radial kernel underlying the Biot–Savart integrand. -/
@[expose] def inverseCube (r : Space) : Space := (‖r‖ ^ 3)⁻¹ • r

private theorem scalar_inverse_cube_derivative {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun z : ℝ => (z ^ 3)⁻¹) (-3 / s ^ 4) s := by
  convert ((hasDerivAt_id s).pow 3).inv (pow_ne_zero _ hs) using 1
  · funext z
    rfl
  · change -3 / s ^ 4 = -(3 * s ^ (3 - 1) * 1) / (s ^ 3) ^ 2
    norm_num
    field_simp

/-- The norm is differentiable at a nonzero Euclidean vector. -/
theorem norm_differentiable {r : Space} (hr : r ≠ 0) :
    DifferentiableAt ℝ (fun x : Space => ‖x‖) r :=
  (differentiableAt_id : DifferentiableAt ℝ (id : Space → Space) r).norm ℝ hr

/-- Actual Fréchet derivative of the spatial kernel away from the singularity. -/
theorem inverseCube_derivative {r : Space} (hr : r ≠ 0) :
    HasFDerivAt inverseCube
      ((‖r‖ ^ 3)⁻¹ • ContinuousLinearMap.id ℝ Space +
        ((-3 / ‖r‖ ^ 4) • fderiv ℝ (fun x : Space => ‖x‖) r).smulRight r) r := by
  have hn := (norm_differentiable hr).hasFDerivAt
  have hs := (scalar_inverse_cube_derivative (norm_ne_zero_iff.mpr hr)).comp_hasFDerivAt r hn
  exact hs.smul (hasFDerivAt_id r)

/-- A conservative operator-norm estimate on the actual three-dimensional derivative. -/
theorem inverseCube_derivative_bound {r : Space} (hr : r ≠ 0) :
    ‖fderiv ℝ inverseCube r‖ ≤ 4 / ‖r‖ ^ 3 := by
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  rw [(inverseCube_derivative hr).fderiv]
  calc
    _ ≤ ‖(‖r‖ ^ 3)⁻¹ • ContinuousLinearMap.id ℝ Space‖ +
        ‖((-3 / ‖r‖ ^ 4) • fderiv ℝ (fun x : Space => ‖x‖) r).smulRight r‖ :=
      norm_add_le _ _
    _ = (‖r‖ ^ 3)⁻¹ + (3 / ‖r‖ ^ 4) * ‖r‖ := by
      simp [norm_smul, ContinuousLinearMap.norm_smulRight_apply,
        norm_fderiv_norm (norm_differentiable hr)]
    _ = 4 / ‖r‖ ^ 3 := by field_simp; ring

/-- A source-separated convex region has a uniform spatial difference bound.
Separation is required on the whole region, including the segment between points. -/
theorem inverseCube_difference (source : Space) {s : Set Space} (hs : Convex ℝ s)
    {d : ℝ} (hd : 0 < d) (sep : ∀ x ∈ s, d ≤ ‖x - source‖)
    {x y : Space} (hx : x ∈ s) (hy : y ∈ s) :
    ‖inverseCube (x - source) - inverseCube (y - source)‖ ≤
      (4 / d ^ 3) * ‖x - y‖ := by
  have hn (z : Space) (hz : z ∈ s) : z - source ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hd (sep z hz))
  have hf (z : Space) (hz : z ∈ s) : HasFDerivAt
      (fun w => inverseCube (w - source)) (fderiv ℝ inverseCube (z - source)) z := by
    have h := (inverseCube_derivative (hn z hz)).differentiableAt.hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const source)
    convert h using 1 <;> simp [Function.comp_def]
  apply hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hf z hz).hasFDerivWithinAt) ?_ hy hx
  intro z hz
  exact (inverseCube_derivative_bound (hn z hz)).trans
    (div_le_div₀ (by norm_num) (by rfl) (by positivity)
      (pow_le_pow_left₀ (le_of_lt hd) (sep z hz) 3))

end PlasmaLean.Fields
