/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.InverseCube

/-!
# Full-region spatial variation of continuous filament fields

An explicit conservative Lipschitz bound follows from the spatial inverse-cube
derivative and continuous integration. No differentiation under the integral is
used. This bounds field variation in 3-D, but is not a proof of Maxwell identities
or of a second/higher field derivative. Source separation covers the whole convex
observation region, not just its endpoints or a grid.
-/
public section
noncomputable section
namespace PlasmaLean.Fields
open WithLp

/-- Linearity of the Euclidean cross product in its second argument. -/
theorem cross_sub_right (v x y : Space) : cross v (x - y) = cross v x - cross v y := by
  simp only [cross, ofLp_sub, map_sub, toLp_sub]

/-- Scalar multiplication commutes with the second cross-product argument. -/
theorem cross_smul_right (v x : Space) (a : ℝ) : cross v (a • x) = a • cross v x := by
  simp only [cross, ofLp_smul, map_smul, toLp_smul]

/-- Rewriting the filament kernel in terms of the spatial radial kernel. -/
theorem filamentKernel_eq_cross_inverseCube (c : ℝ → Space) (t : ℝ) (x : Space) :
    filamentKernel c t x = cross (deriv c t) (inverseCube (x - c t)) := by
  simp only [inverseCube, cross_smul_right, filamentKernel]

/-- Pointwise spatial variation of the kernel on a source-separated convex set. -/
theorem filamentKernel_difference (c : ℝ → Space) (t : ℝ)
    {s : Set Space} (hs : Convex ℝ s) {d V : ℝ} (hd : 0 < d)
    (sep : ∀ x ∈ s, d ≤ ‖x - c t‖) (speed : ‖deriv c t‖ ≤ V)
    {x y : Space} (hx : x ∈ s) (hy : y ∈ s) :
    ‖filamentKernel c t x - filamentKernel c t y‖ ≤
      (V * (4 / d ^ 3)) * ‖x - y‖ := by
  simp only [filamentKernel_eq_cross_inverseCube, ← cross_sub_right]
  have hb := inverseCube_difference (c t) hs hd sep hx hy
  calc
    _ ≤ ‖deriv c t‖ * ‖inverseCube (x - c t) - inverseCube (y - c t)‖ := norm_cross_le _ _
    _ ≤ V * ((4 / d ^ 3) * ‖x - y‖) :=
      mul_le_mul speed hb (norm_nonneg _) (le_trans (norm_nonneg _) speed)
    _ = _ := by ring

/-- The continuous integral transfers the spatial variation bound. Integrability
and source separation must hold for every observation point in the same region. -/
theorem filamentField_difference (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ)
    {s : Set Space} (hs : Convex ℝ s) {d V : ℝ} (hd : 0 < d)
    (sep : ∀ t ∈ Set.uIoc a b, ∀ x ∈ s, d ≤ ‖x - c t‖)
    (speed : ∀ t ∈ Set.uIoc a b, ‖deriv c t‖ ≤ V)
    (hint : ∀ x ∈ s, IntervalIntegrable (fun t => filamentKernel c t x)
      MeasureTheory.volume a b)
    {x y : Space} (hx : x ∈ s) (hy : y ∈ s) :
    ‖filamentField μ₀ I c a b x - filamentField μ₀ I c a b y‖ ≤
      (|μ₀ * I / (4 * Real.pi)| * (V * (4 / d ^ 3) * |b - a|)) * ‖x - y‖ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => filamentKernel_difference c t hs hd (sep t ht) (speed t ht) hx hy)
  unfold filamentField
  rw [← smul_sub, ← intervalIntegral.integral_sub (hint x hx) (hint y hy), norm_smul,
    Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left hb (abs_nonneg (μ₀ * I / (4 * Real.pi)))
  convert h using 1
  ring

end PlasmaLean.Fields
