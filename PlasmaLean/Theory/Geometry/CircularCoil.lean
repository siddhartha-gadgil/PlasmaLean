/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.BiotSavart
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Exact circular filament geometry

An oriented circular filament in a horizontal plane, in Euclidean three-space.
Coordinates R and z₀ use metres; the parameter is a dimensionless angle. This
analytic geometry is a demonstrator fixture, not an optimized stellarator coil.
-/
public section
noncomputable section
namespace PlasmaLean.Geometry
open Fields WithLp Matrix

/-- Counterclockwise circular centerline, viewed from positive z. -/
@[expose] def circularCoil (R z₀ t : ℝ) : Space :=
  toLp 2 ![R * Real.cos t, R * Real.sin t, z₀]

/-- Exact tangent with respect to the dimensionless angular parameter. -/
@[expose] def circularTangent (R t : ℝ) : Space :=
  toLp 2 ![-R * Real.sin t, R * Real.cos t, 0]

/-- The declared tangent is the actual derivative, not separate supplied data. -/
theorem circularCoil_derivative (R z₀ t : ℝ) :
    HasDerivAt (circularCoil R z₀) (circularTangent R t) t := by
  have hd : HasDerivAt (fun s => ![R * Real.cos s, R * Real.sin s, z₀])
      ![-R * Real.sin t, R * Real.cos t, 0] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using (Real.hasDerivAt_cos t).const_mul R
    · simpa using (Real.hasDerivAt_sin t).const_mul R
    · simpa using hasDerivAt_const t z₀
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t hd

/-- The filament closes after one full angular period. -/
theorem circularCoil_periodic (R z₀ : ℝ) :
    Function.Periodic (circularCoil R z₀) (2 * Real.pi) := by
  intro t
  simp [circularCoil, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Nonzero-radius centerlines do not self-intersect within a single half-open
turn. The coincident endpoints of a closed turn are intentionally not rejected. -/
theorem circularCoil_injective_on_turn {R : ℝ} (hR : R ≠ 0) (z₀ : ℝ) :
    Set.InjOn (circularCoil R z₀) (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht u hu heq
  have hcos : Real.cos t = Real.cos u := by
    have h := congrArg (fun x : Space => x 0) heq
    change R * Real.cos t = R * Real.cos u at h
    exact mul_left_cancel₀ hR h
  have hsin : Real.sin t = Real.sin u := by
    have h := congrArg (fun x : Space => x 1) heq
    change R * Real.sin t = R * Real.sin u at h
    exact mul_left_cancel₀ hR h
  have hangle := Real.Angle.cos_sin_inj hcos hsin
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2 * Real.pi) (a := 0)
    (by simpa using ht) (by simpa using hu)).mp hangle

/-- Exact Euclidean tangent norm. Positive radius therefore gives regularity everywhere. -/
theorem circularTangent_norm (R t : ℝ) : ‖circularTangent R t‖ = |R| := by
  have hs : ‖circularTangent R t‖ ^ 2 = R ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_three]
    change (-R * Real.sin t) ^ 2 + (R * Real.cos t) ^ 2 + 0 ^ 2 = R ^ 2
    nlinarith [congrArg (fun s : ℝ => R ^ 2 * s) (Real.sin_sq_add_cos_sq t)]
  nlinarith [norm_nonneg (circularTangent R t), abs_nonneg R, sq_abs R]

/-- Continuous source and tangent curves, including both endpoints of a full turn. -/
theorem circularCoil_continuous (R z₀ : ℝ) : Continuous (circularCoil R z₀) := by
  exact continuous_iff_continuousAt.mpr (fun t => (circularCoil_derivative R z₀ t).continuousAt)

/-- The tangent curve is continuous everywhere. -/
theorem circularTangent_continuous (R : ℝ) : Continuous (circularTangent R) := by
  unfold circularTangent
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const.mul Real.continuous_sin
  · exact continuous_const.mul Real.continuous_cos
  · exact continuous_const

/-- Plane separation certifies clearance for all pairs of points on two circular filaments. -/
theorem circularCoil_plane_clearance (R S z₁ z₂ t u : ℝ) :
    |z₁ - z₂| ≤ dist (circularCoil R z₁ t) (circularCoil S z₂ u) := by
  have h := PiLp.norm_apply_le (circularCoil R z₁ t - circularCoil S z₂ u) 2
  simpa [dist_eq_norm, circularCoil, Real.norm_eq_abs] using h

/-- A point's z-coordinate gives a continuous off-source distance estimate. -/
theorem circularCoil_source_distance (R z₀ t : ℝ) (x : Space) :
    |x 2 - z₀| ≤ ‖x - circularCoil R z₀ t‖ := by
  have h := PiLp.norm_apply_le (x - circularCoil R z₀ t) 2
  simpa [circularCoil, Real.norm_eq_abs] using h

/-- A whole observation ball is separated from the source if its radius is less
than the absolute height of the coil plane. -/
theorem circularCoil_ball_distance (R z₀ t : ℝ) (x : Space) {r : ℝ}
    (hx : ‖x‖ ≤ r) : |z₀| - r ≤ ‖x - circularCoil R z₀ t‖ := by
  have hc : |z₀| ≤ ‖circularCoil R z₀ t‖ := by
    simpa using circularCoil_source_distance R z₀ t 0
  have ht := norm_sub_norm_le (circularCoil R z₀ t) x
  rw [norm_sub_rev] at ht
  linarith

/-- An entire separated angular interval has a genuine integrable field kernel. -/
theorem circularCoil_kernel_integrable (R z₀ a b : ℝ) (x : Space) {r : ℝ}
    (hx : ‖x‖ ≤ r) (hr : r < |z₀|) :
    IntervalIntegrable (fun t => filamentKernel (circularCoil R z₀) t x)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply filamentKernel_continuousOn
  · exact (circularCoil_continuous R z₀).continuousOn
  · have hd : deriv (circularCoil R z₀) = circularTangent R := by
      funext t
      exact (circularCoil_derivative R z₀ t).deriv
    rw [hd]
    exact (circularTangent_continuous R).continuousOn
  · intro t _ hz
    have hsep := circularCoil_ball_distance R z₀ t x hx
    rw [hz, norm_zero] at hsep
    linarith

end PlasmaLean.Geometry
