/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.CircularCoil
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Circular-loop field on its symmetry axis

Exact continuous integration in the free-space filament model. Positive radius
excludes the source singularity on the whole axis. The formula checks orientation
and normalization of the field API; it is not a confinement or coil-stress theorem.
-/
public section
noncomputable section
namespace PlasmaLean.Fields
open Geometry WithLp Matrix

/-- A point on the common symmetry axis, with coordinate in metres. -/
@[expose] def axisPoint (z : ℝ) : Space := toLp 2 ![0, 0, z]

/-- Source distance on the axis is independent of the angular parameter. -/
theorem circularCoil_axis_distance (R z₀ t z : ℝ) :
    ‖axisPoint z - circularCoil R z₀ t‖ = Real.sqrt (R ^ 2 + (z - z₀) ^ 2) := by
  have hs : ‖axisPoint z - circularCoil R z₀ t‖ ^ 2 = R ^ 2 + (z - z₀) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_three]
    change (0 - R * Real.cos t) ^ 2 + (0 - R * Real.sin t) ^ 2 + (z - z₀) ^ 2 = _
    nlinarith [congrArg (fun s : ℝ => R ^ 2 * s) (Real.cos_sq_add_sin_sq t)]
  calc
    ‖axisPoint z - circularCoil R z₀ t‖ = Real.sqrt (‖axisPoint z - circularCoil R z₀ t‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := congrArg Real.sqrt hs

/-- The cross-product numerator, including the current-orientation sign. -/
theorem circularCoil_axis_numerator (R z₀ t z : ℝ) :
    cross (circularTangent R t) (axisPoint z - circularCoil R z₀ t) =
      toLp 2 ![R * (z - z₀) * Real.cos t, R * (z - z₀) * Real.sin t, R ^ 2] := by
  ext i
  fin_cases i
  · change R * Real.cos t * (z - z₀) - 0 * (0 - R * Real.sin t) =
      R * (z - z₀) * Real.cos t
    ring
  · change 0 * (0 - R * Real.cos t) - (-R * Real.sin t) * (z - z₀) =
      R * (z - z₀) * Real.sin t
    ring
  · change (-R * Real.sin t) * (0 - R * Real.sin t) -
      (R * Real.cos t) * (0 - R * Real.cos t) = R ^ 2
    nlinarith [congrArg (fun s : ℝ => R ^ 2 * s) (Real.sin_sq_add_cos_sq t)]

/-- Explicit axis kernel before integration. -/
theorem circularCoil_axis_kernel (R z₀ t z : ℝ) :
    filamentKernel (circularCoil R z₀) t (axisPoint z) =
      (Real.sqrt (R ^ 2 + (z - z₀) ^ 2) ^ 3)⁻¹ •
        toLp 2 ![R * (z - z₀) * Real.cos t, R * (z - z₀) * Real.sin t, R ^ 2] := by
  rw [filamentKernel, (circularCoil_derivative _ _ _).deriv,
    circularCoil_axis_distance, circularCoil_axis_numerator]

/-- Positive-radius loops have continuous kernels at every point of their axis. -/
theorem circularCoil_axis_integrable {R : ℝ} (hR : 0 < R) (z₀ z a b : ℝ) :
    IntervalIntegrable (fun t => filamentKernel (circularCoil R z₀) t (axisPoint z))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply filamentKernel_continuousOn
  · exact (circularCoil_continuous R z₀).continuousOn
  · have hd : deriv (circularCoil R z₀) = circularTangent R := by
      funext t; exact (circularCoil_derivative R z₀ t).deriv
    rw [hd]
    exact (circularTangent_continuous R).continuousOn
  · intro t _ heq
    have hd := circularCoil_axis_distance R z₀ t z
    have hpos : 0 < Real.sqrt (R ^ 2 + (z - z₀) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [heq, norm_zero] at hd
    linarith

/-- Exact vector field on the axis. The square-root cube is (R²+(z-z₀)²)^(3/2). -/
theorem circularCoil_axis_field {R : ℝ} (hR : 0 < R) (μ₀ I z₀ z : ℝ) :
    filamentField μ₀ I (circularCoil R z₀) 0 (2 * Real.pi) (axisPoint z) =
      axisPoint (μ₀ * I * R ^ 2 / (2 * Real.sqrt (R ^ 2 + (z - z₀) ^ 2) ^ 3)) := by
  have hi := circularCoil_axis_integrable hR z₀ z 0 (2 * Real.pi)
  have hcoord (i : Fin 3) :
      (∫ t in (0 : ℝ)..2 * Real.pi, filamentKernel (circularCoil R z₀) t (axisPoint z)) i =
        ∫ t in (0 : ℝ)..2 * Real.pi, (filamentKernel (circularCoil R z₀) t (axisPoint z)) i := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).intervalIntegral_comp_comm hi).symm
  have hpos : 0 < Real.sqrt (R ^ 2 + (z - z₀) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  ext i
  change (μ₀ * I / (4 * Real.pi)) *
    (∫ t in (0 : ℝ)..2 * Real.pi, filamentKernel (circularCoil R z₀) t (axisPoint z)) i = _
  rw [hcoord]
  simp_rw [circularCoil_axis_kernel]
  fin_cases i
  · simp [axisPoint, intervalIntegral.integral_const_mul, integral_cos]
  · simp [axisPoint, intervalIntegral.integral_const_mul, integral_sin]
  · simp [axisPoint, intervalIntegral.integral_const]
    field_simp
    ring

end PlasmaLean.Fields
