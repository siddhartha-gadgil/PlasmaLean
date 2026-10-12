/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FinCases

/-!
# Filament field and source-distance bound

This is the continuous Biot–Savart integral with Euclidean (not coordinate-max)
norm. The model is a filament in free space, in consistent SI units. A positive
source distance excludes its singularity. The integral bounds are mathematical
consequences of the supplied geometry and derivative bounds, not a certificate of
a closed coil, vacuum Maxwell equations, or the field inside a finite conductor.
-/
public section

noncomputable section
namespace PlasmaLean.Fields
open Matrix WithLp

/-- Physical three-space with the Euclidean norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The cross product, transported to Euclidean three-space. -/
@[expose] def cross (u v : Space) : Space := toLp 2 (ofLp u ⨯₃ ofLp v)

/-- Euclidean cross-product inequality, reusing Mathlib's angle identity. -/
theorem norm_cross_le (u v : Space) : ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [cross, InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right (by positivity) (Real.sin_le_one _)

/-- Continuity of the Euclidean cross product, proved from its coordinate formula. -/
theorem continuous_cross : Continuous (fun p : Space × Space => cross p.1 p.2) := by
  unfold cross
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

/-- The filament integrand, using the actual tangent derivative. -/
@[expose] def filamentKernel (c : ℝ → Space) (t : ℝ) (x : Space) : Space :=
  (‖x - c t‖ ^ 3)⁻¹ • cross (deriv c t) (x - c t)

/-- Oriented filament field; closure and regularity are separate geometry obligations. -/
@[expose] def filamentField (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space) : Space :=
  (μ₀ * I / (4 * Real.pi)) • ∫ t in a..b, filamentKernel c t x

set_option maxHeartbeats 800000 in
-- Elaboration of composed PiLp norm, reciprocal, and product continuity is expensive.
/-- Continuous tangents and exclusion of every source singularity ensure continuity
of the kernel on the full parameter set. -/
theorem filamentKernel_continuousOn (c : ℝ → Space) (x : Space) (s : Set ℝ)
    (hc : ContinuousOn c s) (hd : ContinuousOn (deriv c) s)
    (sep : ∀ t ∈ s, x - c t ≠ 0) : ContinuousOn (fun t => filamentKernel c t x) s := by
  unfold filamentKernel
  have hr : ContinuousOn (fun t => x - c t) s := continuousOn_const.sub hc
  have hi : ContinuousOn (fun t => (‖x - c t‖ ^ 3)⁻¹) s :=
    (hr.norm.pow 3).inv₀ (fun t ht => pow_ne_zero _ (norm_ne_zero_iff.mpr (sep t ht)))
  have hcross : ContinuousOn (fun t => cross (deriv c t) (x - c t)) s :=
    continuous_cross.comp_continuousOn (hd.prodMk hr)
  exact hi.smul hcross

/-- Linearity in current follows without any numerical integration. -/
theorem filamentField_add_current (μ₀ I J : ℝ) (c : ℝ → Space)
    (a b : ℝ) (x : Space) :
    filamentField μ₀ (I + J) c a b x =
      filamentField μ₀ I c a b x + filamentField μ₀ J c a b x := by
  simp only [filamentField, mul_add, add_div, add_smul]

/-- Zero current gives zero field. -/
theorem filamentField_zero_current (μ₀ : ℝ) (c : ℝ → Space)
    (a b : ℝ) (x : Space) : filamentField μ₀ 0 c a b x = 0 := by
  simp [filamentField]

/-- Reversing the integration limits reverses the field orientation. -/
theorem filamentField_reverse (μ₀ I : ℝ) (c : ℝ → Space)
    (a b : ℝ) (x : Space) :
    filamentField μ₀ I c b a x = -filamentField μ₀ I c a b x := by
  unfold filamentField
  rw [intervalIntegral.integral_symm a b, smul_neg]

/-- Pointwise source separation converts a tangent bound to an integrand bound. -/
theorem filamentKernel_bound (c : ℝ → Space) (t : ℝ) (x : Space)
    {d V : ℝ} (hd : 0 < d) (sep : d ≤ ‖x - c t‖) (speed : ‖deriv c t‖ ≤ V) :
    ‖filamentKernel c t x‖ ≤ V / d ^ 2 := by
  have hdist : 0 < ‖x - c t‖ := lt_of_lt_of_le hd sep
  calc
    ‖filamentKernel c t x‖ = (‖x - c t‖ ^ 3)⁻¹ * ‖cross (deriv c t) (x - c t)‖ := by
      simp [filamentKernel, norm_smul]
    _ ≤ (‖x - c t‖ ^ 3)⁻¹ * (‖deriv c t‖ * ‖x - c t‖) :=
      mul_le_mul_of_nonneg_left (norm_cross_le _ _) (by positivity)
    _ = ‖deriv c t‖ / ‖x - c t‖ ^ 2 := by
      field_simp
    _ ≤ V / d ^ 2 := div_le_div₀ (le_trans (norm_nonneg _) speed) speed
      (by positivity) (pow_le_pow_left₀ (le_of_lt hd) sep 2)

/-- Continuous-parameter field bound. Integrability is explicit, and both geometric
inequalities cover every point of the parameter interval, not just a sample grid. -/
theorem filamentField_bound (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space)
    {d V : ℝ} (hd : 0 < d)
    (_integrable : IntervalIntegrable (fun t => filamentKernel c t x) MeasureTheory.volume a b)
    (sep : ∀ t ∈ Set.uIoc a b, d ≤ ‖x - c t‖)
    (speed : ∀ t ∈ Set.uIoc a b, ‖deriv c t‖ ≤ V) :
    ‖filamentField μ₀ I c a b x‖ ≤
      |μ₀ * I / (4 * Real.pi)| * (V / d ^ 2 * |b - a|) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => filamentKernel_bound c t x hd (sep t ht) (speed t ht))
  simpa only [filamentField, norm_smul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left hb (abs_nonneg (μ₀ * I / (4 * Real.pi)))

end PlasmaLean.Fields
