/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FieldVariation

/-!
# Manufacturing errors in continuous filament fields

The same angular parameter identifies nominal and actual centerlines. Both position
and tangent errors are required: a position-only tolerance cannot control length or
the Biot–Savart integrand. Distances and derivatives use the Euclidean norm and SI
lengths, with radians dimensionless. All inequalities cover the full integration
interval. These are C⁰ field-error estimates, not field-derivative, conductor
self-field, or Maxwell certificates. The complete proof is the inverse-cube
mean-value estimate, cross-product bilinearity, and the integral triangle inequality.
-/
public section
noncomputable section
namespace PlasmaLean.Fields
open WithLp

/-- Linearity of the first Euclidean cross-product argument. -/
theorem cross_sub_left (v w x : Space) : cross (v - w) x = cross v x - cross w x := by
  simp only [cross, ofLp_sub, map_sub, LinearMap.sub_apply, toLp_sub]

/-- Perturbing a vector by ε consumes at most ε of its distance from zero. -/
theorem perturbed_norm_lower (r q : Space) {d ε : ℝ}
    (sep : d + ε ≤ ‖r‖) (err : ‖q - r‖ ≤ ε) : d ≤ ‖q‖ := by
  have h := norm_sub_norm_le r q
  rw [norm_sub_rev] at h
  linarith

/-- Norm of the radial kernel away from its singularity. -/
theorem inverseCube_norm {r : Space} (hr : r ≠ 0) :
    ‖inverseCube r‖ = 1 / ‖r‖ ^ 2 := by
  have hn := norm_ne_zero_iff.mpr hr
  simp only [inverseCube, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_pow, abs_norm]
  field_simp

/-- Nearby source vectors have a uniform inverse-cube error bound. Separation at
the nominal vector includes the entire perturbation ball, not only the endpoints. -/
theorem inverseCube_perturbation (r q : Space) {d ε : ℝ} (hd : 0 < d)
    (sep : d + ε ≤ ‖r‖) (err : ‖q - r‖ ≤ ε) :
    ‖inverseCube q - inverseCube r‖ ≤ (4 / d ^ 3) * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans err
  have hb := inverseCube_difference (0 : Space) (convex_closedBall r ε) hd
    (fun z hz => by
      simp only [sub_zero]
      exact perturbed_norm_lower r z sep (by simpa only [Metric.mem_closedBall,
        dist_eq_norm] using hz))
    (x := q) (y := r) (by simpa only [Metric.mem_closedBall, dist_eq_norm] using err)
    (Metric.mem_closedBall_self hε)
  simp only [sub_zero] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left err (by positivity))

/-- Pointwise field-kernel error from independent position and tangent budgets.
The reference speed is V, position error ε, and tangent error η. -/
theorem filamentKernel_perturbation (c actual : ℝ → Space) (t : ℝ) (x : Space)
    {d ε η V : ℝ} (hd : 0 < d) (sep : d + ε ≤ ‖x - c t‖)
    (pos : ‖actual t - c t‖ ≤ ε) (tan : ‖deriv actual t - deriv c t‖ ≤ η)
    (speed : ‖deriv c t‖ ≤ V) :
    ‖filamentKernel actual t x - filamentKernel c t x‖ ≤
      η / d ^ 2 + V * (4 / d ^ 3) * ε := by
  have heq : (x - actual t) - (x - c t) = -(actual t - c t) := by abel
  have herr : ‖(x - actual t) - (x - c t)‖ ≤ ε := by simpa only [heq, norm_neg] using pos
  have hs := perturbed_norm_lower (x - c t) (x - actual t) sep herr
  have hn : x - actual t ≠ 0 := norm_pos_iff.mp (hd.trans_le hs)
  have hnorm : ‖inverseCube (x - actual t)‖ ≤ 1 / d ^ 2 := by
    rw [inverseCube_norm hn]
    exact div_le_div₀ (by norm_num) (by rfl) (by positivity)
      (pow_le_pow_left₀ hd.le hs 2)
  have hrad := inverseCube_perturbation (x - c t) (x - actual t) hd sep herr
  have hV : 0 ≤ V := (norm_nonneg _).trans speed
  have hη : 0 ≤ η := (norm_nonneg _).trans tan
  have hsplit : filamentKernel actual t x - filamentKernel c t x =
      cross (deriv actual t - deriv c t) (inverseCube (x - actual t)) +
      cross (deriv c t) (inverseCube (x - actual t) - inverseCube (x - c t)) := by
    rw [cross_sub_left, cross_sub_right]
    simp only [filamentKernel_eq_cross_inverseCube]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖cross (deriv actual t - deriv c t) (inverseCube (x - actual t))‖ +
        ‖cross (deriv c t) (inverseCube (x - actual t) - inverseCube (x - c t))‖ :=
      norm_add_le _ _
    _ ≤ η * (1 / d ^ 2) + V * ((4 / d ^ 3) * ε) := add_le_add
      ((norm_cross_le _ _).trans (mul_le_mul tan hnorm (norm_nonneg _) hη))
      ((norm_cross_le _ _).trans (mul_le_mul speed hrad (norm_nonneg _) hV))
    _ = _ := by ring

/-- Continuous integral error for a manufactured centerline at the same current.
Integrability of both actual and nominal kernels is explicit. -/
theorem filamentField_perturbation (μ₀ I : ℝ) (c actual : ℝ → Space) (a b : ℝ)
    (x : Space) {d ε η V : ℝ} (hd : 0 < d)
    (sep : ∀ t ∈ Set.uIoc a b, d + ε ≤ ‖x - c t‖)
    (pos : ∀ t ∈ Set.uIoc a b, ‖actual t - c t‖ ≤ ε)
    (tan : ∀ t ∈ Set.uIoc a b, ‖deriv actual t - deriv c t‖ ≤ η)
    (speed : ∀ t ∈ Set.uIoc a b, ‖deriv c t‖ ≤ V)
    (hc : IntervalIntegrable (fun t => filamentKernel c t x) MeasureTheory.volume a b)
    (ha : IntervalIntegrable (fun t => filamentKernel actual t x) MeasureTheory.volume a b) :
    ‖filamentField μ₀ I actual a b x - filamentField μ₀ I c a b x‖ ≤
      |μ₀ * I / (4 * Real.pi)| * ((η / d ^ 2 + V * (4 / d ^ 3) * ε) * |b - a|) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => filamentKernel_perturbation c actual t x hd (sep t ht)
      (pos t ht) (tan t ht) (speed t ht))
  unfold filamentField
  rw [← smul_sub, ← intervalIntegral.integral_sub ha hc, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- Current calibration error is exactly the field of the current difference. -/
theorem filamentField_sub_current (μ₀ I J : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space) :
    filamentField μ₀ I c a b x - filamentField μ₀ J c a b x =
      filamentField μ₀ (I - J) c a b x := by
  simp only [filamentField, mul_sub, sub_div, sub_smul]

end PlasmaLean.Fields
