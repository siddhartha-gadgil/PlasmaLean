/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.CoilPerturbation
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating the continuous filament field away from sources

The source curve and its actual tangent are continuous on the entire integration
interval. A positive distance from ALL source points gives one common spatial
neighborhood for dominated differentiation. This proves an actual Fréchet
derivative of the vector integral, not just a sampled Jacobian or a Lipschitz
estimate. The conservative radial-kernel constant is 4, not the sharp 2.
Maxwell identities and higher spatial derivatives remain separate obligations.
-/
public section
noncomputable section
namespace PlasmaLean.Fields
open WithLp MeasureTheory Filter
open scoped Topology

/-- Continuous bilinear cross product on Euclidean physical space. -/
@[expose] def crossBilinear : Space →L[ℝ] Space →L[ℝ] Space :=
  (LinearMap.mk₂ ℝ cross
    (fun u v x => by simp only [cross, ofLp_add, map_add, LinearMap.add_apply, toLp_add])
    (fun a u x => by simp only [cross, ofLp_smul, map_smul, LinearMap.smul_apply, toLp_smul])
    (fun u x y => by simp only [cross, ofLp_add, map_add, toLp_add])
    (fun a u x => cross_smul_right u x a)).mkContinuous₂ 1
    (fun u v => by simpa only [one_mul, LinearMap.mk₂_apply] using norm_cross_le u v)

/-- The operator representation does not change the cross-product convention. -/
theorem crossBilinear_apply (u v : Space) : crossBilinear u v = cross u v := rfl

/-- Holding the first vector fixed gives operator norm at most its Euclidean norm. -/
theorem crossBilinear_norm (u : Space) : ‖crossBilinear u‖ ≤ ‖u‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_cross_le u)

/-- Continuous differentiability of the radial kernel at each nonzero vector. -/
theorem inverseCube_contDiffAt {r : Space} (hr : r ≠ 0) : ContDiffAt ℝ 1 inverseCube r := by
  exact (((contDiffAt_norm ℝ hr).pow 3).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hr))).smul
    contDiffAt_id

/-- Explicit continuous-linear operator for the spatial kernel derivative. -/
@[expose] def kernelDerivative (c : ℝ → Space) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  (crossBilinear (deriv c t)).comp (fderiv ℝ inverseCube (x - c t))

/-- Actual derivative in the observation point, with the source angle held fixed. -/
theorem filamentKernel_derivative (c : ℝ → Space) (t : ℝ) (x : Space)
    (sep : x - c t ≠ 0) :
    HasFDerivAt (filamentKernel c t) (kernelDerivative c t x) x := by
  have hi := (inverseCube_derivative sep).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (c t))
  have hc := (crossBilinear (deriv c t)).hasFDerivAt.comp x hi
  convert hc using 1
  · funext y
    exact filamentKernel_eq_cross_inverseCube c t y
  · simp [kernelDerivative]

/-- Source-distance enclosure of the spatial derivative operator, valid continuously. -/
theorem kernelDerivative_bound (c : ℝ → Space) (t : ℝ) (x : Space)
    {d V : ℝ} (hd : 0 < d) (sep : d ≤ ‖x - c t‖) (speed : ‖deriv c t‖ ≤ V) :
    ‖kernelDerivative c t x‖ ≤ V * (4 / d ^ 3) := by
  have hn : x - c t ≠ 0 := norm_pos_iff.mp (hd.trans_le sep)
  have hb : ‖fderiv ℝ inverseCube (x - c t)‖ ≤ 4 / d ^ 3 :=
    (inverseCube_derivative_bound hn).trans
      (div_le_div₀ (by norm_num) (by rfl) (by positivity)
        (pow_le_pow_left₀ hd.le sep 3))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul ((crossBilinear_norm _).trans speed) hb (norm_nonneg _)
      ((norm_nonneg _).trans speed))

/-- Continuity in the source parameter of the derivative integrand. -/
theorem kernelDerivative_continuousOn (c : ℝ → Space) (x : Space) (s : Set ℝ)
    (hc : ContinuousOn c s) (hd : ContinuousOn (deriv c) s)
    (sep : ∀ t ∈ s, x - c t ≠ 0) : ContinuousOn (fun t => kernelDerivative c t x) s := by
  have hrad : ContinuousOn (fun t => fderiv ℝ inverseCube (x - c t)) s := by
    intro t ht
    have hr : ContinuousWithinAt (fun u : ℝ => x - c u) s t :=
      continuousWithinAt_const.sub (hc t ht)
    have hcont := (inverseCube_contDiffAt (sep t ht)).continuousAt_fderiv (by simp)
    exact hcont.comp_continuousWithinAt (f := fun u : ℝ => x - c u) hr
  exact (crossBilinear.continuous.comp_continuousOn hd).clm_comp hrad

/-- Dominated differentiation of a filament's continuous integral. A common
positive source distance is required on the whole CLOSED angular interval. -/
theorem filamentField_derivative (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space)
    (hc : ContinuousOn c (Set.uIcc a b)) (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    {d V : ℝ} (hd : 0 < d) (_hV : 0 ≤ V)
    (sep : ∀ t ∈ Set.uIcc a b, d ≤ ‖x - c t‖)
    (speed : ∀ t ∈ Set.uIcc a b, ‖deriv c t‖ ≤ V) :
    HasFDerivAt (filamentField μ₀ I c a b)
      ((μ₀ * I / (4 * Real.pi)) • ∫ t in a..b, kernelDerivative c t x) x := by
  have near (z : Space) (hz : z ∈ Metric.ball x (d / 2)) (t : ℝ) (htm : t ∈ Set.uIcc a b) :
      d / 2 ≤ ‖z - c t‖ := by
    have hnorm := norm_sub_norm_le (x - c t) (z - c t)
    have he : (x - c t) - (z - c t) = x - z := by abel
    rw [he, norm_sub_rev x z] at hnorm
    have hn : ‖z - x‖ < d / 2 := hz
    linarith [sep t htm]
  have nz (z : Space) (hz : z ∈ Metric.ball x (d / 2)) (t : ℝ) (htm : t ∈ Set.uIcc a b) :
      z - c t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (near z hz t htm))
  have hx : x ∈ Metric.ball x (d / 2) := Metric.mem_ball_self (by positivity)
  have hint (z : Space) (hz : z ∈ Metric.ball x (d / 2)) :
      IntervalIntegrable (fun t => filamentKernel c t z) volume a b :=
    (filamentKernel_continuousOn c z _ hc ht (nz z hz)).intervalIntegrable
  have hdi : IntervalIntegrable (fun t => kernelDerivative c t x) volume a b :=
    (kernelDerivative_continuousOn c x _ hc ht (nz x hx)).intervalIntegrable
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun z t => filamentKernel c t z) (F' := fun z t => kernelDerivative c t z)
    (bound := fun _ => V * (4 / (d / 2) ^ 3)) (μ := volume)
    (Metric.ball_mem_nhds x (by positivity : 0 < d / 2))
    (Filter.mem_of_superset (Metric.ball_mem_nhds x (by positivity : 0 < d / 2))
      (fun z hz => (hint z hz).aestronglyMeasurable_restrict_uIoc))
    (hint x hx) hdi.aestronglyMeasurable_restrict_uIoc
    (ae_restrict_of_forall_mem measurableSet_uIoc (fun t htm z hz =>
      kernelDerivative_bound c t z (by positivity) (near z hz t (Set.uIoc_subset_uIcc htm))
        (speed t (Set.uIoc_subset_uIcc htm))))
    (intervalIntegrable_const)
    (ae_restrict_of_forall_mem measurableSet_uIoc (fun t htm z hz =>
      filamentKernel_derivative c t z (nz z hz t (Set.uIoc_subset_uIcc htm))))
  exact h.const_smul (μ₀ * I / (4 * Real.pi))

/-- Operator-norm enclosure of the actual derivative of the field integral. -/
theorem filamentField_derivative_bound (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space)
    (hc : ContinuousOn c (Set.uIcc a b)) (ht : ContinuousOn (deriv c) (Set.uIcc a b))
    {d V : ℝ} (hd : 0 < d) (hV : 0 ≤ V)
    (sep : ∀ t ∈ Set.uIcc a b, d ≤ ‖x - c t‖)
    (speed : ∀ t ∈ Set.uIcc a b, ‖deriv c t‖ ≤ V) :
    ‖fderiv ℝ (filamentField μ₀ I c a b) x‖ ≤
      |μ₀ * I / (4 * Real.pi)| * (V * (4 / d ^ 3) * |b - a|) := by
  rw [(filamentField_derivative μ₀ I c a b x hc ht hd hV sep speed).fderiv,
    norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t htm =>
    kernelDerivative_bound c t x hd (sep t (Set.uIoc_subset_uIcc htm))
      (speed t (Set.uIoc_subset_uIcc htm)))

end PlasmaLean.Fields
