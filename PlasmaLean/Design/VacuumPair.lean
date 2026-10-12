/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.CircularLoop
public import PlasmaLean.Theory.Fields.FieldVariation
public import PlasmaLean.Theory.Geometry.ParametricBounds
public import Mathlib.Tactic.NormNum

/-!
# Small two-loop vacuum-field demonstrator: exact geometric fixture

Two circular filaments of radius 0.1 m lie in planes z=±0.2 m. The observation
region is the closed ball of radius 0.05 m about the origin. Current and permeability
remain explicit parameters. These invented exact coefficients are a mathematical
test fixture, not experimental or material data. The loops are axisymmetric: no
stellarator rotational transform, confinement, reactor feasibility, or hardware
qualification follows. `VacuumTolerance` and `VacuumDerivative` add manufactured
field/derivative and tube-envelope bounds. Maxwell and finite-conductor certificates
remain separate targets; this is progress toward, not completion of, roadmap gate P2.
-/
public section
noncomputable section
namespace PlasmaLean.Design.VacuumPair
open Fields Geometry

/-- Upper circular filament, oriented counterclockwise from positive z. -/
@[expose] def upperCoil : ℝ → Space := circularCoil (1 / 10) (1 / 5)

/-- Lower filament with the same parameter/current convention. -/
@[expose] def lowerCoil : ℝ → Space := circularCoil (1 / 10) (-1 / 5)

/-- The entire observation region, not a sampled set of points. -/
@[expose] def ObservationRegion (x : Space) : Prop := ‖x‖ ≤ 1 / 20

/-- The certified region is nonempty. -/
theorem origin_in_region : ObservationRegion 0 := by norm_num [ObservationRegion]

/-- Superposition of the two continuous filament integrals. -/
@[expose] def field (μ₀ I J : ℝ) (x : Space) : Space :=
  filamentField μ₀ I upperCoil 0 (2 * Real.pi) x +
    filamentField μ₀ J lowerCoil 0 (2 * Real.pi) x

/-- Both exact centerlines close after a full turn. -/
theorem closed_coils : Function.Periodic upperCoil (2 * Real.pi) ∧
    Function.Periodic lowerCoil (2 * Real.pi) :=
  ⟨circularCoil_periodic _ _, circularCoil_periodic _ _⟩

/-- Neither exact centerline self-intersects during one half-open turn. -/
theorem simple_coils : Set.InjOn upperCoil (Set.Ico 0 (2 * Real.pi)) ∧
    Set.InjOn lowerCoil (Set.Ico 0 (2 * Real.pi)) :=
  ⟨circularCoil_injective_on_turn (by norm_num) _,
    circularCoil_injective_on_turn (by norm_num) _⟩

/-- The nonzero tangent norm is certified at every angular parameter. -/
theorem regular_coils (t : ℝ) : ‖deriv upperCoil t‖ = 1 / 10 ∧
    ‖deriv lowerCoil t‖ = 1 / 10 := by
  constructor
  · rw [upperCoil, (circularCoil_derivative _ _ _).deriv, circularTangent_norm]
    norm_num
  · rw [lowerCoil, (circularCoil_derivative _ _ _).deriv, circularTangent_norm]
    norm_num

/-- Every pair of centerline points is separated by at least 0.4 m. -/
theorem coil_clearance (t u : ℝ) : 2 / 5 ≤ dist (upperCoil t) (lowerCoil u) := by
  have h := circularCoil_plane_clearance (1 / 10) (1 / 10) (1 / 5) (-1 / 5) t u
  norm_num at h
  simpa only [upperCoil, lowerCoil, neg_div] using h

/-- Every observation point is at least 0.15 m from either filament. -/
theorem source_clearance (x : Space) (hx : ObservationRegion x) (t : ℝ) :
    3 / 20 ≤ ‖x - upperCoil t‖ ∧ 3 / 20 ≤ ‖x - lowerCoil t‖ := by
  constructor
  · have h := circularCoil_ball_distance (1 / 10) (1 / 5) t x hx
    norm_num at h
    exact h
  · have h := circularCoil_ball_distance (1 / 10) (-1 / 5) t x hx
    norm_num at h
    simpa only [lowerCoil, neg_div] using h

/-- No supplied integrability assumption remains for either candidate kernel. -/
theorem integrable_kernels (x : Space) (hx : ObservationRegion x) :
    IntervalIntegrable (fun t => filamentKernel upperCoil t x) MeasureTheory.volume
      0 (2 * Real.pi) ∧
    IntervalIntegrable (fun t => filamentKernel lowerCoil t x) MeasureTheory.volume
      0 (2 * Real.pi) := by
  constructor
  · exact circularCoil_kernel_integrable _ _ _ _ x hx (by norm_num)
  · exact circularCoil_kernel_integrable _ _ _ _ x hx (by norm_num)

private theorem one_field_bound (μ₀ I z₀ : ℝ) (hz : |z₀| = 1 / 5)
    (x : Space) (hx : ObservationRegion x) :
    ‖filamentField μ₀ I (circularCoil (1 / 10) z₀) 0 (2 * Real.pi) x‖ ≤
      20 / 9 * |μ₀ * I| := by
  have hi := circularCoil_kernel_integrable (1 / 10) z₀ 0 (2 * Real.pi) x hx
    (by rw [hz]; norm_num)
  have hb := filamentField_bound μ₀ I (circularCoil (1 / 10) z₀) 0 (2 * Real.pi) x
    (d := 3 / 20) (V := 1 / 10) (by norm_num) hi
    (by
      intro t _
      have h := circularCoil_ball_distance (1 / 10) z₀ t x hx
      rw [hz] at h
      norm_num at h
      exact h)
    (by
      intro t _
      rw [(circularCoil_derivative _ _ _).deriv, circularTangent_norm]
      norm_num)
  convert hb using 1
  rw [abs_div, abs_of_pos (by positivity : 0 < 4 * Real.pi), sub_zero,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp
  ring

/-- A field amplitude enclosure holds at every point of the observation ball for
all real currents. It is an upper bound, not a lower field or confinement claim. -/
theorem field_bound (μ₀ I J : ℝ) (x : Space) (hx : ObservationRegion x) :
    ‖field μ₀ I J x‖ ≤ 20 / 9 * (|μ₀ * I| + |μ₀ * J|) := by
  have hu := one_field_bound μ₀ I (1 / 5) (by norm_num) x hx
  have hl := one_field_bound μ₀ J (-1 / 5) (by norm_num) x hx
  have ht := norm_add_le (filamentField μ₀ I upperCoil 0 (2 * Real.pi) x)
    (filamentField μ₀ J lowerCoil 0 (2 * Real.pi) x)
  change ‖filamentField μ₀ I upperCoil 0 (2 * Real.pi) x +
    filamentField μ₀ J lowerCoil 0 (2 * Real.pi) x‖ ≤ _
  change ‖filamentField μ₀ I upperCoil 0 (2 * Real.pi) x‖ ≤ _ at hu
  change ‖filamentField μ₀ J lowerCoil 0 (2 * Real.pi) x‖ ≤ _ at hl
  linarith

/-- The exact midpoint field for equal oriented currents, independently checking
the continuous integral normalization and sign. -/
theorem midpoint_field (μ₀ I : ℝ) :
    field μ₀ I I 0 = axisPoint (μ₀ * I / (100 * Real.sqrt (1 / 20) ^ 3)) := by
  have hu := circularCoil_axis_field (R := 1 / 10) (by norm_num) μ₀ I (1 / 5) 0
  have hl := circularCoil_axis_field (R := 1 / 10) (by norm_num) μ₀ I (-1 / 5) 0
  have hz : axisPoint 0 = 0 := by ext i; fin_cases i <;> rfl
  rw [hz] at hu hl
  unfold field upperCoil lowerCoil
  rw [hu, hl]
  norm_num
  ext i
  fin_cases i <;> simp [axisPoint]
  ring

/-- Equal positive currents produce a nonzero positive axial midpoint field. This
is a field assertion only, not a minimum over the region or a confinement result. -/
theorem midpoint_field_positive {μ₀ I : ℝ} (hμ : 0 < μ₀) (hI : 0 < I) :
    0 < (field μ₀ I I 0) 2 := by
  rw [midpoint_field]
  change 0 < μ₀ * I / (100 * Real.sqrt (1 / 20) ^ 3)
  positivity

private theorem one_field_difference (μ₀ I z₀ : ℝ) (hz : |z₀| = 1 / 5)
    (x y : Space) (hx : ObservationRegion x) (hy : ObservationRegion y) :
    ‖filamentField μ₀ I (circularCoil (1 / 10) z₀) 0 (2 * Real.pi) x -
      filamentField μ₀ I (circularCoil (1 / 10) z₀) 0 (2 * Real.pi) y‖ ≤
        (1600 / 27 * |μ₀ * I|) * ‖x - y‖ := by
  have hs : Convex ℝ {z : Space | ObservationRegion z} := by
    simpa only [Metric.closedBall, dist_zero_right, ObservationRegion] using
      convex_closedBall (0 : Space) (1 / 20)
  have hb := filamentField_difference μ₀ I (circularCoil (1 / 10) z₀) 0 (2 * Real.pi)
    hs (d := 3 / 20) (V := 1 / 10) (by norm_num)
    (by
      intro t _ z hzr
      have h := circularCoil_ball_distance (1 / 10) z₀ t z hzr
      rw [hz] at h
      norm_num at h
      exact h)
    (by
      intro t _
      rw [(circularCoil_derivative _ _ _).deriv, circularTangent_norm]
      norm_num)
    (by
      intro z hzr
      exact circularCoil_kernel_integrable _ _ _ _ z hzr (by rw [hz]; norm_num)) hx hy
  convert hb using 1
  rw [abs_div, abs_of_pos (by positivity : 0 < 4 * Real.pi), sub_zero,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp
  ring

/-- Quantitative spatial field variation for every pair of points in the entire
three-dimensional observation ball, obtained without differentiating the integral. -/
theorem field_difference (μ₀ I J : ℝ) (x y : Space)
    (hx : ObservationRegion x) (hy : ObservationRegion y) :
    ‖field μ₀ I J x - field μ₀ I J y‖ ≤
      (1600 / 27 * (|μ₀ * I| + |μ₀ * J|)) * ‖x - y‖ := by
  have hu := one_field_difference μ₀ I (1 / 5) (by norm_num) x y hx hy
  have hl := one_field_difference μ₀ J (-1 / 5) (by norm_num) x y hx hy
  let u := filamentField μ₀ I upperCoil 0 (2 * Real.pi)
  let l := filamentField μ₀ J lowerCoil 0 (2 * Real.pi)
  have heq : field μ₀ I J x - field μ₀ I J y = (u x - u y) + (l x - l y) := by
    dsimp [field, u, l]
    abel
  rw [heq]
  have ht := norm_add_le (u x - u y) (l x - l y)
  change ‖u x - u y‖ ≤ _ at hu
  change ‖l x - l y‖ ≤ _ at hl
  nlinarith

/-- Uniform centerline displacements consume clearance margin everywhere, without
assuming that fields or finite winding-pack properties transfer automatically. -/
theorem perturbed_clearance (upper lower : ℝ → Space) {ε₁ ε₂ : ℝ}
    (hu : ∀ t, dist (upperCoil t) (upper t) ≤ ε₁)
    (hl : ∀ t, dist (lower t) (lowerCoil t) ≤ ε₂) (t u : ℝ) :
    2 / 5 - ε₁ - ε₂ ≤ dist (upper t) (lower u) :=
  clearance_of_nearby _ _ _ _ (coil_clearance t u) (hu t) (hl u)

/-- Zero currents give no field, a limiting case that cannot be called confinement. -/
theorem zero_current (μ₀ : ℝ) (x : Space) : field μ₀ 0 0 x = 0 := by
  simp [field, filamentField_zero_current]

end PlasmaLean.Design.VacuumPair
