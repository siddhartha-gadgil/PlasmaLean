/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.VacuumPair
public import PlasmaLean.Theory.Fields.CoilPerturbation
public import PlasmaLean.Theory.Geometry.CoilTube
public import PlasmaLean.Theory.Geometry.PlacedCircle

/-!
# An end-to-end tolerance budget for the vacuum-pair fixture

The invented demonstration budget is 1 mm position error, 1 mm/radian tangent
error, 1% current calibration error, and 5 mm tube radius. These are design inputs,
not measured manufacturing capabilities or conductor qualification. The actual
curves must be C¹ and closed. The proof discharges integrability and composes the
errors for the very same curves/currents. It certifies a nonvanishing field in a
1 mm probe ball, NOT an invariant torus or plasma confinement. Tubes are enclosing
sets, not proved embedded winding packs; the field still uses filaments.
-/
public section
noncomputable section
namespace PlasmaLean.Design.VacuumPair
open Fields Geometry

/-- A full-domain C¹ manufacturing envelope, in the same angular parameter. -/
structure WithinTolerance (nominal actual : ℝ → Space) : Prop where
  differentiable : Differentiable ℝ actual
  tangent_continuous : Continuous (deriv actual)
  closed : Function.Periodic actual (2 * Real.pi)
  position : ∀ t, ‖actual t - nominal t‖ ≤ 1 / 1000
  tangent : ∀ t, ‖deriv actual t - deriv nominal t‖ ≤ 1 / 1000

/-- Unmodified circles witness that the tolerance contract is nonempty. -/
theorem circle_within_tolerance (R z₀ : ℝ) :
    WithinTolerance (circularCoil R z₀) (circularCoil R z₀) where
  differentiable t := (circularCoil_derivative R z₀ t).differentiableAt
  tangent_continuous := by
    have he : deriv (circularCoil R z₀) = circularTangent R :=
      funext (fun t => (circularCoil_derivative R z₀ t).deriv)
    rw [he]
    exact circularTangent_continuous R
  closed := circularCoil_periodic R z₀
  position t := by simp
  tangent t := by simp

/-- Both nominal coils are admissible manufactured coils. -/
theorem nominal_within_tolerance : WithinTolerance upperCoil upperCoil ∧
    WithinTolerance lowerCoil lowerCoil :=
  ⟨circle_within_tolerance _ _, circle_within_tolerance _ _⟩

/-- Rigid-pose/centre metrology budgets discharge the full C¹ manufacturing
contract for placed circles. No measured dataset is assumed to satisfy them. -/
theorem placed_circle_within_tolerance (Q P : Space ≃ₗᵢ[ℝ] Space)
    (center actualCenter : Space) (R : ℝ) {ε α : ℝ}
    (hc : ‖actualCenter - center‖ ≤ ε)
    (hQ : ‖P.toContinuousLinearEquiv.toContinuousLinearMap -
      Q.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ α)
    (position_budget : ε + α * |R| ≤ 1 / 1000)
    (tangent_budget : α * |R| ≤ 1 / 1000) :
    WithinTolerance (placedCircle Q center R) (placedCircle P actualCenter R) where
  differentiable := (placedCircle_C1 P actualCenter R).1
  tangent_continuous := (placedCircle_C1 P actualCenter R).2
  closed := placedCircle_periodic P actualCenter R
  position t :=
    (placedCircle_position_error Q P center actualCenter R t hc hQ).trans position_budget
  tangent t := (placedCircle_tangent_error Q P center actualCenter R t hQ).trans tangent_budget

/-- Field of the actual pair; no separate nominal witness is substituted. -/
@[expose] def manufacturedField (μ₀ J₁ J₂ : ℝ) (upper lower : ℝ → Space) (x : Space) : Space :=
  filamentField μ₀ J₁ upper 0 (2 * Real.pi) x +
    filamentField μ₀ J₂ lower 0 (2 * Real.pi) x

/-- C¹ source regularity and the consumed distance margin ensure actual-kernel integrability. -/
private theorem perturbed_integrable (c actual : ℝ → Space) (h : WithinTolerance c actual)
    (x : Space) (sep : ∀ t, 3 / 20 ≤ ‖x - c t‖) :
    IntervalIntegrable (fun t => filamentKernel actual t x) MeasureTheory.volume
      0 (2 * Real.pi) := by
  apply ContinuousOn.intervalIntegrable
  apply filamentKernel_continuousOn actual x _ h.differentiable.continuous.continuousOn
    h.tangent_continuous.continuousOn
  intro t _
  have he : (x - actual t) - (x - c t) = -(actual t - c t) := by abel
  have hs : 7 / 50 ≤ ‖x - actual t‖ :=
    perturbed_norm_lower (x - c t) (x - actual t) (ε := 1 / 1000)
      (by linarith [sep t]) (by simpa only [he, norm_neg] using h.position t)
  exact norm_pos_iff.mp (by linarith)

/-- One full-turn field-error budget with exact fixture constants and no quadrature. -/
private theorem one_manufacturing_error (μ₀ I : ℝ) (c actual : ℝ → Space)
    (h : WithinTolerance c actual) (x : Space)
    (sep : ∀ t, 3 / 20 ≤ ‖x - c t‖) (speed : ∀ t, ‖deriv c t‖ = 1 / 10)
    (hi : IntervalIntegrable (fun t => filamentKernel c t x) MeasureTheory.volume
      0 (2 * Real.pi)) :
    ‖filamentField μ₀ I actual 0 (2 * Real.pi) x -
      filamentField μ₀ I c 0 (2 * Real.pi) x‖ ≤ 135 / 1372 * |μ₀ * I| := by
  have hb := filamentField_perturbation μ₀ I c actual 0 (2 * Real.pi) x
    (d := 7 / 50) (ε := 1 / 1000) (η := 1 / 1000) (V := 1 / 10) (by norm_num)
    (fun t _ => by linarith [sep t]) (fun t _ => h.position t)
    (fun t _ => h.tangent t) (fun t _ => (speed t).le) hi (perturbed_integrable c actual h x sep)
  convert hb using 1
  rw [abs_div, abs_of_pos (by positivity : 0 < 4 * Real.pi), sub_zero,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp
  ring

/-- Whole-observation-ball field error from simultaneous manufacture of both coils. -/
theorem manufacturing_error (μ₀ J₁ J₂ : ℝ) (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    (x : Space) (hx : ObservationRegion x) :
    ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ J₁ J₂ x‖ ≤
      135 / 1372 * (|μ₀ * J₁| + |μ₀ * J₂|) := by
  have eu := one_manufacturing_error μ₀ J₁ upperCoil upper hu x
    (fun t => (source_clearance x hx t).1) (fun t => (regular_coils t).1)
    (integrable_kernels x hx).1
  have el := one_manufacturing_error μ₀ J₂ lowerCoil lower hl x
    (fun t => (source_clearance x hx t).2) (fun t => (regular_coils t).2)
    (integrable_kernels x hx).2
  let U := filamentField μ₀ J₁ upper 0 (2 * Real.pi) x -
    filamentField μ₀ J₁ upperCoil 0 (2 * Real.pi) x
  let L := filamentField μ₀ J₂ lower 0 (2 * Real.pi) x -
    filamentField μ₀ J₂ lowerCoil 0 (2 * Real.pi) x
  have he : manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ J₁ J₂ x = U + L := by
    dsimp [manufacturedField, field, U, L]
    abel
  rw [he]
  have ht := norm_add_le U L
  change ‖U‖ ≤ _ at eu
  change ‖L‖ ≤ _ at el
  linarith

/-- Current-error superposition uses the identical decoded nominal geometry. -/
theorem field_current_error (μ₀ I J₁ J₂ : ℝ) (x : Space) (hx : ObservationRegion x) :
    ‖field μ₀ J₁ J₂ x - field μ₀ I I x‖ ≤
      20 / 9 * (|μ₀ * (J₁ - I)| + |μ₀ * (J₂ - I)|) := by
  have he : field μ₀ J₁ J₂ x - field μ₀ I I x = field μ₀ (J₁ - I) (J₂ - I) x := by
    unfold field
    rw [← filamentField_sub_current, ← filamentField_sub_current]
    abel
  rw [he]
  exact field_bound _ _ _ x hx

/-- A relative calibration interval bounds both the actual current and its error. -/
private theorem calibrated_current_bounds {μ₀ I J : ℝ} (hμ : 0 ≤ μ₀) (hI : 0 ≤ I)
    (hJ : |J - I| ≤ I / 100) :
    |μ₀ * J| ≤ 101 / 100 * (μ₀ * I) ∧ |μ₀ * (J - I)| ≤ (μ₀ * I) / 100 := by
  have ha : |J| ≤ 101 / 100 * I := by
    have ht := abs_add_le (J - I) I
    rw [sub_add_cancel, abs_of_nonneg hI] at ht
    linarith
  rw [abs_mul, abs_mul, abs_of_nonneg hμ]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ha hμ]
  · nlinarith [mul_le_mul_of_nonneg_left hJ hμ]

/-- Combined C¹ manufacturing and independent 1% current errors consume less than
μ₀I/4 of the field budget at EVERY point of the original 5 cm observation ball. -/
theorem combined_field_error {μ₀ I J₁ J₂ : ℝ} (hμ : 0 < μ₀) (hI : 0 < I)
    (upper lower : ℝ → Space) (hu : WithinTolerance upperCoil upper)
    (hl : WithinTolerance lowerCoil lower)
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100)
    (x : Space) (hx : ObservationRegion x) :
    ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ ≤ (μ₀ * I) / 4 := by
  have hm := manufacturing_error μ₀ J₁ J₂ upper lower hu hl x hx
  have hc := field_current_error μ₀ I J₁ J₂ x hx
  obtain ⟨hu₁, hu₂⟩ := calibrated_current_bounds hμ.le hI.le hJ₁
  obtain ⟨hl₁, hl₂⟩ := calibrated_current_bounds hμ.le hI.le hJ₂
  have ht := dist_triangle (manufacturedField μ₀ J₁ J₂ upper lower x)
    (field μ₀ J₁ J₂ x) (field μ₀ I I x)
  simp only [dist_eq_norm] at ht
  nlinarith [mul_pos hμ hI]

/-- A conservative exact axial lower bound at the midpoint. -/
theorem midpoint_axial_lower {μ₀ I : ℝ} (hμ : 0 ≤ μ₀) (hI : 0 ≤ I) :
    16 / 25 * (μ₀ * I) ≤ (field μ₀ I I 0) 2 := by
  rw [midpoint_field]
  change 16 / 25 * (μ₀ * I) ≤ μ₀ * I / (100 * Real.sqrt (1 / 20) ^ 3)
  have hs : Real.sqrt (1 / 20) ≤ 1 / 4 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hcube := pow_le_pow_left₀ (Real.sqrt_nonneg (1 / 20)) hs 3
  have hp : 0 < 100 * Real.sqrt (1 / 20) ^ 3 := by positivity
  apply (le_div_iff₀ hp).mpr
  have hnon : 0 ≤ μ₀ * I := mul_nonneg hμ hI
  nlinarith [mul_le_mul_of_nonneg_left hcube hnon]

/-- The nominal axial component is at least μ₀I/2 throughout a 1 mm probe ball.
This is a pointwise direction bound, not a magnetic-surface assertion. -/
theorem probe_axial_lower {μ₀ I : ℝ} (hμ : 0 < μ₀) (hI : 0 < I)
    (x : Space) (hx : ‖x‖ ≤ 1 / 1000) : (μ₀ * I) / 2 ≤ (field μ₀ I I x) 2 := by
  have hr : ObservationRegion x := by dsimp [ObservationRegion]; linarith
  have hv := field_difference μ₀ I I x 0 hr origin_in_region
  rw [sub_zero, abs_of_pos (mul_pos hμ hI)] at hv
  have hc := PiLp.norm_apply_le (field μ₀ I I x - field μ₀ I I 0) 2
  have he : |(field μ₀ I I x) 2 - (field μ₀ I I 0) 2| ≤
      ‖field μ₀ I I x - field μ₀ I I 0‖ := by simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hc
  have hl := midpoint_axial_lower hμ.le hI.le
  have hd := (abs_le.mp he).1
  nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ (3200 / 27) * (μ₀ * I))]

/-- The same manufactured coils and calibrated currents retain a positive axial
field throughout the probe ball. No trajectory confinement is inferred. -/
theorem robust_probe_field {μ₀ I J₁ J₂ : ℝ} (hμ : 0 < μ₀) (hI : 0 < I)
    (upper lower : ℝ → Space) (hu : WithinTolerance upperCoil upper)
    (hl : WithinTolerance lowerCoil lower)
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100)
    (x : Space) (hx : ‖x‖ ≤ 1 / 1000) :
    (μ₀ * I) / 4 ≤ (manufacturedField μ₀ J₁ J₂ upper lower x) 2 ∧
      manufacturedField μ₀ J₁ J₂ upper lower x ≠ 0 := by
  have hr : ObservationRegion x := by dsimp [ObservationRegion]; linarith
  have hb := combined_field_error hμ hI upper lower hu hl hJ₁ hJ₂ x hr
  have hc := PiLp.norm_apply_le
    (manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x) 2
  have he : |(manufacturedField μ₀ J₁ J₂ upper lower x) 2 - (field μ₀ I I x) 2| ≤
      ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hc
  have hp := probe_axial_lower hμ hI x hx
  have hd := (abs_le.mp he).1
  have hlow : (μ₀ * I) / 4 ≤ (manufacturedField μ₀ J₁ J₂ upper lower x) 2 := by linarith
  refine ⟨hlow, ?_⟩
  intro hz
  rw [hz] at hlow
  have hpos : 0 < μ₀ * I / 4 := by positivity
  change μ₀ * I / 4 ≤ 0 at hlow
  linarith

/-- Every point of the actual 5 mm-radius tube envelopes has at least 388 mm
coil-to-coil clearance, including both 1 mm centerline errors. -/
theorem manufactured_tube_clearance (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    {x y : Space} (hx : x ∈ CoilTube upper (1 / 200))
    (hy : y ∈ CoilTube lower (1 / 200)) : 97 / 250 ≤ dist x y := by
  have su : CoilTube upper (1 / 200) ⊆ CoilTube upperCoil (1 / 1000 + 1 / 200) :=
    perturbed_tube_subset upperCoil upper (fun t => by
      simpa only [dist_eq_norm, norm_sub_rev] using hu.position t)
  have sl : CoilTube lower (1 / 200) ⊆ CoilTube lowerCoil (1 / 1000 + 1 / 200) :=
    perturbed_tube_subset lowerCoil lower (fun t => by
      simpa only [dist_eq_norm, norm_sub_rev] using hl.position t)
  have hb := tube_clearance upperCoil lowerCoil coil_clearance (su hx) (sl hy)
  norm_num at hb
  exact hb

end PlasmaLean.Design.VacuumPair
