/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.VacuumTolerance
public import PlasmaLean.Theory.Fields.FieldDerivative

/-!
# Actual field derivatives for the tolerance-aware fixture

This discharges the dominated-differentiation obligations for the actual C¹
manufactured coils as well as the nominal circles. The derivative is spatial and
uses the Euclidean operator norm; units are T/m for SI inputs. Field amplitude,
nonvanishing, and derivative certificates refer to the same actual geometry.
No bound on the difference of two field derivatives, Maxwell equation, field-line
barrier, or particle-confinement property is asserted here.
-/
public section
noncomputable section
namespace PlasmaLean.Design.VacuumPair
open Fields Geometry

/-- Uniform source distance retained by an actual coil after its position error. -/
private theorem actual_source_clearance (c actual : ℝ → Space) (h : WithinTolerance c actual)
    (x : Space) (sep : ∀ t, 3 / 20 ≤ ‖x - c t‖) (t : ℝ) :
    7 / 50 ≤ ‖x - actual t‖ := by
  have he : (x - actual t) - (x - c t) = -(actual t - c t) := by abel
  exact perturbed_norm_lower (x - c t) (x - actual t) (ε := 1 / 1000)
    (by linarith [sep t]) (by simpa only [he, norm_neg] using h.position t)

/-- The manufacturing budget preserves nonzero tangents as well as an upper speed bound. -/
theorem actual_speed_bounds (c actual : ℝ → Space) (h : WithinTolerance c actual)
    (speed : ∀ t, ‖deriv c t‖ = 1 / 10) (t : ℝ) :
    99 / 1000 ≤ ‖deriv actual t‖ ∧ ‖deriv actual t‖ ≤ 101 / 1000 := by
  have hn := abs_norm_sub_norm_le (deriv actual t) (deriv c t)
  rw [speed t] at hn
  have hboth := abs_le.mp (hn.trans (h.tangent t))
  constructor <;> linarith [hboth.1, hboth.2]

/-- One manufactured coil's actual field derivative and exact conservative enclosure. -/
private theorem one_actual_derivative (μ₀ I : ℝ) (c actual : ℝ → Space)
    (h : WithinTolerance c actual) (x : Space)
    (sep : ∀ t, 3 / 20 ≤ ‖x - c t‖) (speed : ∀ t, ‖deriv c t‖ = 1 / 10) :
    DifferentiableAt ℝ (filamentField μ₀ I actual 0 (2 * Real.pi)) x ∧
      ‖fderiv ℝ (filamentField μ₀ I actual 0 (2 * Real.pi)) x‖ ≤
        25250 / 343 * |μ₀ * I| := by
  have hc := h.differentiable.continuous.continuousOn (s := Set.uIcc 0 (2 * Real.pi))
  have ht := h.tangent_continuous.continuousOn (s := Set.uIcc 0 (2 * Real.pi))
  have hs := fun t (_ : t ∈ Set.uIcc 0 (2 * Real.pi)) => actual_source_clearance c actual h x sep t
  have hv := fun t (_ : t ∈ Set.uIcc 0 (2 * Real.pi)) => (actual_speed_bounds c actual h speed t).2
  have hd := filamentField_derivative μ₀ I actual 0 (2 * Real.pi) x hc ht
    (by norm_num : (0 : ℝ) < 7 / 50) (by norm_num : (0 : ℝ) ≤ 101 / 1000) hs hv
  refine ⟨hd.differentiableAt, ?_⟩
  have hb := filamentField_derivative_bound μ₀ I actual 0 (2 * Real.pi) x hc ht
    (by norm_num : (0 : ℝ) < 7 / 50) (by norm_num : (0 : ℝ) ≤ 101 / 1000) hs hv
  convert hb using 1
  rw [abs_div, abs_of_pos (by positivity : 0 < 4 * Real.pi), sub_zero,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp
  ring

/-- Differentiability and an operator enclosure for every point of the original
5 cm ball and every pair of manufactured coils satisfying the stated C¹ budget. -/
theorem manufactured_field_derivative (μ₀ J₁ J₂ : ℝ) (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    (x : Space) (hx : ObservationRegion x) :
    DifferentiableAt ℝ (manufacturedField μ₀ J₁ J₂ upper lower) x ∧
      ‖fderiv ℝ (manufacturedField μ₀ J₁ J₂ upper lower) x‖ ≤
        25250 / 343 * (|μ₀ * J₁| + |μ₀ * J₂|) := by
  obtain ⟨du, bu⟩ := one_actual_derivative μ₀ J₁ upperCoil upper hu x
    (fun t => (source_clearance x hx t).1) (fun t => (regular_coils t).1)
  obtain ⟨dl, bl⟩ := one_actual_derivative μ₀ J₂ lowerCoil lower hl x
    (fun t => (source_clearance x hx t).2) (fun t => (regular_coils t).2)
  refine ⟨du.add dl, ?_⟩
  change ‖fderiv ℝ (filamentField μ₀ J₁ upper 0 (2 * Real.pi) +
    filamentField μ₀ J₂ lower 0 (2 * Real.pi)) x‖ ≤ _
  rw [fderiv_add du dl]
  have hn := norm_add_le
    (fderiv ℝ (filamentField μ₀ J₁ upper 0 (2 * Real.pi)) x)
    (fderiv ℝ (filamentField μ₀ J₂ lower 0 (2 * Real.pi)) x)
  linarith

/-- The nominal field is genuinely differentiable, rather than only Lipschitz. -/
theorem field_differentiable (μ₀ I J : ℝ) (x : Space) (hx : ObservationRegion x) :
    DifferentiableAt ℝ (field μ₀ I J) x :=
  (manufactured_field_derivative μ₀ I J upperCoil lowerCoil
    nominal_within_tolerance.1 nominal_within_tolerance.2 x hx).1

/-- Zero-current derivative is zero, independently checking the limiting case. -/
theorem zero_current_derivative (μ₀ : ℝ) (x : Space) :
    fderiv ℝ (field μ₀ 0 0) x = 0 := by
  have he : field μ₀ 0 0 = fun _ => (0 : Space) := funext (zero_current μ₀)
  rw [he]
  exact fderiv_const_apply _

end PlasmaLean.Design.VacuumPair
