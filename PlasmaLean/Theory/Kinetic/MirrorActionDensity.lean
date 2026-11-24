/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionCollar

/-! # Action perturbations with a changing arclength density -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionDensity

open MeasureTheory Real MirrorSublevelAction

variable {X : Type*} [MeasurableSpace X]

/-- Arclength in a common parameter with real nonnegative density. -/
def arcMeasure (μ : Measure X) (w : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

/-- Pull the action back to the reference parameter measure. -/
theorem action_density (μ : Measure X) {w : X → ℝ} (mw : Measurable w)
    (nw : ∀ᵐ x ∂μ, 0 ≤ w x) (C : X → ℝ) (h : ℝ) :
    action (arcMeasure μ w) C h = ∫ x, w x * √(2 * (h - C x)) ∂μ := by
  rw [arcMeasure, action, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [nw] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

/-- Changing the arclength density costs at most its L¹ discrepancy times
the maximum possible parallel speed. The common parameter measure can be infinite. -/
theorem density_difference (μ : Measure X) {w v C : X → ℝ} {base h : ℝ}
    (mw : Measurable w) (mv : Measurable v) (nw : ∀ᵐ x ∂μ, 0 ≤ w x) (nv : ∀ᵐ x ∂μ, 0 ≤ v x)
    (iw : Integrable w μ) (iv : Integrable v μ) (mc : AEMeasurable C μ)
    (floorC : ∀ᵐ x ∂μ, base ≤ C x) :
    |action (arcMeasure μ w) C h - action (arcMeasure μ v) C h| ≤
      √(2 * (h - base)) * ∫ x, |w x - v x| ∂μ := by
  let s := fun x => √(2 * (h - C x))
  let V := √(2 * (h - base))
  have ms : AEStronglyMeasurable s μ := by dsimp [s]; fun_prop
  have bound : ∀ᵐ x ∂μ, ‖s x‖ ≤ V := by
    filter_upwards [floorC] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [action_density μ mw nw, action_density μ mv nv,
    ← integral_sub (iw.mul_bdd ms bound) (iv.mul_bdd ms bound)]
  have est := norm_integral_le_of_norm_le (μ := μ)
    (f := fun x => w x * s x - v x * s x) ((iw.sub iv).abs.const_mul V) (by
      filter_upwards [bound] with x hx
      rw [← sub_mul, Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  simpa only [Real.norm_eq_abs, integral_const_mul, Pi.sub_apply, V] using est

/-- Add this explicit density term to any fixed-measure profile estimate,
including the regular-collar estimate for wells with a critical bottom. -/
theorem profile_and_density (μ : Measure X) {w v B C : X → ℝ} {base h E : ℝ}
    (mw : Measurable w) (mv : Measurable v) (nw : ∀ᵐ x ∂μ, 0 ≤ w x) (nv : ∀ᵐ x ∂μ, 0 ≤ v x)
    (iw : Integrable w μ) (iv : Integrable v μ) (mc : AEMeasurable C μ)
    (floorC : ∀ᵐ x ∂μ, base ≤ C x)
    (profiles : |action (arcMeasure μ w) B h - action (arcMeasure μ w) C h| ≤ E) :
    |action (arcMeasure μ w) B h - action (arcMeasure μ v) C h| ≤
      E + √(2 * (h - base)) * ∫ x, |w x - v x| ∂μ :=
  (abs_sub_le _ (action (arcMeasure μ w) C h) _).trans
    (add_le_add profiles (density_difference μ mw mv nw nv iw iv mc floorC))

/-- An L¹ bound on arclength change adds its rate times the maximum speed to the
fixed-density action derivative estimate. All densities use the same angular parameter. -/
theorem label_derivative (μ : Measure X) (w B : ℝ → X → ℝ) {α base h P L D : ℝ}
    (p₀ : 0 ≤ P) (l₀ : 0 ≤ L) (mw : ∀ β, Measurable (w β))
    (nw : ∀ β, ∀ᵐ x ∂μ, 0 ≤ w β x) (iw : ∀ β, Integrable (w β) μ)
    (mb : ∀ β, AEMeasurable (B β) μ) (floorB : ∀ β, ∀ᵐ x ∂μ, base ≤ B β x)
    (profiles : ∀ᶠ β in nhds α, |action (arcMeasure μ (w α)) (B α) h -
      action (arcMeasure μ (w α)) (B β) h| ≤ P * |β - α|)
    (densities : ∀ᶠ β in nhds α, (∫ x, |w α x - w β x| ∂μ) ≤ L * |β - α|)
    (hd : HasDerivAt (fun β => action (arcMeasure μ (w β)) (B β) h) D α) :
    |D| ≤ P + √(2 * (h - base)) * L := by
  apply hd.le_of_lip' (add_nonneg p₀ (mul_nonneg (Real.sqrt_nonneg _) l₀))
  filter_upwards [profiles, densities] with β prof den
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (action _ (B β) h)]
  have bound := profile_and_density μ (mw α) (mw β) (nw α) (nw β) (iw α) (iw β)
    (mb β) (floorB β) prof
  calc
    _ ≤ _ := bound
    _ ≤ P * |β - α| + √(2 * (h - base)) * (L * |β - α|) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left den (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- On a probability space, constant densities one and zero at the field floor
attain the coefficient of the L¹ density discrepancy. -/
theorem density_bound_attained (μ : Measure X) [IsProbabilityMeasure μ] (base h : ℝ) :
    |action (arcMeasure μ (fun _ => 1)) (fun _ => base) h -
      action (arcMeasure μ (fun _ => 0)) (fun _ => base) h| = √(2 * (h - base)) := by
  rw [action_density μ measurable_const (Filter.Eventually.of_forall fun _ => zero_le_one),
    action_density μ measurable_const (Filter.Eventually.of_forall fun _ => le_refl 0)]
  simp [abs_of_nonneg (Real.sqrt_nonneg _)]

end PlasmaLean.Kinetic.MirrorActionDensity
