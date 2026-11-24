/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import PlasmaLean.Theory.Kinetic.MirrorHeightAction

/-!
# Bounce action from field-strength sublevel lengths

A well carries a finite arclength measure. Its clipped single-passage action is
determined by the arclength below each field strength. Integration over parallel
speed avoids any regularity requirement at a turning point.
-/

@[expose] public section
noncomputable section

open MeasureTheory Real Set

namespace PlasmaLean.Kinetic.MirrorSublevelAction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Arclength of the part of the measured well below or at a field strength. -/
def sublevelLength (μ : Measure X) (B : X → ℝ) (level : ℝ) : ℝ :=
  μ.real {x | B x ≤ level}

/-- Single-passage action in the normalization used by `MirrorHeightAction.action`. -/
def action (μ : Measure X) (B : X → ℝ) (h : ℝ) : ℝ :=
  ∫ x, √(2 * (h - B x)) ∂μ

/-- The measure definition recovers the existing trace action when the trace
parameter has nonnegative arclength density on the integration bracket. -/
theorem action_trace {a b : ℝ} (hab : a ≤ b) (B w : ℝ → ℝ) (h : ℝ)
    (hw : Measurable w) (hw₀ : ∀ t ∈ Ioc a b, 0 ≤ w t) :
    action ((volume.restrict (Ioc a b)).withDensity (fun t => ENNReal.ofReal (w t))) B h =
      MirrorHeightAction.action B w a b h := by
  rw [action, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _,
    MirrorHeightAction.action, intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [ENNReal.toReal_ofReal (hw₀ t ht), smul_eq_mul]

/-- Layer-cake formula in parallel speed. The field has an almost-everywhere
lower bound on the well. Plateaus and degenerate mirror points are allowed. -/
theorem action_eq_integral_sublevel (μ : Measure X) [IsFiniteMeasure μ]
    {B : X → ℝ} (hB : AEMeasurable B μ) {base h : ℝ} (floorB : ∀ᵐ x ∂μ, base ≤ B x) :
    action μ B h =
      ∫ v in Ioc 0 (√(2 * (h - base))), sublevelLength μ B (h - v^2 / 2) := by
  let speed := fun x => √(2 * (h - B x))
  have bounded : ∀ᵐ x ∂μ, speed x ≤ √(2 * (h - base)) := by
    filter_upwards [floorB] with x hx
    exact Real.sqrt_le_sqrt (by linarith)
  have meas : AEMeasurable speed μ := by dsimp [speed]; fun_prop
  have integ : Integrable speed μ := Integrable.of_bound meas.aestronglyMeasurable _ (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), speed] using bounded)
  change (∫ x, speed x ∂μ) = _
  rw [integ.integral_eq_integral_Ioc_meas_le (.of_forall (fun _ => Real.sqrt_nonneg _)) bounded]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  apply congrArg μ.real
  ext x
  simp only [mem_ofPred_eq, speed, Real.le_sqrt' hv.1]
  constructor <;> intro step <;> linarith

/-- Increasing the speed threshold can only reduce the length that meets it. -/
theorem antitone_sublevel_speed (μ : Measure X) [IsFiniteMeasure μ] (B : X → ℝ) (h : ℝ) :
    AntitoneOn (fun v => sublevelLength μ B (h - v^2 / 2)) (Ici 0) := by
  intro u hu v _ huv
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  change B x ≤ h - v^2 / 2 at hx
  change B x ≤ h - u^2 / 2
  nlinarith [sq_le_sq' (by linarith [mem_Ici.mp hu] : -v ≤ u) huv]

private theorem integrableOn_profile (μ : Measure X) [IsFiniteMeasure μ] (B : X → ℝ)
    (h L : ℝ) (hL : 0 ≤ L) :
    IntegrableOn (fun v => sublevelLength μ B (h - v^2 / 2)) (Ioc 0 L) :=
  ((antitone_sublevel_speed μ B h).mono (by
    rw [uIcc_of_le hL]; exact Icc_subset_Ici_self)).intervalIntegrable.1

/-- A uniform discrepancy in sublevel arclength gives a sharp action bound.
The two wells can have different parameter spaces, total lengths and measures. -/
theorem action_difference_le (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {B : X → ℝ} {C : Y → ℝ}
    (hB : AEMeasurable B μ) (hC : AEMeasurable C ν) {base h ε : ℝ}
    (floorB : ∀ᵐ x ∂μ, base ≤ B x) (floorC : ∀ᵐ y ∂ν, base ≤ C y) (hh : base ≤ h)
    (gap : ∀ b ∈ Icc base h, |sublevelLength μ B b - sublevelLength ν C b| ≤ ε) :
    |action μ B h - action ν C h| ≤ ε * √(2 * (h - base)) := by
  let L := √(2 * (h - base))
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hsq : L^2 = 2 * (h - base) := Real.sq_sqrt (by linarith)
  rw [action_eq_integral_sublevel μ hB floorB, action_eq_integral_sublevel ν hC floorC,
    ← integral_sub (integrableOn_profile μ B h L hL) (integrableOn_profile ν C h L hL)]
  have bound := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 L)
    (f := fun v => sublevelLength μ B (h - v^2 / 2) - sublevelLength ν C (h - v^2 / 2))
    (C := ε) measure_Ioc_lt_top (by
      intro v hv
      rw [Real.norm_eq_abs]
      apply gap
      constructor
      · nlinarith [sq_le_sq' (by linarith [hv.1] : -L ≤ v) hv.2]
      · nlinarith [sq_nonneg v])
  simpa only [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hL, sub_zero, L] using bound

/-- Equimeasurable well profiles have identical action at this height.
It suffices to compare sublevels between the common lower bound and the height. -/
theorem action_eq_of_sublevels (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {B : X → ℝ} {C : Y → ℝ}
    (hB : AEMeasurable B μ) (hC : AEMeasurable C ν) {base h : ℝ}
    (floorB : ∀ᵐ x ∂μ, base ≤ B x) (floorC : ∀ᵐ y ∂ν, base ≤ C y) (hh : base ≤ h)
    (same : ∀ b ∈ Icc base h, sublevelLength μ B b = sublevelLength ν C b) :
    action μ B h = action ν C h := by
  have bound := action_difference_le μ ν hB hC floorB floorC hh (ε := 0)
    (fun b hb => by simp [same b hb])
  exact sub_eq_zero.mp (by simpa using bound)

/-- If sublevel lengths vary at most linearly with a field-line label near a
given label, the derivative of the action there obeys the corresponding bound.
Both the arclength measure and the field profile may depend on the label. -/
theorem abs_action_derivative_le (μ : ℝ → Measure X) [∀ α, IsFiniteMeasure (μ α)]
    (B : ℝ → X → ℝ) {base h α D K : ℝ} (hh : base ≤ h) (hK : 0 ≤ K)
    (hB : ∀ β, AEMeasurable (B β) (μ β)) (hbase : ∀ β, ∀ᵐ x ∂μ β, base ≤ B β x)
    (gap : ∀ᶠ β in nhds α, ∀ b ∈ Icc base h,
      |sublevelLength (μ β) (B β) b - sublevelLength (μ α) (B α) b| ≤ K * |β - α|)
    (hd : HasDerivAt (fun β => action (μ β) (B β) h) D α) :
    |D| ≤ K * √(2 * (h - base)) := by
  apply hd.le_of_lip' (mul_nonneg hK (Real.sqrt_nonneg _))
  filter_upwards [gap] with β hg
  simpa only [Real.norm_eq_abs, mul_right_comm] using
    action_difference_le (μ β) (μ α) (hB β) (hB α) (hbase β) (hbase α) hh hg

/-- Every sublevel at or above a constant field contains the entire well. -/
theorem sublevelLength_const (μ : Measure X) {base b : ℝ} (hb : base ≤ b) :
    sublevelLength μ (fun _ => base) b = μ.real univ := by
  simp [sublevelLength, hb]

/-- Flat-bottom profiles on two wells attain the action discrepancy exactly,
with the difference of their total arclengths as the sublevel discrepancy. -/
theorem flat_wells_attain_bound (μ : Measure X) (ν : Measure Y) (base h : ℝ) :
    |action μ (fun _ => base) h - action ν (fun _ => base) h| =
      |μ.real univ - ν.real univ| * √(2 * (h - base)) := by
  simp only [action, integral_const, smul_eq_mul, ← sub_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]

end PlasmaLean.Kinetic.MirrorSublevelAction
