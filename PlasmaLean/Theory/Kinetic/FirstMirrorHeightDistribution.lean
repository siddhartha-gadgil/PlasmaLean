/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.FirstMirrorRegularValues
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Measurable height events for the two first mirrors of a fixed field profile -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.FirstMirror
open Set MeasureTheory

/-- Strict ordering of first-contact times makes both outward-slope observations measurable
in the original real height. No choice of a joint distribution on trajectories is needed. -/
theorem measurable_good_heights {f g : ℝ → ℝ} {a b c d L U : ℝ}
    (p : Family f a b L U) (q : Family g c d L U) (ha : 0 ≤ a) (hc : 0 ≤ c) (m : ℝ) :
    MeasurableSet {H : ℝ | ∃ h : Icc L U, (h : ℝ) = H ∧
      m < deriv f (p.time h) ∧ m < deriv g (q.time h)} := by
  let s : Set (Icc L U) := {h | m < deriv f (p.time h) ∧ m < deriv g (q.time h)}
  have mf := (measurable_deriv f).comp (p.strictMono ha).monotone.measurable
  have mg := (measurable_deriv g).comp (q.strictMono hc).monotone.measurable
  have ms : MeasurableSet s :=
    (measurableSet_lt measurable_const mf).inter (measurableSet_lt measurable_const mg)
  have equal : {H : ℝ | ∃ h : Icc L U, (h : ℝ) = H ∧ m < deriv f (p.time h) ∧
      m < deriv g (q.time h)} = ((↑) : Icc L U → ℝ) '' s := by
    ext H
    constructor
    · rintro ⟨h,eq,ok⟩
      exact ⟨h,ok,eq⟩
    · rintro ⟨h,ok,eq⟩
      exact ⟨h,eq,ok⟩
  rw [equal]
  exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' ms

/-- Lebesgue measure conditioned on the closed height band. -/
def uniformHeight (L U : ℝ) : Measure ℝ := ProbabilityTheory.cond volume (Icc L U)

theorem uniformHeight_isProbability {L U : ℝ} (pos : L < U) :
    IsProbabilityMeasure (uniformHeight L U) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr pos)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

/-- Normalization divides the area lower bound by the actual height-band width. -/
theorem uniformHeight_lower {G : Set ℝ} {L U lo : ℝ} (pos : L < U) (within : G ⊆ Icc L U)
    (area : ENNReal.ofReal lo ≤ volume G) :
    ENNReal.ofReal (lo / (U - L)) ≤ uniformHeight L U G := by
  rw [uniformHeight, ProbabilityTheory.cond_apply measurableSet_Icc,
    inter_eq_right.mpr within, Real.volume_Icc, ENNReal.ofReal_div_of_pos (sub_pos.mpr pos),
    ENNReal.div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left area zero_le

/-- A change of law only needs an upper density ratio on the failed event. The output
measure must be normalized, and the reference probability can be any baseline law. -/
theorem probability_of_bad_density {X : Type*} [MeasurableSpace X] {base alt : Measure X}
    [IsProbabilityMeasure base] [IsProbabilityMeasure alt] {G : Set X} (mg : MeasurableSet G)
    {p C : ENNReal} (good : p ≤ base G) {ρ : X → ENNReal} (law : alt = base.withDensity ρ)
    (bad : ∀ᵐ x ∂(base.restrict Gᶜ), ρ x ≤ C) :
    1 - C * (1 - p) ≤ alt G := by
  have hbad : alt Gᶜ ≤ C * base Gᶜ := by
    rw [law,withDensity_apply _ mg.compl]
    calc
      ∫⁻ x in Gᶜ, ρ x ∂base ≤ ∫⁻ _ in Gᶜ, C ∂base := lintegral_mono_ae bad
      _ = _ := by simp
  have miss : base Gᶜ ≤ 1 - p := by
    rw [measure_compl mg (measure_ne_top _ _),measure_univ]
    exact tsub_le_tsub_left good _
  apply tsub_le_iff_right.mpr
  calc
    1 = alt G + alt Gᶜ := by
      simpa only [measure_univ] using (measure_add_measure_compl (μ := alt) mg).symm
    _ ≤ _ := add_le_add le_rfl (hbad.trans (mul_le_mul_of_nonneg_left miss zero_le))

/-- A measurable height observable can be sampled on a preselected family. After its
pushforward is identified, the height-event bound holds for the original sample space. -/
theorem probability_of_height_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {H : X → ℝ} (mH : Measurable H) {G : Set ℝ} (mG : MeasurableSet G) {μ : Measure ℝ}
    (law : ν.map H = μ) {p : ENNReal} (bound : p ≤ μ G) :
    p ≤ ν (H ⁻¹' G) := by
  rw [← Measure.map_apply mH mG,law]
  exact bound

/-- A sampling law supported at a single bad height assigns zero mass to the good event. -/
theorem excluded_atom {G : Set ℝ} (mg : MeasurableSet G) {h : ℝ} (outside : h ∉ G) :
    Measure.dirac h G = 0 := by rw [Measure.dirac_apply' h mg,indicator_of_notMem outside]

end PlasmaLean.Kinetic.FirstMirror
