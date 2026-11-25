/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialPassingCore
public import PlasmaLean.Design.DommaschkToroidalFieldBounds
public import PlasmaLean.Theory.Kinetic.MirrorBounceTime

/-! # Travel time on the nonturning part of each original radial field line -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialPassingTime
open Set MeasureTheory Certificates.PositionFrameSlabs
open DommaschkRadialFamilyContinuity DommaschkNativeWellAction DommaschkFirstMirrorLaunchSign
open DommaschkRadialPassingCore DommaschkSignedTraceDensity DommaschkPhysicalActionPanel
open DommaschkMirrorTubeCrossing

/-- The time per unit geometric azimuth uses the speed of the actual Cartesian field line. -/
def rate (y : ℝ → Plane) (h t : ℝ) : ℝ := density y t / Real.sqrt (2 * (h - field y t))

private theorem weight_eq {y : ℝ → Plane} {T t : ℝ}
    (e : Enclosed y (-T) T) (ht : t ∈ Icc (-T) T) :
    density y t = arcDensity (y t 0) t (y t 1) := by
  have box := e.region t ht
  exact arcDensity_of_ode (e.ode t ht)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) box.1.1)
    ((by norm_num : (0 : ℝ) < 1 / 64).trans (DommaschkSignedTraceDenominator.regular t box.1 box.2))

theorem regular_rate {y : ℝ → Plane} {S T h : ℝ} (e : Enclosed y (-T) T) (st : S ≤ T)
    (passage : Passing y S) (heightRange : h ∈ Icc (height false : ℝ) (height true : ℝ)) :
    ContinuousOn (rate y h) (Icc (-S) S) ∧
      ∀ t ∈ Icc (-S) S, 1 / 2 ≤ rate y h t ∧ rate y h t ≤ 15 := by
  have sub : Icc (-S) S ⊆ Icc (-T) T := Icc_subset_Icc (neg_le_neg st) st
  have cy : ContinuousOn y (Icc (-S) S) :=
    fun t ht => (e.ode t (sub ht)).continuousAt.continuousWithinAt
  have box := fun t (ht : t ∈ Icc (-S) S) => e.region t (sub ht)
  have den : ContinuousOn (density y) (Icc (-S) S) :=
    (continuousOn_density_region cy box).congr (fun t ht => weight_eq e (sub ht))
  have fc : ContinuousOn (field y) (Icc (-S) S) := by
    change ContinuousOn (fun t => strength t (y t)) _
    simpa only [one_mul] using continuousOn_strength cy 1
      (fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) (box t ht).1.1)
  have speed : ContinuousOn (fun t => Real.sqrt (2 * (h - field y t))) (Icc (-S) S) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul (continuousOn_const.sub fc))
  have positive (t : ℝ) (ht : t ∈ Icc (-S) S) : 0 < Real.sqrt (2 * (h - field y t)) :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 12) ((passage t ht).2 h heightRange.1)
  refine ⟨den.div speed (fun t ht => (positive t ht).ne'), fun t ht => ?_⟩
  have wlo := density_lower t (box t ht)
  have whi := DommaschkToroidalFieldBounds.density_upper (box t ht) (passage t ht).1.le
  have flo : 0 ≤ field y t := norm_nonneg _
  have hhi : h ≤ 5300546391395933 / 5000000000000000 := by
    simpa only [height, Bool.true_eq, ite_true, Rat.cast_div, Rat.cast_ofNat] using heightRange.2
  have shi : Real.sqrt (2 * (h - field y t)) ≤ 3 / 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · linarith
  have slo := (passage t ht).2 h heightRange.1
  unfold rate
  rw [weight_eq e (sub ht)]
  constructor
  · apply (le_div_iff₀ (positive t ht)).2
    linarith
  · apply (div_le_iff₀ (positive t ht)).2
    linarith

/-- For any ordered subsegment, its normalized Cartesian travel time is comparable with its
angular length. Both endpoints, the original birth and either direction of flight are allowed. -/
theorem duration {y : ℝ → Plane} {S T h a b : ℝ} (e : Enclosed y (-T) T) (st : S ≤ T)
    (passage : Passing y S) (heightRange : h ∈ Icc (height false : ℝ) (height true : ℝ))
    (left : -S ≤ a) (ab : a ≤ b) (right : b ≤ S) :
    (b - a) / 2 ≤ Kinetic.MirrorActionEnvelope.oneWayBounceTime (density y) (field y) h a b ∧
      Kinetic.MirrorActionEnvelope.oneWayBounceTime (density y) (field y) h a b ≤ 15 * (b - a) := by
  obtain ⟨cont, bounds⟩ := regular_rate e st passage heightRange
  have sub : Icc a b ⊆ Icc (-S) S := Icc_subset_Icc left right
  have finite : IntervalIntegrable (rate y h) volume a b :=
    (cont.mono (by simpa only [uIcc_of_le ab] using sub)).intervalIntegrable
  have lo := intervalIntegral.integral_mono_on ab (intervalIntegrable_const (c := (1/2 : ℝ)))
    finite (fun t ht => (bounds t (sub ht)).1)
  have hi := intervalIntegral.integral_mono_on ab finite (intervalIntegrable_const (c := (15 : ℝ)))
    (fun t ht => (bounds t (sub ht)).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at lo hi
  change (b - a) / 2 ≤ (∫ t in a..b, rate y h t) ∧ (∫ t in a..b, rate y h t) ≤ 15 * (b - a)
  constructor <;> linarith

/-- Signed normalized travel time measured from the original birth angle. -/
def clock (y : ℝ → Plane) (h φ t : ℝ) : ℝ := ∫ u in φ..t, rate y h u

/-- Every time between the two ends of the passage is attained at exactly one angular
position, including on the side preceding the birth. The time at the birth is zero. -/
def ClockOn (y : ℝ → Plane) (S h φ : ℝ) : Prop :=
  clock y h φ φ = 0 ∧ ContinuousOn (clock y h φ) (Icc (-S) S) ∧
    StrictMonoOn (clock y h φ) (Icc (-S) S) ∧
    (∀ a ∈ Icc (-S) S, ∀ b ∈ Icc (-S) S, a ≤ b →
      (b-a)/2 ≤ clock y h φ b - clock y h φ a ∧ clock y h φ b - clock y h φ a ≤ 15*(b-a)) ∧
    ∀ τ ∈ Icc (clock y h φ (-S)) (clock y h φ S),
      ∃! t : Icc (-S) S, clock y h φ t = τ

theorem clock_on {y : ℝ → Plane} {S T h φ : ℝ} (e : Enclosed y (-T) T) (st : S ≤ T)
    (passage : Passing y S) (heightRange : h ∈ Icc (height false : ℝ) (height true : ℝ))
    (born : φ ∈ Icc (-S) S) : ClockOn y S h φ := by
  have regular := (regular_rate e st passage heightRange).1
  have finite {a b : ℝ} (ha : a ∈ Icc (-S) S) (hb : b ∈ Icc (-S) S) :
      IntervalIntegrable (rate y h) volume a b :=
    (regular.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have order := born.1.trans born.2
  have hl := left_mem_Icc.mpr order
  have hr := right_mem_Icc.mpr order
  have cts : ContinuousOn (clock y h φ) (Icc (-S) S) := by
    change ContinuousOn (fun t => ∫ u in φ..t, rate y h u) _
    rw [← uIcc_of_le order]
    exact intervalIntegral.continuousOn_primitive_interval' (finite hl hr)
      (by rwa [uIcc_of_le order])
  have inc (a : ℝ) (ha : a ∈ Icc (-S) S) (b : ℝ) (hb : b ∈ Icc (-S) S) (ab : a ≤ b) :
      (b-a)/2 ≤ clock y h φ b - clock y h φ a ∧ clock y h φ b - clock y h φ a ≤ 15*(b-a) := by
    unfold clock
    rw [intervalIntegral.integral_interval_sub_left (finite born hb) (finite born ha)]
    exact duration e st passage heightRange ha.1 ab hb.2
  have mono : StrictMonoOn (clock y h φ) (Icc (-S) S) := by
    intro a ha b hb ab
    linarith [(inc a ha b hb ab.le).1]
  refine ⟨by simp [clock], cts, mono, inc, fun τ hτ => ?_⟩
  obtain ⟨t, ht, eq⟩ := intermediate_value_Icc order cts hτ
  refine ⟨⟨t, ht⟩, eq, fun r er => ?_⟩
  exact Subtype.ext (mono.injOn r.property ht (er.trans eq.symm))

/-- A quantitative interval of signed travel times about a birth that is separated
from both angular ends of the passing core. -/
theorem times_about_birth {y : ℝ → Plane} {S h φ d : ℝ} (c : ClockOn y S h φ)
    (born : φ ∈ Icc (-S) S) (room : 2 * d + |φ| ≤ S) {τ : ℝ} (time : |τ| ≤ d) :
    ∃! t : Icc (-S) S, clock y h φ t = τ := by
  obtain ⟨zero, _, _, inc, every⟩ := c
  have nonempty := born.1.trans born.2
  have left := (inc (-S) (left_mem_Icc.mpr nonempty) φ born born.1).1
  have right := (inc φ born S (right_mem_Icc.mpr nonempty) born.2).1
  rw [zero] at left right
  obtain ⟨ltime, rtime⟩ := abs_le.mp time
  apply every τ
  constructor
  · linarith [neg_abs_le φ]
  · linarith [le_abs_self φ]

end PlasmaLean.Design.DommaschkRadialPassingTime
