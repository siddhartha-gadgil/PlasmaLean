/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkActionFlightFloor
public import PlasmaLean.Theory.Kinetic.MirrorActionVariationLower

/-! # A radial derivative certificate target from the pilot energy and time bounds -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialActionCriterion
open Set Real MeasureTheory Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope
open Kinetic.MirrorActionVariation DommaschkActionFlightFloor

/-- On any observed first well with the certified pilot time and action estimates,
two signed pointwise variation inequalities would force a radial action slope above 1/3. -/
theorem slope_gt_third {f w df dw : ℝ → ℝ} {l r h : ℝ} (lr : l ≤ r)
    (J : IntervalIntegrable (fun t => w t * √(2 * (h - f t))) volume l r)
    (T : IntervalIntegrable (fun t => w t / √(2 * (h - f t))) volume l r)
    (var : IntervalIntegrable (fun t => variation h (f t) (w t) (df t) (dw t)) volume l r)
    (cap : action f w l r h ≤ DommaschkActionArchiveMass.mass)
    (time : allFloor < oneWayBounceTime w f h l r)
    (controls : ∀ t ∈ Ioo l r, f t < h →
      0 ≤ w t ∧ -(w t / 32) ≤ dw t ∧ df t ≤ -(1 / 144)) :
    (1 / 3 : ℝ) < ∫ t in l..r, variation h (f t) (w t) (df t) (dw t) := by
  have cmp := variation_lower (A := 1 / 32) (k := 1 / 144) lr J T var (by
    intro t ht active
    obtain ⟨pos, arc, field⟩ := controls t ht active
    exact ⟨pos, by linarith only [arc], field⟩)
  norm_num [allFloor, DommaschkActionArchiveMass.mass] at cap time
  linarith only [cmp, cap, time]

/-- Restrict the criterion to the exact first mirrors of an N-116 trajectory.
Uniqueness transports the action cap, time floor and integrability to the nominated well. -/
theorem at_first_well {φ h l r : ℝ} {y : ℝ → Certificates.PositionFrameSlabs.Plane}
    {df dw : ℝ → ℝ} (known : TimeBounds φ y)
    (hh : h ∈ Icc (DommaschkFirstMirrorLaunchSign.height false : ℝ)
      (DommaschkFirstMirrorLaunchSign.height true))
    (well : LaunchWell (DommaschkNativeWellAction.field y) 0 h l r)
    (J : IntervalIntegrable (fun t => DommaschkActionFlightFloor.weight y t *
      √(2 * (h - DommaschkNativeWellAction.field y t))) volume l r)
    (var : IntervalIntegrable (fun t => variation h (DommaschkNativeWellAction.field y t)
      (DommaschkActionFlightFloor.weight y t) (df t) (dw t)) volume l r)
    (controls : ∀ t ∈ Ioo l r, 0 ≤ DommaschkActionFlightFloor.weight y t ∧
      -(DommaschkActionFlightFloor.weight y t / 32) ≤ dw t ∧ df t ≤ -(1 / 144)) :
    (1 / 3 : ℝ) < ∫ t in l..r, variation h (DommaschkNativeWellAction.field y t)
      (DommaschkActionFlightFloor.weight y t) (df t) (dw t) := by
  obtain ⟨L, _, R, _, _, first, cap, finite, low, _, _⟩ := known h hh
  obtain ⟨rfl, rfl⟩ := well.unique first
  exact slope_gt_third (well.left_lt.trans well.lt_right).le J finite var cap low
    (fun t ht _ => controls t ht)

end PlasmaLean.Design.DommaschkRadialActionCriterion
