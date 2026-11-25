/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialFamilyContinuity
public import PlasmaLean.Certificates.PositiveSubwell

/-! # A positive action core at an arbitrary physical section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkShiftedActionSubwell

open Set Certificates.PositionFrameSlabs DommaschkRadialFamilyContinuity DommaschkNativeWellAction
open DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel DommaschkSignedTraceDensity
open Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope Certificates.MirrorActionQuadrature

def fieldAt (s : ℝ) (y : ℝ → Plane) (t : ℝ) : ℝ := field y (s+t)

def arcAt (s : ℝ) (y : ℝ → Plane) (t : ℝ) : ℝ :=
  arcDensity (y (s+t) 0) (s+t) (y (s+t) 1)

/-- A core quadrature may use time relative to a fixed section, even though the
physical well and its Cartesian arclength use absolute geometric azimuth. -/
theorem shifted {s φ l r h : ℝ} {y : ℝ → Plane} (e : Enclosed y l r)
    (w : LaunchWell (field y) φ h l r) :
    LaunchWell (fieldAt s y) (φ-s) h (l-s) (r-s) ∧
    ContinuousOn (fieldAt s y) (Icc (l-s) (r-s)) ∧
    ContinuousOn (arcAt s y) (Icc (l-s) (r-s)) ∧
    (∀ t ∈ Icc (l-s) (r-s), 0 ≤ arcAt s y t) ∧
    action (fieldAt s y) (arcAt s y) (l-s) (r-s) h = action (field y) (density y) l r h := by
  have maps : MapsTo (fun t => s+t) (Icc (l-s) (r-s)) (Icc l r) :=
    fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have cy : ContinuousOn y (Icc l r) := fun t ht => (e.ode t ht).continuousAt.continuousWithinAt
  have cf : ContinuousOn (field y) (Icc l r) := by
    change ContinuousOn (fun t => strength t (y t)) _
    simpa only [one_mul] using continuousOn_strength cy 1
      (fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) (e.region t ht).1.1)
  let a := fun t => arcDensity (y t 0) t (y t 1)
  have eqWeight (t) (ht : t ∈ Icc l r) : density y t = a t := by
    have box := e.region t ht
    exact arcDensity_of_ode (e.ode t ht)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) box.1.1)
      ((by norm_num : (0 : ℝ) < 1 / 64).trans
        (DommaschkSignedTraceDenominator.regular t box.1 box.2))
  have al : s+(l-s) = l := by ring
  have ar : s+(r-s) = r := by ring
  have add : Continuous (fun t : ℝ => s+t) := continuous_const.add continuous_id
  have ca : ContinuousOn a (Icc l r) := continuousOn_density_region cy e.region
  have shiftedField : ContinuousOn (fieldAt s y) (Icc (l-s) (r-s)) := by
    apply (cf.comp add.continuousOn maps).congr
    intro t _
    simp only [fieldAt,Function.comp_apply]
  have shiftedArc : ContinuousOn (arcAt s y) (Icc (l-s) (r-s)) := by
    apply (ca.comp add.continuousOn maps).congr
    intro t _
    simp only [arcAt,Function.comp_apply,a]
  refine ⟨⟨sub_lt_sub_right w.left_lt s,sub_lt_sub_right w.lt_right s,?_,?_,?_⟩,
    shiftedField,shiftedArc,?_,?_⟩
  · simpa only [fieldAt,al] using w.left_hit
  · simpa only [fieldAt,ar] using w.right_hit
  · intro t ht
    exact w.accessible _ ⟨by linarith [ht.1],by linarith [ht.2]⟩
  · intro t ht
    change 0 ≤ a (s+t)
    rw [← eqWeight _ (maps ht)]
    exact norm_nonneg _
  · let g := fun t => a t * Real.sqrt (2*(h-field y t))
    change (∫ t in (l-s)..(r-s), g (s+t)) = _
    rw [intervalIntegral.integral_comp_add_left,al,ar]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (w.left_lt.trans w.lt_right).le]
    intro t ht
    dsimp [g]
    rw [eqWeight t ht]

end PlasmaLean.Design.DommaschkShiftedActionSubwell
