/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSecondaryHeightCollar
public import PlasmaLean.Design.DommaschkLowerActionPath
public import PlasmaLean.Theory.Kinetic.MirrorActionShoulders

/-! # Lower action on the entire closed interval of an incoming physical trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkIncomingHeightAction
open Certificates.PositionFrameSlabs DommaschkLowerActionPath Set
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open DommaschkSecondaryHeightCollar DommaschkSecondaryActionMass

/-- On a closed trace window the analytic arclength density is continuous. Its action agrees
with the Cartesian derivative integral because the two weights coincide on the open interval. -/
theorem closed_inputs {entry : State} {fr br : List Step} {T a b : ℝ} {y : ℝ → Plane}
    (p : Signed entry fr br T y) (ab : a ≤ b) (left : -T ≤ a) (right : b ≤ T)
    (valid : ∀ t ∈ Icc a b, DommaschkSignedTraceDomain.Region (y t)) :
    ContinuousOn (field y) (Icc a b) ∧ ContinuousOn (density y) (Icc a b) ∧
    ∀ h, action (field y) (density y) a b h =
      action (field y) (DommaschkNativeWellAction.density y) a b h := by
  have sub := Icc_subset_Icc left right
  have cont : ContinuousOn y (Icc a b) :=
    fun t ht => (p.ode t (sub ht)).continuousWithinAt.mono sub
  refine ⟨?_,DommaschkSignedTraceDensity.continuousOn_density_region cont valid,?_⟩
  · change ContinuousOn (fun t => DommaschkMirrorTubeCrossing.strength t (y t)) (Icc a b)
    simpa only [one_mul] using DommaschkMirrorTubeCrossing.continuousOn_strength cont 1
      (fun t ht => by linarith [(valid t ht).1.1])
  · intro h
    apply intervalIntegral.integral_congr_Ioo_of_le ab
    intro t ht
    have j : t ∈ Ioo (-T) T := ⟨left.trans_lt ht.1, ht.2.trans_le right⟩
    have box := valid t (Ioo_subset_Icc_self ht)
    have az := DommaschkSignedTraceDenominator.regular t box.1 box.2
    have w := DommaschkPhysicalActionPanel.arcDensity_of_ode
      ((p.ode t (Ioo_subset_Icc_self j)).hasDerivAt (Icc_mem_nhds j.1 j.2))
      (by linarith [box.1.1]) (by linarith)
    exact congrArg (fun v => v * _) w.symm

/-- Add two equal incoming widths using the certified magnitude and physical density floors,
without any assumption that the available trace already reaches a mirror. -/
theorem lower_on_window {f w : ℝ → ℝ} {A h m : ℝ} (width : 1 / 2 ≤ A)
    (hh : lower ≤ h) (cf : ContinuousOn f (Icc (-A) A)) (cw : ContinuousOn w (Icc (-A) A))
    (density_floor : ∀ t ∈ Icc (-A) A, 7 / 8 ≤ w t)
    (clear : ∀ t ∈ Icc (-A) A,
      f t < (↑(DommaschkFirstMirrorLaunchSign.height false - 1 / 270000) : ℝ))
    (core : m ≤ action f w (-(1 / 2)) (1 / 2) h) :
    m + (2 * A - 1) * ((7 / 8) * (161 / 5000)) ≤ action f w (-A) A h := by
  have margin : (161 / 5000 : ℝ) ^ 2 <
      2 * (lower - ↑(DommaschkFirstMirrorLaunchSign.height false - 1 / 270000)) := by
    norm_num [lower,height,DommaschkFirstMirrorLaunchSign.height]
  have point (t : ℝ) (ht : t ∈ Icc (-A) A) :
      (7 / 8) * (161 / 5000) ≤ w t * Real.sqrt (2 * (h - f t)) := by
    have speed : (161 / 5000 : ℝ) < Real.sqrt (2 * (h - f t)) :=
      (Real.lt_sqrt (by norm_num)).2 (margin.trans_le
        (mul_le_mul_of_nonneg_left (sub_le_sub hh (clear t ht).le) (by norm_num)))
    exact mul_le_mul (density_floor t ht) speed.le (by norm_num)
      ((by norm_num : (0 : ℝ) ≤ 7 / 8).trans (density_floor t ht))
  have z := action_add_shoulders (neg_le_neg width) (by norm_num) width cf cw
    (fun t ht => point t ⟨ht.1,ht.2.trans (by linarith)⟩)
    (fun t ht => point t ⟨(by linarith : -A ≤ 1 / 2).trans ht.1,ht.2⟩) core
  convert z using 1
  ring

end PlasmaLean.Design.DommaschkIncomingHeightAction
