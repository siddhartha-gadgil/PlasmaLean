/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionTransverse

/-! # An atomic field profile at, above, and below the critical height -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionFlight

open Set Real MirrorHeightAction MirrorActionEnvelope

/-- The unit trace of a constant zero field gives the scalar square-root primitive. -/
theorem flat_action (h : ℝ) : action (fun _ => 0) (fun _ => 1) 0 1 h = √(2 * h) := by
  simp [action]

theorem flat_time (h : ℝ) : oneWayBounceTime (fun _ => 1) (fun _ => 0) h 0 1 =
    1 / √(2 * h) := by
  simp [oneWayBounceTime]

/-- Every height off the atom has the predicted derivative, including heights below the field. -/
theorem flat_regular {h : ℝ} (nz : h ≠ 0) :
    HasDerivAt (action (fun _ => 0) (fun _ => 1) 0 1)
      (oneWayBounceTime (fun _ => 1) (fun _ => 0) h 0 1) h := by
  rw [flat_time, show action (fun _ => 0) (fun _ => 1) 0 1 = fun k => √(2 * k) from
    funext flat_action]
  have d := (hasDerivAt_sqrt (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) nz)).comp h
    (hasDerivAt_const_mul 2)
  apply d.congr_deriv
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- At the atom the integral identity still holds while the action has no finite derivative. -/
theorem flat_critical :
    ¬ DifferentiableAt ℝ (action (fun _ => 0) (fun _ => 1) 0 1) 0 := by
  rw [show action (fun _ => 0) (fun _ => 1) 0 1 = fun k => √(2 * k) from funext flat_action]
  intro diff
  have ds := diff.hasDerivAt.mul diff.hasDerivAt
  have z : HasDerivWithinAt (fun t : ℝ => 2 * t) 0 (Ici 0) 0 := by
    apply (ds.hasDerivWithinAt.congr_deriv (by simp)).congr_of_mem _ self_mem_Ici
    intro t ht
    change 2 * t = √(2 * t) * √(2 * t)
    exact (mul_self_sqrt (mul_nonneg (by norm_num) ht)).symm
  have two := (hasDerivAt_const_mul (x := (0 : ℝ)) 2).hasDerivWithinAt (s := Ici 0)
  have eq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ z two
  norm_num at eq

end PlasmaLean.Kinetic.MirrorActionFlight
