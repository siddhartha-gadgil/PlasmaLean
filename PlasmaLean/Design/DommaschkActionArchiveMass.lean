/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionExactMass
public import PlasmaLean.Design.DommaschkActionQ0R470

/-! # Exact rectangle mass for the pilot upper-action archive -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkActionArchiveMass
open Certificates.MirrorActionQuadrature DommaschkActionQ0R470 Set

abbrev mass : ℝ := 1146552112157123 / 844424930131968

theorem integer_mass : total slabs = 4586208448628492 := by kernel_fact

theorem target_gap :
    6799610938322487 / 5000000000000000 - mass =
      274671348019911459639037 / (128849018880000000000000000 : ℝ) := by norm_num [mass]

theorem closed_upper {f w : ℝ → ℝ} {h : ℝ}
    (cells : Covers true w f h (-325 / 64) slabs)
    (hn : ∀ t ∈ Icc (-325 / 64 : ℝ) (325 / 64), 0 ≤ w t)
    (cf : ContinuousOn f (Icc (-325 / 64 : ℝ) (325 / 64)))
    (cw : ContinuousOn w (Icc (-325 / 64 : ℝ) (325 / 64))) :
    Kinetic.MirrorHeightAction.action f w (-325 / 64) (325 / 64) h ≤ mass := by
  have estimate := exact_upper_mass DommaschkActionQ0R470.checked.len cells hn cf cw
  rw [integer_mass] at estimate
  norm_num [mass] at estimate ⊢
  exact estimate

end PlasmaLean.Design.DommaschkActionArchiveMass
