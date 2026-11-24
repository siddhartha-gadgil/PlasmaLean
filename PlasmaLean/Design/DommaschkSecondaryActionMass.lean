/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeLowerAction
public import PlasmaLean.Design.DommaschkActionQ0R478

/-! # The lower action packet at the second phase-zero launch -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSecondaryActionMass
open Certificates.MirrorActionQuadrature DommaschkActionQ0R478 Set

abbrev mass : ℝ := 383207832386575 / 281474976710656
abbrev target : ℝ := 6799610938322487 / 5000000000000000
abbrev height : ℝ := 5300546391395933 / 5000000000000000

theorem integer_mass : total slabs = 4598493988638900 := by kernel_fact

theorem target_lt_mass : target < mass := by norm_num [target,mass]

/-- Every complete physical cover of the original 654 lower blocks bounds its integral. -/
theorem floor_of_cover {f w : ℝ → ℝ} (cells : Covers false w f height (-327 / 64) slabs)
    (hn : ∀ t ∈ Icc (-327 / 64 : ℝ) (327 / 64), 0 ≤ w t)
    (cf : ContinuousOn f (Icc (-327 / 64 : ℝ) (327 / 64)))
    (cw : ContinuousOn w (Icc (-327 / 64 : ℝ) (327 / 64))) :
    target < mass ∧ mass ≤ Kinetic.MirrorHeightAction.action f w (-327 / 64) (327 / 64) height := by
  have b := Certificates.NativeActionInterval.exact_lower_mass DommaschkActionQ0R478.checked.len
    cells hn cf cw
  rw [integer_mass] at b
  refine ⟨target_lt_mass, ?_⟩
  norm_num [mass] at b ⊢
  exact b

end PlasmaLean.Design.DommaschkSecondaryActionMass
