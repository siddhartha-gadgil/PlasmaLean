/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSecondaryActionMass
public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope

/-! # A strictly interior window suffices for the second launch's lower action target -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSecondaryActionCore
open Certificates.MirrorActionQuadrature DommaschkActionQ0R478 DommaschkSecondaryActionMass Set
open Kinetic.MirrorHeightAction

/-- The original chronological blocks from negative through positive elapsed row 321. -/
def inner : List (Block false) := (slabs.drop 5).take 644

abbrev innerMass : ℝ := 1148484200086339 / 844424930131968

theorem inner_length : inner.length = 322 + 322 := by kernel_fact
theorem inner_total : total inner = 4593936800345356 := by kernel_fact

/-- The symmetric window shortened by one additional slab on each side misses the target. -/
theorem previous_total : total ((slabs.drop 6).take 642) = 4591932807427064 := by kernel_fact

theorem crosses_target : 4591932807427064 / (3072 * 1099511627776 : ℝ) < target ∧
    target < innerMass := by norm_num [target,innerMass]

/-- A cover only up to elapsed time 322/64 proves the strict lower target on any enclosing
interval, including the interval between the two first mirrors when their locations are given. -/
theorem floor_on_enclosing_interval {f w : ℝ → ℝ} {l r : ℝ}
    (left : l ≤ -322 / 64) (right : 322 / 64 ≤ r)
    (cells : Covers false w f height (-322 / 64) inner)
    (hn : ∀ t ∈ Icc l r, 0 ≤ w t) (cf : ContinuousOn f (Icc l r))
    (cw : ContinuousOn w (Icc l r)) : target < innerMass ∧ innerMass ≤ action f w l r height := by
  have sub : Icc (-322 / 64 : ℝ) (322 / 64) ⊆ Icc l r := Icc_subset_Icc left right
  have estimate := Certificates.NativeActionInterval.exact_lower_mass inner_length cells
    (fun t ht => hn t (sub ht)) (cf.mono sub) (cw.mono sub)
  rw [inner_total] at estimate
  have core : innerMass ≤ action f w (-322 / 64) (322 / 64) height := by
    norm_num [innerMass] at estimate ⊢
    exact estimate
  exact ⟨crosses_target.2, core.trans (Kinetic.MirrorActionEnvelope.action_mono_interval
    left (by norm_num) right cf cw hn)⟩

end PlasmaLean.Design.DommaschkSecondaryActionCore
