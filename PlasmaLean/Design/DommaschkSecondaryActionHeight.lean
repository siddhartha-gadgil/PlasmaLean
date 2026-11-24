/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.LowerActionHeightShift
public import PlasmaLean.Design.DommaschkSecondaryActionCore

/-! # Persistence of the second launch's action comparison on a height interval -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSecondaryActionHeight
open Certificates Certificates.MirrorActionQuadrature Set
open DommaschkSecondaryActionCore DommaschkSecondaryActionMass
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction

/-- For every height in the indicated window the original physical quadrature cover gives
a shifted mass. A positive floor also places every original panel strictly inside the well. -/
theorem shifted_cover {w f : ℝ → ℝ} {h : ℝ} {ticks floor : ℕ} {rows : List (Block false)}
    (length : rows.length = 322 + 322) (positive : 0 < floor)
    (checked : LowerActionHeightShift.blockTest ticks floor inner rows = true)
    (level : height - ticks / 134217728 ≤ h)
    (cells : Covers false w f height (-322 / 64) inner) : Covers false w f h (-322 / 64) rows ∧
      (∀ t ∈ Icc (-322 / 64 : ℝ) (322 / 64), f t < h) := by
  obtain ⟨cover, gap⟩ := LowerActionHeightShift.covers (h := h) (by linarith) _ checked cells
  refine ⟨cover, ?_⟩
  have nonempty : rows ≠ [] := by rintro rfl; simp at length
  have lower := gap nonempty
  rw [length] at lower
  rw [show (-322 / 64 : ℝ) + (↑(322 + 322 : ℕ) : ℝ) / 64 = 322 / 64 by norm_num] at lower
  intro t ht
  have hit := lower t ht
  have pos : (0 : ℝ) < floor / 67108864 := by positivity
  rcases lt_max_iff.mp (pos.trans_le hit) with good | bad
  · linarith
  · exact (lt_irrefl _ bad).elim

/-- The same positive squared-speed witnesses place the original core inside any first
well at the proposed height, without an independent estimate of either mirror's time. -/
theorem first_well {w f : ℝ → ℝ} {h l r : ℝ} {ticks floor : ℕ} {rows : List (Block false)}
    (length : rows.length = 322 + 322) (positive : 0 < floor)
    (checked : LowerActionHeightShift.blockTest ticks floor inner rows = true)
    (level : height - ticks / 134217728 ≤ h)
    (cells : Covers false w f height (-322 / 64) inner)
    (well : LaunchWell f 0 h l r)
    (hn : ∀ t ∈ Icc l r, 0 ≤ w t)
    (cf : ContinuousOn f (Icc l r))
    (cw : ContinuousOn w (Icc l r)) :
    l < -322 / 64 ∧ 322 / 64 < r ∧
      total rows / (3072 * 1099511627776 : ℝ) ≤ action f w l r h := by
  obtain ⟨cover,below⟩ := shifted_cover length positive checked level cells
  obtain ⟨left,right⟩ := well.contains_core (by norm_num) (by norm_num) (fun t ht =>
    below t ⟨ht.1.le,ht.2.le⟩)
  have lc : l < -322 / 64 := left.lt_of_ne (fun eq =>
    (below l ⟨eq.ge,by linarith [well.left_lt]⟩).ne well.left_hit)
  have rc : 322 / 64 < r := right.lt_of_ne (fun eq =>
    (below r ⟨by linarith [well.lt_right],eq.ge⟩).ne well.right_hit)
  have sub := Icc_subset_Icc left right
  have bound := NativeActionInterval.exact_lower_mass length cover
    (fun t ht => hn t (sub ht)) (cf.mono sub) (cw.mono sub)
  exact ⟨lc,rc,bound.trans (action_mono_interval left (by norm_num) right cf cw hn)⟩

end PlasmaLean.Design.DommaschkSecondaryActionHeight
