/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeWellAction

/-!
# Opposite-section obstruction for the phase-zero radial bracket

The rational bounds are outputs of the directed physical ODE and action
enclosure. The application states their physical input explicitly.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeActionStrip
open Set DommaschkNativeWellAction

def tile (k : Fin 7) : Set ℝ :=
  Icc ((470 + (k : ℝ)) / 1000) ((if k = 6 then 478 else 471 + (k : ℝ)) / 1000)

/-- Directed lower bounds on the upper-height first-well action, on six
adjacent intervals of width 0.001 and one of width 0.002. -/
def actionFloor : Fin 7 → ℚ :=
  ![3140470404350409367 / 2305843009213693952, 4713756579888970541 / 3458764513820540928,
    3144539708700991931 / 2305843009213693952, 3146576331037095963 / 2305843009213693952,
    9445842606335543981 / 6917529027641081856, 4725972288480847627 / 3458764513820540928,
    1177210714492671449 / 864691128455135232]

theorem covers {u : ℝ} (hu : u ∈ Icc (47 / 100 : ℝ) (239 / 500)) : ∃ k, u ∈ tile k := by
  obtain ⟨hl, hh⟩ := hu
  by_cases a : u ≤ 471 / 1000
  · exact ⟨0, by norm_num [tile]; constructor <;> linarith⟩
  by_cases b : u ≤ 472 / 1000
  · exact ⟨1, by norm_num [tile]; constructor <;> linarith⟩
  by_cases c : u ≤ 473 / 1000
  · exact ⟨2, by norm_num [tile]; constructor <;> linarith⟩
  by_cases d : u ≤ 474 / 1000
  · exact ⟨3, by norm_num [tile]; constructor <;> linarith⟩
  by_cases e : u ≤ 475 / 1000
  · exact ⟨4, by norm_num [tile]; constructor <;> linarith⟩
  by_cases g : u ≤ 476 / 1000
  · exact ⟨5, by norm_num [tile]; constructor <;> linarith⟩
  exact ⟨6, by norm_num [tile]; constructor <;> linarith⟩

theorem strict_margins (k : Fin 7) : target + 3 / 2000 < (actionFloor k : ℝ) := by
  fin_cases k <;> norm_num [actionFloor, target, Matrix.cons_val]

/-- For any proposed phase-radius action, the seven pointwise lower bounds
exclude the prescribed action on the entire opposite sector of the narrow
strip. The action inputs retain their exact physical clock and height. -/
theorem excludes {J : ℝ → ℝ → ℝ}
    (lower : ∀ k φ u, |φ - Real.pi / 2| ≤ 1 / 2 ^ 19 → u ∈ tile k → (actionFloor k : ℝ) ≤ J φ u)
    {φ u : ℝ} (phase : |φ - Real.pi / 2| ≤ 1 / 2 ^ 19) (hu : u ∈ Icc (47 / 100 : ℝ) (239 / 500)) :
    target + 3 / 2000 < J φ u := by
  obtain ⟨k, hk⟩ := covers hu
  exact (strict_margins k).trans_le (lower k φ u phase hk)

/-- A moving label restricted to the old radial bracket also misses the target
when its launch phase reaches the opposite sector. -/
theorem moving_label_excluded {P : Type*} {phase radius : P → ℝ} {J : ℝ → ℝ → ℝ}
    (lower : ∀ k φ u, |φ - Real.pi / 2| ≤ 1 / 2 ^ 19 → u ∈ tile k → (actionFloor k : ℝ) ≤ J φ u)
    (p : P) (angle : |phase p - Real.pi / 2| ≤ 1 / 2 ^ 19)
    (hr : radius p ∈ Icc (47 / 100 : ℝ) (239 / 500)) :
    J (phase p) (radius p) ≠ target := by
  have h := excludes lower angle hr
  exact (lt_trans (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 3 / 2000)) h).ne'

end PlasmaLean.Design.DommaschkOppositeActionStrip
