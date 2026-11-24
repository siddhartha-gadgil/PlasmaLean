/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSecondaryActionHeight
public import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
public import PlasmaLean.Theory.Kinetic.MirrorHeightBand

/-! # First-mirror displacement near the upper action height -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSecondaryHeightCollar
open Set Kinetic.MirrorHeightBand

/-- A height window on which the shifted lower action rectangles exceed the design target. -/
abbrev lower : ℝ := DommaschkSecondaryActionMass.height - 267 / 134217728

/-- Regard the proposed action window as part of the proved full mirror-height band. -/
def level {h : ℝ} (hh : h ∈ Icc lower DommaschkSecondaryActionMass.height) :
    Icc (DommaschkFirstMirrorLaunchSign.height false : ℝ)
      (DommaschkFirstMirrorLaunchSign.height true) :=
  ⟨h,(by
    norm_num [DommaschkFirstMirrorLaunchSign.height,lower,DommaschkSecondaryActionMass.height] :
    (DommaschkFirstMirrorLaunchSign.height false : ℝ) ≤ lower).trans hh.1, hh.2.trans_eq (by
    norm_num [DommaschkFirstMirrorLaunchSign.height, DommaschkSecondaryActionMass.height])⟩

/-- The whole window has at most this absolute displacement from the upper root on each branch. -/
theorem time_near_upper {f : ℝ → ℝ} {a b : ℝ}
    (br : Branch f a b (DommaschkFirstMirrorLaunchSign.height false)
      (DommaschkFirstMirrorLaunchSign.height true) (1 / 400))
    (hi : Icc (DommaschkFirstMirrorLaunchSign.height false : ℝ)
      (DommaschkFirstMirrorLaunchSign.height true))
    (top : (hi : ℝ) = DommaschkSecondaryActionMass.height)
    {h : ℝ} (hh : h ∈ Icc lower DommaschkSecondaryActionMass.height) :
    |br.time (level hh) - br.time hi| < 1 / 512 := by
  have pos : 0 ≤ lower := by norm_num [lower,DommaschkSecondaryActionMass.height]
  have sq := sq_le_sq₀ (pos.trans hh.1) ((pos.trans hh.1).trans hh.2) |>.mpr hh.2
  have sq' := sq_le_sq₀ pos (pos.trans hh.1) |>.mpr hh.1
  have room : DommaschkSecondaryActionMass.height ^ 2 - lower ^ 2 < (1 / 400 : ℝ) / 512 := by
    norm_num [lower,DommaschkSecondaryActionMass.height]
  have d := br.displacement (level hh) hi
  change 1 / 400 * |br.time (level hh) - br.time hi| ≤ |h ^ 2 - (hi : ℝ) ^ 2| at d
  rw [top, abs_of_nonpos (sub_nonpos.mpr sq)] at d
  rw [neg_sub] at d
  have gap := (d.trans (sub_le_sub_left sq' _)).trans_lt room
  apply (mul_lt_mul_iff_right₀ (by norm_num : (0 : ℝ) < 1 / 400)).mp
  simpa only [div_eq_mul_inv, one_mul] using gap

end PlasmaLean.Design.DommaschkSecondaryHeightCollar
