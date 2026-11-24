/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPairedArcRatio

/-! # Radial profile comparisons from signed native action numerators -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkNativePairedProfiles
open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkMirrorTubeCrossing DommaschkKam
open DommaschkPairedActionProfiles DommaschkNativeActionGeometry DommaschkPairedArcRatio
set_option maxRecDepth 8192

theorem native_weight_identity {φ : ℝ} {x : Plane} (r : 0 < x 0)
    (d : 0 < atPoint dD (x 0) φ (x 1)) : 0 ≤ weight φ x ∧
    (atPoint dD (x 0) φ (x 1)) ^ 2 * (weight φ x) ^ 2 = (x 0) ^ 16 * (strength φ x) ^ 2 := by
  obtain ⟨pos, h⟩ := physical_identity r d
  refine ⟨pos, h.trans ?_⟩
  rw [← squared_numerator r]
  ring

theorem native_ratio {di do_ ui uo wi wo k : ℝ} (diPos : 0 < di) (doPos : 0 < do_)
    (wPos : 0 ≤ wo) (inner : di ^ 2 * wi ^ 2 = ui) (outer : do_ ^ 2 * wo ^ 2 = uo)
    (gap : 0 ≤ uo * (di * di) - k ^ 2 * (ui * (do_ * do_))) : k * wi ≤ wo := by
  have cleared : 0 ≤ (wo ^ 2 - (k * wi) ^ 2) * (di ^ 2 * do_ ^ 2) := by
    rw [← inner, ← outer] at gap
    linarith only [gap]
  exact le_of_sq_le_sq (sub_nonneg.mp
    (nonneg_of_mul_nonneg_left cleared (mul_pos (sq_pos_of_pos diPos) (sq_pos_of_pos doPos)))) wPos

theorem native_ceiling {p h f : ℝ} (hp : 0 < p)
    (gap : 0 ≤ p * (h ^ 2 - f ^ 2) + ((17 / 16) ^ 2 - h ^ 2) * p) : f ≤ 17 / 16 := by
  have cleared : p * f ^ 2 ≤ p * ((17 / 16) ^ 2) := by linarith only [gap]
  exact le_of_sq_le_sq (le_of_mul_le_mul_left cleared hp) (by norm_num)

theorem native_field {p P h f F d : ℝ} (hp : 0 < p) (hP : 0 < P)
    (gap : 0 ≤ P * (h ^ 2 - F ^ 2) * p - p * (h ^ 2 - f ^ 2) * P - d * (p * P)) :
    d ≤ f ^ 2 - F ^ 2 := by
  apply le_of_mul_le_mul_right _ (mul_pos hp hP)
  linarith only [gap]

end PlasmaLean.Design.DommaschkNativePairedProfiles
