/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPairedActionProfiles

/-! # A denominator-cleared comparison of arclength at a common physical angle -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPairedArcRatio
open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkMirrorTubeCrossing DommaschkKam
open DommaschkPairedActionProfiles DommaschkNativeActionGeometry
set_option maxRecDepth 8192

abbrev ratio : ℝ := 3999 / 4000

theorem physical_identity {φ : ℝ} {x : Plane} (r : 0 < x 0)
    (d : 0 < atPoint dD (x 0) φ (x 1)) :
    let D := atPoint dD (x 0) φ (x 1)
    let A := (atPoint dnR (x 0) φ (x 1)) ^ 2 + (atPoint dnZ (x 0) φ (x 1)) ^ 2
    0 ≤ weight φ x ∧ D ^ 2 * (weight φ x) ^ 2 = (x 0) ^ 2 * D ^ 2 + A := by
  dsimp only
  have e := squared_numerator r φ
  rw [weight_eq r d]
  refine ⟨div_nonneg (mul_nonneg (pow_nonneg r.le _) (norm_nonneg _)) d.le, ?_⟩
  field_simp [d.ne']
  linarith only [e]

/-- A cleared scalar margin certifies the common ceiling without dividing Taylor models. -/
theorem ceiling {φ : ℝ} {x : Plane} (r : 0 < x 0)
    (margin : 0 ≤ (17 / 16) ^ 2 * (x 0) ^ 16 -
      (((x 0) * atPoint dD (x 0) φ (x 1)) ^ 2 + (atPoint dnR (x 0) φ (x 1)) ^ 2 +
        (atPoint dnZ (x 0) φ (x 1)) ^ 2)) : strength φ x ≤ 17 / 16 := by
  rw [squared_numerator r, mul_comm ((17 / 16 : ℝ) ^ 2)] at margin
  exact le_of_sq_le_sq (le_of_mul_le_mul_left (sub_nonneg.mp margin) (pow_pos r _)) (by norm_num)

/-- A positive margin retains the dependence of both field evaluations on the same angle. -/
theorem compare {ri ro di do_ ai ao wi wo k : ℝ} (diPos : 0 < di) (doPos : 0 < do_)
    (wPos : 0 ≤ wo) (inner : di ^ 2 * wi ^ 2 = ri ^ 2 * di ^ 2 + ai)
    (outer : do_ ^ 2 * wo ^ 2 = ro ^ 2 * do_ ^ 2 + ao)
    (margin : 0 ≤ ((ro - ri) * (ro + ri) + (1 - k ^ 2) * (ri * ri)) *
      ((di * di) * (do_ * do_)) + ao * (di * di) - k ^ 2 * (ai * (do_ * do_))) :
    k * wi ≤ wo := by
  have eq : (wo ^ 2 - (k * wi) ^ 2) * (di ^ 2 * do_ ^ 2) =
      ((ro - ri) * (ro + ri) + (1 - k ^ 2) * (ri * ri)) * ((di * di) * (do_ * do_)) +
        ao * (di * di) - k ^ 2 * (ai * (do_ * do_)) := by
    linear_combination di ^ 2 * outer - k ^ 2 * do_ ^ 2 * inner
  rw [← eq] at margin
  have pos := mul_pos (sq_pos_of_pos diPos) (sq_pos_of_pos doPos)
  exact le_of_sq_le_sq (sub_nonneg.mp (nonneg_of_mul_nonneg_left margin pos)) wPos

/-- The two squared-field ceilings convert the squared drop to the physical field drop. -/
theorem compared_of_squared {φ : ℝ} {x y : Plane}
    (inner : strength φ x ≤ 17 / 16) (outer : strength φ y ≤ 17 / 16)
    (drop : 2 * (17 / 16) * (1 / 18000) ≤ (strength φ x) ^ 2 - (strength φ y) ^ 2)
    (arc : ratio * weight φ x ≤ weight φ y) : Compared φ x y := by
  refine ⟨inner, outer, ?_, arc⟩
  by_contra! h
  have sum : 0 < strength φ x + strength φ y := by
    by_contra! z
    have a : 0 ≤ strength φ x := norm_nonneg _
    have b : 0 ≤ strength φ y := norm_nonneg _
    have hx : strength φ x = 0 := by linarith
    have hy : strength φ y = 0 := by linarith
    norm_num [hx, hy] at drop
  have small := mul_lt_mul_of_pos_right
    (show strength φ x - strength φ y < 1 / 18000 by linarith only [h]) sum
  nlinarith only [small, inner, outer, drop]

end PlasmaLean.Design.DommaschkPairedArcRatio
