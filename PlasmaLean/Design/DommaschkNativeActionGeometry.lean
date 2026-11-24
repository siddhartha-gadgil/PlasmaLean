/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeActionModel
public import PlasmaLean.Design.DommaschkTaylorResidual

/-! # Physical meanings of the two compensated numerators in the action packet -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkNativeActionGeometry
open DommaschkKam DommaschkBounceField DommaschkCompensatedAction DommaschkMirrorEndpointSign
open DommaschkMirrorTubeCrossing Certificates.PositionFrameSlabs
open Certificates.TrajectoryTaylorModel DommaschkBounceTaylor
set_option maxRecDepth 8192

theorem checked_product {a b out : Model} {s x y : ℝ} (hs : |s| ≤ 1)
    (ha : a.Mem s x) (hb : b.Mem s y) (h : Matches ((⟨7, 80⟩ : Format).mul a b) out) :
    out.Mem s (x*y) := by
  rw [← h.eq]
  exact Format.mul_mem _ hs ha hb

theorem checked_sum {a b out : Model} {s x y : ℝ} (ha : a.Mem s x) (hb : b.Mem s y)
    (h : Matches (addModel a b) out) : out.Mem s (x+y) := by
  rw [← h.eq]
  exact mem_add ha hb

theorem checked_neg {a out : Model} {s x : ℝ} (ha : a.Mem s x)
    (h : Matches (TaylorResidual.neg a) out) : out.Mem s (-x) := by
  rw [← h.eq]
  exact TaylorResidual.neg_mem ha

theorem squared_numerator {x : Plane} (hR : 0 < x 0) (φ : ℝ) :
    ((x 0) * atPoint dD (x 0) φ (x 1)) ^ 2 + (atPoint dnR (x 0) φ (x 1)) ^ 2 +
      (atPoint dnZ (x 0) φ (x 1)) ^ 2 = (x 0) ^ 16 * (strength φ x) ^ 2 := by
  simpa only [gap, zero_mul, sub_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), ← sq,
    strength] using gap_eq hR 0 φ (x 1)

theorem compensated_numerator {x : Plane} (hR : 0 < x 0) (φ : ℝ) (k h : ℚ) :
    -((x 0) ^ 2 * atPoint (shiftedD k) (x 0) φ (x 1) *
      (2 * atPoint dD (x 0) φ (x 1) - atPoint (shiftedD k) (x 0) φ (x 1)) +
      (atPoint dnR (x 0) φ (x 1)) ^ 2 + (atPoint dnZ (x 0) φ (x 1)) ^ 2 +
      (x 0) ^ 16 * (((k ^ 2 - h ^ 2 : ℚ) : ℝ))) =
    (x 0) ^ 16 * ((h : ℝ) ^ 2 - (strength φ x) ^ 2) := by
  have hf := gap_from_shift k (R := x 0) (u := x 0 - dkR0) (z := x 1)
    (c := Real.cos (2 * φ)) (s := Real.sin (2 * φ)) (h := (h : ℝ)) rfl
  change gap (x 0) (h : ℝ) (atPoint dD (x 0) φ (x 1)) (atPoint dnR (x 0) φ (x 1))
    (atPoint dnZ (x 0) φ (x 1)) = _ at hf
  rw [gap_eq hR] at hf
  simp only [Rat.cast_sub, Rat.cast_pow]
  unfold atPoint strength
  linarith only [hf]

end PlasmaLean.Design.DommaschkNativeActionGeometry
