/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
public import PlasmaLean.Design.DommaschkPositionFramesBack

/-! # Physical mirror signs at the ends of a trace slab -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorEndpointSign
open Certificates Certificates.PositionFrameSlabs TrajectoryTaylorModel DommaschkBounceField
open DommaschkMirrorTubeCrossing DommaschkKam DommaschkKam.DkPoly Contract

/-- Cancellation in the two factors preserves the common radial input to both field terms. -/
def gap (R h D nr nz : ℝ) : ℝ :=
  (R*D - h*R^8) * (R*D + h*R^8) + nr^2 + nz^2

theorem gap_eq {R : ℝ} (hR : 0 < R) (h φ z : ℝ) :
    gap R h (atPoint dD R φ z) (atPoint dnR R φ z) (atPoint dnZ R φ z) =
      R^16 * (‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖^2-h^2) := by
  rw [norm_sq_eq_strengthSq hR]
  unfold gap Certificates.RadialSlabs.strengthSq
  field_simp [hR.ne']
  ring

/-- Positive means above the mirror height, negative means below it. -/
def oriented (right : Bool) (x h : ℝ) : Prop := if right then h < x else x < h

theorem physical_sign (right : Bool) {R h φ z : ℝ} (hR : 0 < R) (hh : 0 ≤ h)
    (bound : oriented right (gap R h (atPoint dD R φ z) (atPoint dnR R φ z)
      (atPoint dnZ R φ z)) 0) :
    oriented right ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖ h := by
  rw [gap_eq hR] at bound
  cases right <;> simp only [oriented, Bool.false_eq_true, ↓reduceIte] at bound ⊢
  · exact (sq_lt_sq₀ (norm_nonneg _) hh).mp
      (sub_neg.mp (neg_of_mul_neg_right bound (by positivity)))
  · exact (sq_lt_sq₀ hh (norm_nonneg _)).mp
      (sub_pos.mp (pos_of_mul_pos_right bound (by positivity)))

/-- Use the radius itself as the common normalized variable in all field polynomials. -/
theorem radial_parameter {R : ℝ} {c e : ℤ} (he : 0 < e)
    (h : |R - (c : ℝ) / 2 ^ 80| ≤ (e : ℝ) / 2 ^ 80) :
    ∃ s : ℝ, |s| ≤ 1 ∧ (ofDyadic 80 [c, e] 0).Mem s R := by
  have pos : (0 : ℝ) < e := by exact_mod_cast he
  let s := ((2:ℝ)^80*R-c)/e
  have eq : s * e = (2:ℝ)^80 * R - c := div_mul_cancel₀ _ pos.ne'
  refine ⟨s, ?_, ?_⟩
  · rw [abs_le] at h ⊢
    exact ⟨(le_div_iff₀ pos).mpr (by linarith [h.1]), (div_le_iff₀ pos).mpr (by linarith [h.2])⟩
  · rw [mem_ofDyadic_iff]
    simp only [List.map_cons, List.map_nil, QPoly.eval_cons, QPoly.eval_nil, Rat.cast_intCast,
      mul_zero, add_zero, Int.cast_zero, abs_nonpos_iff]
    linarith

/-- Move a fixed-time trigonometric enclosure to a constant model in the radial variable. -/
theorem at_fixed_time {m : Model} {q : ℚ} {x : ℝ} (hm : m.Mem (q : ℝ) x) (s : ℝ) :
    (⟨[QPoly.evalQ m.poly q],m.radius⟩ : Model).Mem s x := by
  simpa only [Model.Mem, QPoly.eval_cons, QPoly.eval_nil, mul_zero, add_zero,
    QPoly.eval_cast] using hm

/-- A physical tube supplies a coordinate enclosure even at a slab boundary. -/
theorem coordinate {previous : PositionFrameSlabs.State} {r : Step} {a t : ℝ} {x : Plane}
    (hx : x ∈ (physicalSlab previous r a).tube t) (j : Fin 2) :
    |x j - reference a r t j| ≤ r.physicalOut/(2:ℝ)^80 := by
  calc
    _ ≤ ‖x - reference a r t‖ := PiLp.norm_apply_le _ _
    _ ≤ _ := by rw [← dist_eq_norm]; exact hx.2

theorem point_radial (r z : ℤ) : point ⟨r,z⟩ 0 = (r : ℝ) / 2^80 := rfl

theorem point_vertical (r z : ℤ) : point ⟨r,z⟩ 1 = (z : ℝ) / 2^80 := rfl

end PlasmaLean.Design.DommaschkMirrorEndpointSign
