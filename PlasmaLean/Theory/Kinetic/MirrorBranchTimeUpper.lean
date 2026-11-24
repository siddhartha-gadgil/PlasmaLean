/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorTimeActionBounds

/-! # One-way time from a field-strength margin on the core and a transverse outer branch -/

public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionEnvelope
open Set MeasureTheory MirrorHeightBand

/-- An upper bound using the density ceiling, the core reciprocal speed, the collar
derivative estimate, and the actual distance between the two turning points. -/
theorem branch_time_upper {f w : ℝ → ℝ} {a b L U k D W A : ℝ}
    (branch : Branch f a b L U k) (ord : L ≤ U) (h : Icc L U)
    (ha : 0 ≤ a) (hk : 0 < k) (hL : 0 ≤ L) (hD : 0 ≤ D) (hW : 0 ≤ W) (hA : 0 < A)
    (factor : (h : ℝ) ≤ k * D ^ 2)
    (weights : ∀ t ∈ Ioo 0 (branch.time h), w t ≤ W)
    (gap : ∀ t ∈ Ioo 0 (branch.time ⟨L, le_rfl, ord⟩),
      (1 / A) ^ 2 ≤ 2 * ((h : ℝ) - f t))
    (finite : IntervalIntegrable (fun t => w t / Real.sqrt (2 * ((h : ℝ) - f t)))
      volume 0 (branch.time h)) :
    let s := branch.time ⟨L, le_rfl, ord⟩
    oneWayBounceTime w f h 0 (branch.time h) ≤
      s * (W * A) + 2 * (W * D) * Real.sqrt (branch.time h - s) := by
  let s := branch.time ⟨L, le_rfl, ord⟩
  let r := branch.time h
  have start : 0 ≤ s := ha.trans (branch.interior_time ⟨L, le_rfl, ord⟩).1.le
  have order : s ≤ r := branch.ordered.monotone h.2.1
  have central (t : ℝ) (ht : t ∈ Ioo 0 s) :
      w t / Real.sqrt (2 * ((h : ℝ) - f t)) ≤ W * A := by
    have root : 1 / A ≤ Real.sqrt (2 * ((h : ℝ) - f t)) := by
      simpa only [Real.sqrt_sq (one_div_nonneg.mpr hA.le)] using Real.sqrt_le_sqrt (gap t ht)
    have hp := lt_of_lt_of_le (one_div_pos.mpr hA) root
    apply (div_le_iff₀ hp).mpr
    calc
      w t ≤ W := weights t ⟨ht.1, ht.2.trans_le order⟩
      _ = W * A * (1 / A) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left root (mul_nonneg hW hA.le)
  have collar (t : ℝ) (ht : t ∈ Ioo s r) :
      w t / Real.sqrt (2 * ((h : ℝ) - f t)) ≤ (W * D) / Real.sqrt (r - t) := by
    have inv := branch_collar_time_bound branch ord hk hL hD factor ht ha
    calc
      _ ≤ W / Real.sqrt (2 * ((h : ℝ) - f t)) :=
        div_le_div_of_nonneg_right (weights t ⟨start.trans_lt ht.1, ht.2⟩) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left inv hW using 1 <;> ring
  simpa only [zero_sub, sub_zero, oneWayBounceTime, s, r] using
    half_time_upper start order finite central collar

end PlasmaLean.Kinetic.MirrorActionEnvelope
