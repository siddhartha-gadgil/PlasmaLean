/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionVariation

/-! # Signed lower bounds for transverse mirror-action variation -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionVariation
open Set Real MeasureTheory MirrorHeightAction MirrorActionEnvelope

/-- A decrease in field strength on the accessible part of the line gives a positive
term proportional to the flight time. Loss of arclength costs at most A times the action. -/
theorem variation_lower {f w df dw : ℝ → ℝ} {a b h A k : ℝ} (ab : a ≤ b)
    (J : IntervalIntegrable (fun t => w t * √(2 * (h - f t))) volume a b)
    (T : IntervalIntegrable (fun t => w t / √(2 * (h - f t))) volume a b)
    (var : IntervalIntegrable (fun t => variation h (f t) (w t) (df t) (dw t)) volume a b)
    (controls : ∀ t ∈ Ioo a b, f t < h → 0 ≤ w t ∧ -(A * w t) ≤ dw t ∧ df t ≤ -k) :
    k * oneWayBounceTime w f h a b - A * action f w a b h ≤
      ∫ t in a..b, variation h (f t) (w t) (df t) (dw t) := by
  let q (t : ℝ) := √(2 * (h - f t))
  have point (t : ℝ) (ht : t ∈ Ioo a b) :
      k * (w t / q t) - A * (w t * q t) ≤ variation h (f t) (w t) (df t) (dw t) := by
    by_cases active : f t < h
    · obtain ⟨wpos, arc, field⟩ := controls t ht active
      have speed : 0 ≤ q t := sqrt_nonneg _
      have p := mul_le_mul_of_nonneg_right arc speed
      have n := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left field wpos) speed
      change _ ≤ dw t * q t - w t * df t / q t
      rw [show w t * -k / q t = -(k * (w t / q t)) by ring] at n
      linarith only [p, n]
    · have zero : q t = 0 := sqrt_eq_zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr (not_lt.mp active)))
      change _ ≤ dw t * q t - w t * df t / q t
      simp [zero]
  have compare := intervalIntegral.integral_mono_on_of_le_Ioo ab
    ((T.const_mul k).sub (J.const_mul A)) var point
  rw [intervalIntegral.integral_sub (T.const_mul k) (J.const_mul A),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at compare
  exact compare

end PlasmaLean.Kinetic.MirrorActionVariation
