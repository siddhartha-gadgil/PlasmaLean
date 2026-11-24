/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.TrajectoryHarmonicSections

/-! # The first QA2R harmonic in physical coordinates at the opposite section -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkOppositeHarmonic
open Certificates Certificates.QPoly Certificates.TrajectoryTaylorModel
open Certificates.TrajectoryTrig Certificates.TrajectoryHarmonicPacket

/-- Shift the model centre as well as the physical phase. Its coefficients
are negated and its original error radius is retained. -/
theorem first {i : ℕ} (p : Packet i) (back sine : Bool) {t : ℝ}
    (ht : t ∈ Set.Icc ((i : ℝ) / 64) (((i : ℝ) + 1) / 64)) :
    (negative ((p back 0).model sine)).Mem (128 * t - (2 * i + 1 : ℝ))
      (wave sine (2 * (Real.pi / 2 + (if back then -t else t)))) := by
  have original := physical_section p true back 0 sine ht
  simp only [ite_true, Fin.val_zero, Nat.cast_zero, zero_add, pow_one, mul_one,
    neg_one_mul] at original
  have sign_flip (u v : ℝ) : -u - v = -(u + v) := by ring
  simp only [Model.Mem, sign_flip, abs_neg] at original
  simpa only [Model.Mem, negative, eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul,
    sub_neg_eq_add] using original

end PlasmaLean.Design.DommaschkOppositeHarmonic
