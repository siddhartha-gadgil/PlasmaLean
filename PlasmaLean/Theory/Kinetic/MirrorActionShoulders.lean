/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope

/-! # Adding action on the two intervals outside an already integrated core -/

public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionEnvelope
open Set MeasureTheory MirrorHeightAction

/-- A pointwise lower bound on the action density on each side of a certified core
adds their actual widths to the same single-passage action. -/
theorem action_add_shoulders {f w : ℝ → ℝ} {a b c d h v m : ℝ}
    (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d)
    (cf : ContinuousOn f (Icc a d)) (cw : ContinuousOn w (Icc a d))
    (left : ∀ t ∈ Icc a b, v ≤ w t * Real.sqrt (2 * (h - f t)))
    (right : ∀ t ∈ Icc c d, v ≤ w t * Real.sqrt (2 * (h - f t)))
    (core : m ≤ action f w b c h) :
    m + ((b - a) + (d - c)) * v ≤ action f w a d h := by
  let g := fun t => w t * Real.sqrt (2 * (h - f t))
  have cont : ContinuousOn g (Icc a d) :=
    cw.mul (continuousOn_const.mul (continuousOn_const.sub cf)).sqrt
  have integ {x y : ℝ} (xy : x ≤ y) (ax : a ≤ x) (yd : y ≤ d) :
      IntervalIntegrable g volume x y :=
    (cont.mono (Icc_subset_Icc ax yd)).intervalIntegrable_of_Icc xy
  have small {x y : ℝ} (xy : x ≤ y) (ax : a ≤ x) (yd : y ≤ d)
      (floor : ∀ t ∈ Icc x y, v ≤ g t) : (y - x) * v ≤ ∫ t in x..y, g t := by
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using
      intervalIntegral.integral_mono_on xy intervalIntegrable_const (integ xy ax yd) floor
  have L := small ab le_rfl (bc.trans cd) left
  have R := small cd (ab.trans bc) le_rfl right
  change m ≤ ∫ t in b..c, g t at core
  change _ ≤ ∫ t in a..d, g t
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (integ (ab.trans bc) le_rfl cd) (integ cd (ab.trans bc) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals
      (integ ab le_rfl (bc.trans cd)) (integ bc ab cd)]
  linarith

end PlasmaLean.Kinetic.MirrorActionEnvelope
