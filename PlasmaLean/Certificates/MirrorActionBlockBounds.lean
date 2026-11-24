/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionUniformCells
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Composing physical covers over consecutive action blocks -/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorActionQuadrature

open MeasureTheory Set

/-- A measured arclength density and a continuous strength profile give an
integrable action whenever the density and clipped speed are bounded. -/
theorem action_le_uniform {a b h A S : ℝ} {w f : ℝ → ℝ} (ab : a ≤ b)
    (meas : AEStronglyMeasurable w (volume.restrict (Icc a b)))
    (cf : ContinuousOn f (Icc a b)) (nonneg : 0 ≤ S)
    (bounds : ∀ t ∈ Icc a b, 0 ≤ w t ∧ w t ≤ A ∧ max (2 * (h - f t)) 0 ≤ S ^ 2) :
    IntervalIntegrable (fun t => w t * Real.sqrt (2 * (h - f t))) volume a b ∧
      Kinetic.MirrorHeightAction.action f w a b h ≤ (b - a) * (A * S) := by
  let speed := fun t => Real.sqrt (2 * (h - f t))
  have cont : ContinuousOn speed (Icc a b) :=
    (continuousOn_const.mul (continuousOn_const.sub cf)).sqrt
  have cap (t : ℝ) (ht : t ∈ Icc a b) : ‖w t * speed t‖ ≤ A * S := by
    obtain ⟨hw, wa, hs⟩ := bounds t ht
    have sv : speed t ≤ S := (Real.sqrt_le_iff.mpr ⟨nonneg, (le_max_left _ _).trans hs⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (Real.sqrt_nonneg _))]
    exact mul_le_mul wa sv (Real.sqrt_nonneg _) (hw.trans wa)
  have integrable : IntervalIntegrable (fun t => w t * speed t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ab]
    apply IntegrableOn.of_bound measure_Icc_lt_top
      (meas.mul (cont.aestronglyMeasurable measurableSet_Icc)) (A * S)
    exact (ae_restrict_mem measurableSet_Icc).mono cap
  refine ⟨integrable, ?_⟩
  calc
    Kinetic.MirrorHeightAction.action f w a b h ≤ ∫ _ in a..b, A * S :=
      intervalIntegral.integral_mono_on ab integrable intervalIntegrable_const
        (fun t ht => (le_abs_self _).trans (cap t ht))
    _ = (b - a) * (A * S) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]

/-- Joining consecutive pieces preserves the same functions of physical time and
starts the second piece at exactly the outgoing clock of the first. -/
theorem covers_append_iff {u : Bool} {w f : ℝ → ℝ} {h : ℝ} (a : ℝ)
    (left right : List (Block u)) :
    Covers u w f h a (left ++ right) ↔
      Covers u w f h a left ∧ Covers u w f h (a + left.length / 64) right := by
  induction left generalizing a with
  | nil => simp [Covers]
  | cons b bs ih =>
    simp only [List.cons_append, Covers, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [show a + 1 / 64 + bs.length / 64 = a + (bs.length + 1 : ℝ) / 64 by ring]
    exact and_assoc.symm

/-- A common lower floor on all packed upper columns certifies a physical
upper cover for an arbitrary consecutive list, including either endpoint. -/
theorem covers_of_floor {A G : ℕ} {w f : ℝ → ℝ} {h a : ℝ} (bs : List (Block true))
    (checked : ∀ b ∈ bs, floorTest A G 48 b.packed = true)
    (bound : ∀ t ∈ Set.Icc a (a + bs.length / 64),
      w t ≤ A / 1048576 ∧ max (2 * (h - f t)) 0 ≤ G / 67108864) :
    Covers true w f h a bs := by
  induction bs generalizing a with
  | nil => trivial
  | cons b bs ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at bound
    constructor
    · apply cells_of_floor 48 (checked b (List.mem_cons_self ..))
      intro t ht
      apply bound t
      have len := Nat.cast_nonneg (α := ℝ) bs.length
      exact ⟨ht.1, by norm_num at ht; linarith [ht.2]⟩
    · apply ih (fun b h => checked b (List.mem_cons_of_mem _ h))
      intro t ht
      apply bound t
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

end PlasmaLean.Certificates.MirrorActionQuadrature
