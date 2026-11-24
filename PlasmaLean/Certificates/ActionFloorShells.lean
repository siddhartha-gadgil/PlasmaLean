/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PolynomialActionFloor

/-! # Integrating lower polynomials on two outward clocks and adjoining an interior integral -/

@[expose] public section
namespace PlasmaLean.Certificates.PolynomialActionFloor
open MeasureTheory Set

/-- An outward interval and its negative-time reflection contribute two physical integrals. -/
structure Shell (F : ℝ → ℝ) (a b mass : ℝ) : Prop where
  forward : mass ≤ ∫ t in a..b, F t
  backward : mass ≤ ∫ t in -b..-a, F t

theorem shell_of_bounds {F p : ℝ → ℝ} {a b m : ℝ} (ha : 0 ≤ a) (ab : a ≤ b)
    (continuous : ContinuousOn F (Icc (-b) b)) (poly : Continuous p)
    (integral : (∫ t in a..b, p t) = m)
    (both : ∀ t ∈ Icc a b, p t ≤ F t ∧ p t ≤ F (-t)) : Shell F a b m := by
  have inc : Icc a b ⊆ Icc (-b) b := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have neg : MapsTo (fun t : ℝ => -t) (Icc a b) (Icc (-b) b) :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have first := (continuous.mono inc).intervalIntegrable_of_Icc (μ := volume) ab
  have second := (continuous.comp continuous_neg.continuousOn neg).intervalIntegrable_of_Icc
    (μ := volume) ab
  constructor
  · rw [← integral]
    exact intervalIntegral.integral_mono_on ab (poly.intervalIntegrable _ _) first
      (fun t ht => (both t ht).1)
  · rw [← integral, ← intervalIntegral.integral_comp_neg F]
    exact intervalIntegral.integral_mono_on ab (poly.intervalIntegrable _ _) second
      (fun t ht => (both t ht).2)

theorem Shell.adjoin {F : ℝ → ℝ} {a b m lower : ℝ} (ha : 0 ≤ a) (ab : a ≤ b)
    (continuous : ContinuousOn F (Icc (-b) b)) (h : Shell F a b m)
    (center : lower ≤ ∫ t in -a..a, F t) : lower + 2 * m ≤ ∫ t in -b..b, F t := by
  have regular {x y : ℝ} (h₁ : -b ≤ x) (h₂ : x ≤ y) (h₃ : y ≤ b) :
      IntervalIntegrable F volume x y :=
    (continuous.mono (Icc_subset_Icc h₁ h₃)).intervalIntegrable_of_Icc h₂
  have whole := intervalIntegral.integral_add_adjacent_intervals
    (regular (by linarith) (show -b ≤ -a by linarith) (by linarith))
    (regular (by linarith) (show -a ≤ a by linarith) (by linarith))
  have last := intervalIntegral.integral_add_adjacent_intervals
    (regular (by linarith) (show -b ≤ a by linarith) (by linarith))
    (regular (by linarith) ab le_rfl)
  linarith only [whole, last, h.forward, h.backward, center]

end PlasmaLean.Certificates.PolynomialActionFloor
