/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Linarith

/-!
# Finite-time control of an approximate invariant

Note 04 supplies the elementary complete proof: a derivative bound integrates to
epsilon times elapsed time. A loss event separated by a larger invariant gap is
impossible. This is a scalar observable theorem; actual trajectories, field bounds,
initial sets, and any full-orbit/reduced-orbit error must be supplied separately.
-/
public section

namespace PlasmaLean.Kinetic

/-- A uniform derivative bound controls drift everywhere in [0,T]. -/
theorem invariant_drift {K K' : ℝ → ℝ} {ε T t : ℝ}
    (hK : ∀ s ∈ Set.Icc 0 T, HasDerivAt K (K' s) s)
    (hbound : ∀ s ∈ Set.Icc 0 T, |K' s| ≤ ε)
    (ht : t ∈ Set.Icc 0 T) : |K t - K 0| ≤ ε * t := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hK s hs).hasDerivWithinAt)
    (fun s hs => (by simpa [Real.norm_eq_abs] using hbound s (Set.Ico_subset_Icc_self hs))) t ht
  simpa [Real.norm_eq_abs] using h

/-- A loss state cannot be reached while the certified invariant drift is below the gap. -/
theorem excludes_loss {K K' : ℝ → ℝ} {ε T t k₀ kloss : ℝ}
    (hK : ∀ s ∈ Set.Icc 0 T, HasDerivAt K (K' s) s)
    (hbound : ∀ s ∈ Set.Icc 0 T, |K' s| ≤ ε)
    (ht : t ∈ Set.Icc 0 T) (initial : K 0 ≤ k₀) (gap : ε * t < kloss - k₀) :
    K t < kloss := by
  have h := (abs_le.mp (invariant_drift hK hbound ht)).2
  linarith

/-- Exact invariance is recovered when the derivative bound collapses to zero. -/
theorem exact_invariant {K K' : ℝ → ℝ} {T t : ℝ}
    (hK : ∀ s ∈ Set.Icc 0 T, HasDerivAt K (K' s) s)
    (hbound : ∀ s ∈ Set.Icc 0 T, |K' s| ≤ 0)
    (ht : t ∈ Set.Icc 0 T) : K t = K 0 := by
  have h := invariant_drift hK hbound ht
  simp only [zero_mul] at h
  have hz : |K t - K 0| = 0 := by simpa using le_antisymm h (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

end PlasmaLean.Kinetic
