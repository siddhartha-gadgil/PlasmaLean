/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith

/-! # Continuous clearance from covered samples
The sample cover is quantified over the full domain. The supplied displacement
bounds can come from Lipschitz or derivative estimates; sampled separation alone
does not meet these hypotheses. Distances use one common metric and unit.
-/
public section

namespace PlasmaLean.Geometry

/-- Transfer one pair of sample clearances to nearby points. -/
theorem clearance_of_nearby {E : Type*} [PseudoMetricSpace E]
    (x y x₀ y₀ : E) {d e₁ e₂ : ℝ}
    (hs : d ≤ dist x₀ y₀) (hx : dist x₀ x ≤ e₁) (hy : dist y y₀ ≤ e₂) :
    d-e₁-e₂ ≤ dist x y := by
  have h₁ := dist_triangle x₀ x y₀
  have h₂ := dist_triangle x y y₀
  linarith

/-- A finite (or arbitrary) sample cover plus error bounds certifies every point pair. -/
theorem clearance_of_cover {E A B I J : Type*} [PseudoMetricSpace E]
    (f : A → E) (g : B → E) (s : I → E) (t : J → E) {d e₁ e₂ : ℝ}
    (cover₁ : ∀ a, ∃ i, dist (s i) (f a) ≤ e₁)
    (cover₂ : ∀ b, ∃ j, dist (g b) (t j) ≤ e₂)
    (samples : ∀ i j, d ≤ dist (s i) (t j)) :
    ∀ a b, d-e₁-e₂ ≤ dist (f a) (g b) := by
  intro a b
  obtain ⟨i, hi⟩ := cover₁ a
  obtain ⟨j, hj⟩ := cover₂ b
  exact clearance_of_nearby _ _ _ _ (samples i j) hi hj

/-- No interpolation loss when both enclosure radii collapse to zero. -/
theorem exact_samples {E : Type*} [PseudoMetricSpace E] (x y : E) {d : ℝ}
    (h : d ≤ dist x y) : d-0-0 ≤ dist x y := by simpa using h

/-- Lipschitz constants and full parameter-space covers discharge the interpolation
errors needed for continuous geometric clearance. -/
theorem clearance_of_lipschitz_cover {E A B I J : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace A] [PseudoMetricSpace B]
    (f : A → E) (g : B → E) (s : I → A) (t : J → B)
    {L₁ L₂ : NNReal} {r₁ r₂ d : ℝ}
    (hf : LipschitzWith L₁ f) (hg : LipschitzWith L₂ g)
    (cover₁ : ∀ a, ∃ i, dist (s i) a ≤ r₁)
    (cover₂ : ∀ b, ∃ j, dist b (t j) ≤ r₂)
    (samples : ∀ i j, d ≤ dist (f (s i)) (g (t j))) :
    ∀ a b, d - L₁ * r₁ - L₂ * r₂ ≤ dist (f a) (g b) := by
  apply clearance_of_cover f g (f ∘ s) (g ∘ t)
  · intro a
    obtain ⟨i, hi⟩ := cover₁ a
    exact ⟨i, hf.dist_le_mul_of_le hi⟩
  · intro b
    obtain ⟨j, hj⟩ := cover₂ b
    exact ⟨j, hg.dist_le_mul_of_le hj⟩
  · exact samples

end PlasmaLean.Geometry
