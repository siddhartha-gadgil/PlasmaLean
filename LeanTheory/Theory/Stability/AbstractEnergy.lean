/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Conditional energy theorem on a real normed space

Complete elementary proof of the abstract energy identity, with position and
velocity in the same normed space. Both symmetric forms are continuous bilinear
maps. Conservation is conditional on a differentiable solution on [0,T]. Evolution
existence, the V-to-H embedding variant, and a PDE bridge are separate targets.
-/
public section

noncomputable section
namespace LeanTheory.Stability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Kinetic plus potential energy for two time-independent bilinear forms. -/
@[expose] def energy (m a : E →L[ℝ] E →L[ℝ] ℝ) (x v : E) : ℝ :=
  (m v v + a x x) / 2

/-- The evolution equation and form symmetry imply zero energy derivative. -/
theorem energy_hasDerivAt_zero (m a : E →L[ℝ] E →L[ℝ] ℝ)
    (hm : ∀ u v, m u v = m v u) (ha : ∀ u v, a u v = a v u)
    (x v : ℝ → E) (acc : E) (t : ℝ)
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v acc t)
    (motion : m acc (v t) + a (x t) (v t) = 0) :
    HasDerivAt (fun s => energy m a (x s) (v s)) 0 t := by
  have dm := m.hasDerivAt_of_bilinear (fun _ => hv) (fun _ => hv)
  have da := a.hasDerivAt_of_bilinear (fun _ => hx) (fun _ => hx)
  convert (dm.add da).div_const 2 using 1
  · dsimp [energy]
  · rw [hm (v t) acc, ha (v t) (x t)]
    linarith

/-- Energy is conserved up to every time in the supplied existence interval. -/
theorem energy_conserved (m a : E →L[ℝ] E →L[ℝ] ℝ)
    (hm : ∀ u v, m u v = m v u) (ha : ∀ u v, a u v = a v u)
    (x v acc : ℝ → E) {T t : ℝ}
    (hx : ∀ s ∈ Set.Icc 0 T, HasDerivAt x (v s) s)
    (hv : ∀ s ∈ Set.Icc 0 T, HasDerivAt v (acc s) s)
    (motion : ∀ s ∈ Set.Icc 0 T, ∀ η, m (acc s) η + a (x s) η = 0)
    (ht : t ∈ Set.Icc 0 T) : energy m a (x t) (v t) = energy m a (x 0) (v 0) := by
  have hd : ∀ s ∈ Set.Icc 0 T, HasDerivWithinAt
      (fun r => energy m a (x r) (v r)) 0 (Set.Icc 0 T) s := by
    intro s hs
    exact (energy_hasDerivAt_zero m a hm ha x v (acc s) s
      (hx s hs) (hv s hs) (motion s hs (v s))).hasDerivWithinAt
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (C := 0) (by intros; simp) t ht
  simp only [zero_mul] at hb
  have he : ‖energy m a (x t) (v t) - energy m a (x 0) (v 0)‖ = 0 := by
    simpa using le_antisymm hb (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

/-- A positive potential-energy lower bound and nonnegative inertia bound displacement. -/
theorem displacement_bound (m a : E →L[ℝ] E →L[ℝ] ℝ) (x v : E)
    {c E₀ : ℝ} (hc : 0 < c) (hm : 0 ≤ m v v)
    (ha : c * ‖x‖ ^ 2 ≤ a x x) (hE : energy m a x v = E₀) :
    ‖x‖ ^ 2 ≤ 2 * E₀ / c := by
  apply (le_div_iff₀ hc).mpr
  dsimp [energy] at hE
  nlinarith

/-- Nonnegative potential energy controls velocity through positive inertia. -/
theorem velocity_bound (m a : E →L[ℝ] E →L[ℝ] ℝ) (x v : E)
    {m₀ E₀ : ℝ} (hm₀ : 0 < m₀) (hm : m₀ * ‖v‖ ^ 2 ≤ m v v)
    (ha : 0 ≤ a x x) (hE : energy m a x v = E₀) :
    ‖v‖ ^ 2 ≤ 2 * E₀ / m₀ := by
  apply (le_div_iff₀ hm₀).mpr
  dsimp [energy] at hE
  nlinarith

end LeanTheory.Stability
