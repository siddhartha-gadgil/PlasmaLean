/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith

/-!
# Local contraction validation and its equation bridge

The Banach fixed-point theorem is reused from pinned Mathlib. Domain coverage,
residual size, and a Lipschitz constant on the full closed ball are hypotheses.
The radii-polynomial lemma only discharges scalar inequalities. It cannot supply
missing derivative or infinite-tail bounds for a plasma equilibrium operator.
-/
public section

namespace PlasmaLean.Certificates

/-- Negative radii-polynomial value at a positive radius gives strict contraction
and ball-invariance inequalities. -/
theorem radii_conditions {Y Z₀ Z₂ r : ℝ} (hY : 0 ≤ Y) (hr : 0 < r)
    (hp : Y + (Z₀ - 1) * r + Z₂ * r ^ 2 < 0) :
    Z₀ + Z₂ * r < 1 ∧ Y + (Z₀ + Z₂ * r) * r ≤ r := by
  constructor
  · nlinarith
  · nlinarith

/-- A residual enclosure and contraction on the entire ball yield a unique nearby fixed point. -/
theorem local_fixedPoint {E : Type*} [MetricSpace E] [CompleteSpace E]
    (T : E → E) (center : E) {r Y : ℝ} {K : NNReal}
    (hr : 0 ≤ r) (hK : K < 1)
    (residual : dist (T center) center ≤ Y)
    (lip : LipschitzOnWith K T (Metric.closedBall center r))
    (budget : Y + (K : ℝ) * r ≤ r) :
    ∃ x ∈ Metric.closedBall center r, T x = x ∧
      ∀ y ∈ Metric.closedBall center r, T y = y → y = x := by
  have hc : center ∈ Metric.closedBall center r := Metric.mem_closedBall_self hr
  have maps : Set.MapsTo T (Metric.closedBall center r) (Metric.closedBall center r) := by
    intro x hx
    have hl := lip.dist_le_mul x hx center hc
    have hb : dist x center ≤ r := hx
    have hm := mul_le_mul_of_nonneg_left hb K.coe_nonneg
    have hd := dist_triangle (T x) (T center) center
    change dist (T x) center ≤ r
    linarith
  have contraction : ContractingWith K (maps.restrict T _ _) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact lip.dist_le_mul x x.property y y.property
  obtain ⟨x, hx, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete maps contraction hc (edist_ne_top _ _)
  refine ⟨x, hx, hfix, ?_⟩
  intro y hy hfy
  have hdist := lip.dist_le_mul y hy x hx
  rw [hfy, hfix] at hdist
  have hk : (K : ℝ) < 1 := hK
  have hz : dist y x = 0 := by nlinarith [dist_nonneg (x := y) (y := x)]
  exact dist_eq_zero.mp hz

/-- Injectivity of the approximate inverse converts a fixed point into an equation solution. -/
theorem fixedPoint_equation {E : Type*} [AddCommGroup E]
    (A : E →+ E) (F : E → E) (hA : Function.Injective A) (x : E)
    (hfix : x - A (F x) = x) : F x = 0 := by
  apply hA
  rw [map_zero]
  exact sub_eq_self.mp hfix

/-- Without injectivity, a fixed-point claim can be completely vacuous. -/
theorem zero_inverse_counterexample :
    (∀ x : ℝ, x - 0 * (1 : ℝ) = x) ∧ ¬ (∃ _x : ℝ, (1 : ℝ) = 0) := by
  simp

end PlasmaLean.Certificates
