/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Order.IntermediateValue

/-! # Closed-interval ODE uniqueness from regularity along one solution -/

@[expose] public section
namespace PlasmaLean.Fields
open Set Filter Topology Metric

/-- Two solutions with a common terminal value agree everywhere on a closed time
interval. Joint local C¹ regularity is required only on the graph of the known
solution. The other solution can be given solely by its ODE on the interval. -/
theorem ode_eqOn_of_terminal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {a b : ℝ} {x y : ℝ → E}
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (F t (x t)) (Icc a b) t)
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (F t (y t)) (Icc a b) t)
    (regular : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 (fun p : ℝ × E => F p.1 p.2) (t, y t))
    (end_eq : x b = y b) : EqOn x y (Icc a b) := by
  have cx : ContinuousOn x (Icc a b) := fun t ht => (hx t ht).continuousWithinAt
  have cy : ContinuousOn y (Icc a b) := fun t ht => (hy t ht).continuousWithinAt
  let same : Set ℝ := {t | x t = y t}
  have closed : IsClosed (same ∩ Icc a b) := by
    rw [inter_comm]
    exact isClosed_Icc.isClosed_eq cx cy
  apply closed.Icc_subset_of_forall_exists_lt end_eq
  intro c hc u hu
  obtain ⟨eq, ac, cb⟩ := hc
  change x c = y c at eq
  change u < c at hu
  have inside : c ∈ Icc a b := ⟨ac.le, cb⟩
  obtain ⟨K, U, nb, lip⟩ := (regular c inside).exists_lipschitzOnWith
  have g₁ : ContinuousWithinAt (fun t => (t, x t)) (Icc a b) c :=
    continuousWithinAt_id.prodMk (cx c inside)
  have g₂ : ContinuousWithinAt (fun t => (t, y t)) (Icc a b) c :=
    continuousWithinAt_id.prodMk (cy c inside)
  have nx : {t | (t, x t) ∈ U} ∈ 𝓝[Icc a b] c := g₁ (by simpa only [eq] using nb)
  have ny : {t | (t, y t) ∈ U} ∈ 𝓝[Icc a b] c := g₂ nb
  obtain ⟨ε, εpos, small⟩ := Metric.mem_nhdsWithin_iff.mp (inter_mem nx ny)
  let d := max (max u a) (c - ε/2)
  have dc : d < c := max_lt (max_lt hu ac) (by linarith)
  have ad : a ≤ d := (le_max_right u a).trans (le_max_left _ _)
  have ud : u ≤ d := (le_max_left u a).trans (le_max_left _ _)
  have sub : Icc d c ⊆ Icc a b := Icc_subset_Icc ad cb
  have near (t) (ht : t ∈ Icc d c) : (t, x t) ∈ U ∧ (t, y t) ∈ U := by
    apply small
    refine ⟨?_, sub ht⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have lo : c - ε/2 ≤ d := le_max_right _ _
    constructor <;> linarith [ht.1,ht.2]
  have both := ODE_solution_unique_of_mem_Icc_left (v := F) (s := fun t => {v | (t,v) ∈ U})
    (K := K) (a := d) (b := c)
    (fun t _ => lipschitzOnWith_iff_dist_le_mul.mpr (fun p hp q hq => by
      simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using
        lip.dist_le_mul (t,p) hp (t,q) hq))
    (cx.mono sub)
    (fun t ht => (hx t (sub (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem ⟨lt_of_le_of_lt ad ht.1, le_trans ht.2 cb⟩))
    (fun t ht => (near t (Ioc_subset_Icc_self ht)).1) (cy.mono sub)
    (fun t ht => (hy t (sub (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem ⟨lt_of_le_of_lt ad ht.1, le_trans ht.2 cb⟩))
    (fun t ht => (near t (Ioc_subset_Icc_self ht)).2) eq
  exact ⟨d, both ⟨le_rfl, dc.le⟩, ud, dc⟩

end PlasmaLean.Fields
