/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.TrajectoryFamilyContinuity

/-! # Joint continuity for trajectories launched at a parameter-dependent clock -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.TrajectoryFamily
open Set Filter Topology
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace P]

/-- Continuous birth times and positions determine a jointly continuous family of enclosed
solutions. The time window and compact spatial set may include both sides of every birth. -/
theorem continuousOn_of_moving_birth {V : E → E} {S : Set E} {a b : ℝ} {c : P → ℝ}
    {Y : P → ℝ → E} (compact : IsCompact S) (smooth : ∀ x ∈ S, ContDiffAt ℝ 1 V x)
    (clock : Continuous c) (times : ∀ p, c p ∈ Icc a b)
    (birth : Continuous fun p => Y p (c p))
    (ode : ∀ p s, s ∈ Icc a b → HasDerivAt (Y p) (V (Y p s)) s)
    (inside : ∀ p, MapsTo (Y p) (Icc a b) S) :
    ContinuousOn (fun z : P × ℝ => Y z.1 z.2) (univ ×ˢ Icc a b) := by
  by_cases ab : a ≤ b
  swap
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge ab)]
  have atStart : a ∈ Icc a b := left_mem_Icc.mpr ab
  apply continuousOn_of_enclosed compact smooth atStart _ ode inside
  obtain ⟨K, lip⟩ := compact_lipschitz compact smooth
  apply continuous_iff_continuousAt.mpr
  intro p
  have reference : Continuous (fun q => Y p (c q)) :=
    (show ContinuousOn (Y p) (Icc a b) from
      fun s hs => (ode p s hs).continuousAt.continuousWithinAt).comp_continuous clock times
  have vanish : Tendsto (fun q => dist (Y q (c q)) (Y p (c q)) * Real.exp (K * (b - a)))
      (𝓝 p) (𝓝 0) := by
    simpa using ((birth.dist reference).continuousAt (x := p)).tendsto.mul_const
      (Real.exp (K * (b - a)))
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ => dist_nonneg) (fun q => ?_) vanish
  have bound := dist_from_birth lip (times q) atStart (ode q) (ode p) (inside q) (inside p)
  have dt : |a - c q| ≤ b - a := by
    rw [abs_of_nonpos (sub_nonpos.mpr (times q).1)]
    linarith [(times q).2]
  exact bound.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left dt K.coe_nonneg)) dist_nonneg)

end PlasmaLean.Fields.TrajectoryFamily
