/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import PlasmaLean.Theory.Fields.ClosedIntervalODEUniqueness

/-! # A common local time and displacement bound for every initial condition in a neighborhood -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.LocalFlowDisplacement
open Set Metric Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous dependence of the actual local flow lets all initial points in one open set
share a closed time window, a prescribed displacement bound and an open regularity domain. -/
theorem common_window {f : E → E} {U : Set E} {c : E} {d : ℝ}
    (smooth : ContDiffAt ℝ 1 f c) (op : IsOpen U) (hc : c ∈ U) (hd : 0 < d) :
    ∃ W : Set E, IsOpen W ∧ c ∈ W ∧ W ⊆ U ∧ ∃ T > 0, ∀ p ∈ W,
      ∃ y : ℝ → E, y 0 = p ∧ ∀ t ∈ Icc 0 T,
        HasDerivAt y (f (y t)) t ∧ y t ∈ U ∧ dist (y t) p < d := by
  obtain ⟨ε, pos, a, r, L, K, rpos, pl⟩ := IsPicardLindelof.of_contDiffAt_one smooth
  obtain ⟨flow, sol, joint⟩ := (pl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hz : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith, by linarith⟩
  have rpos' : 0 < (r : ℝ) := rpos
  have central : flow (c, 0) = c := (sol c (mem_closedBall_self r.coe_nonneg)).1
  have continuous : ContinuousAt flow (c, 0) := joint.continuousAt
    (prod_mem_nhds (closedBall_mem_nhds c rpos') (Icc_mem_nhds hz.1 hz.2))
  have stays : ∀ᶠ z : E × ℝ in 𝓝 (c, 0), flow z ∈ U :=
    continuous (op.mem_nhds (by rw [central]; exact hc))
  have close : ∀ᶠ z : E × ℝ in 𝓝 (c, 0), flow z ∈ U ∧ dist (flow z) z.1 < d :=
    stays.and ((continuous.dist continuous_fst.continuousAt).eventually_lt_const
      (by rw [central]; simpa using hd))
  obtain ⟨ρ, ρpos, fit⟩ := Metric.mem_nhds_iff.mp close
  let W := ball c (min (r : ℝ) ρ) ∩ U
  let T := min ε ρ / 2
  have tpos : 0 < T := half_pos (lt_min pos ρpos)
  have te : T < ε := by dsimp [T]; linarith [min_le_left ε ρ]
  have tr : T < ρ := by dsimp [T]; linarith [min_le_right ε ρ]
  refine ⟨W, isOpen_ball.inter op, ⟨mem_ball_self (lt_min rpos' ρpos), hc⟩,
    inter_subset_right, T, tpos, ?_⟩
  intro p hp
  have near : dist p c < min (r : ℝ) ρ := hp.1
  obtain ⟨start, ode⟩ := sol p ((near.trans_le (min_le_left _ _)).le)
  refine ⟨fun t => flow (p, t), start, fun t ht => ?_⟩
  have mt : t ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have pair : (p, t) ∈ ball (c, 0) ρ := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ⟨near.trans_le (min_le_right _ _), ht.2.trans_lt tr⟩
  exact ⟨(ode t (Ioo_subset_Icc_self mt)).hasDerivAt (Icc_mem_nhds mt.1 mt.2), fit pair⟩

omit [CompleteSpace E] in
/-- Local smoothness along the known branch forces any other partial solution with the
same initial value to follow it, even if regularity of the other solution was not assumed. -/
theorem agree_from_start {f : E → E} {x y : ℝ → E} {T : ℝ}
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (f (y t)) t)
    (smooth : ∀ t ∈ Icc 0 T, ContDiffAt ℝ 1 f (y t)) (start : x 0 = y 0) :
    EqOn x y (Icc 0 T) := by
  have reverse {z : ℝ → E} (dz : ∀ t ∈ Icc 0 T, HasDerivAt z (f (z t)) t)
      (s : ℝ) (hs : s ∈ Icc (-T) 0) :
      HasDerivWithinAt (fun a => z (-a)) (-(f (z (-s)))) (Icc (-T) 0) s := by
    have neg : -s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simpa only [Function.comp_def, id_eq, neg_one_smul] using
      ((dz (-s) neg).scomp s (hasDerivAt_id s).neg).hasDerivWithinAt (s := Icc (-T) 0)
  have rev := ode_eqOn_of_terminal (F := fun _ v => -(f v)) (reverse hx) (reverse hy)
    (fun t ht => ((smooth (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).comp
      (t, y (-t)) contDiffAt_snd).neg) (by simpa only [neg_zero] using start)
  intro t ht
  simpa only [neg_neg] using rev (show -t ∈ Icc (-T) 0 from ⟨neg_le_neg ht.2, neg_nonpos.mpr ht.1⟩)

end PlasmaLean.Fields.LocalFlowDisplacement
