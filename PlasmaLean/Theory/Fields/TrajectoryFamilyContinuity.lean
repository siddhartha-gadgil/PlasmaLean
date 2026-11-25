/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Continuous dependence of two-sided enclosed trajectories on their birth parameters -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.TrajectoryFamily

open Set Filter Topology
open scoped NNReal
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace P]

private theorem forward_distance {V : E → E} {S : Set E} {K : ℝ≥0} {a b : ℝ}
    {f g : ℝ → E} (lip : LipschitzOnWith K V S)
    (fode : ∀ s ∈ Icc a b, HasDerivAt f (V (f s)) s)
    (gode : ∀ s ∈ Icc a b, HasDerivAt g (V (g s)) s)
    (fr : MapsTo f (Icc a b) S) (gr : MapsTo g (Icc a b) S) (ab : a ≤ b) :
    dist (f b) (g b) ≤ dist (f a) (g a) * Real.exp (K * (b - a)) := by
  apply dist_le_of_trajectories_ODE_of_mem (v := fun _ => V) (s := fun _ => S)
    (fun _ _ => lip) (fun t ht => (fode t ht).continuousAt.continuousWithinAt)
    (fun t ht => (fode t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun _ ht => fr (Ico_subset_Icc_self ht))
    (fun t ht => (gode t ht).continuousAt.continuousWithinAt)
    (fun t ht => (gode t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun _ ht => gr (Ico_subset_Icc_self ht)) le_rfl b (right_mem_Icc.mpr ab)

/-- A single compact, regular spatial enclosure supplies the Lipschitz constant for all
the trajectories. The estimate uses the same interior birth clock in either direction. -/
theorem dist_from_birth {V : E → E} {S : Set E} {K : ℝ≥0} {a b c t : ℝ}
    {f g : ℝ → E} (lip : LipschitzOnWith K V S) (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (fode : ∀ s ∈ Icc a b, HasDerivAt f (V (f s)) s)
    (gode : ∀ s ∈ Icc a b, HasDerivAt g (V (g s)) s)
    (fr : MapsTo f (Icc a b) S) (gr : MapsTo g (Icc a b) S) :
    dist (f t) (g t) ≤ dist (f c) (g c) * Real.exp (K * |t - c|) := by
  rcases le_total c t with forward | back
  · have sub := Icc_subset_Icc hc.1 ht.2
    rw [abs_of_nonneg (sub_nonneg.mpr forward)]
    exact forward_distance lip (fun s hs => fode s (sub hs)) (fun s hs => gode s (sub hs))
      (fun _ hs => fr (sub hs)) (fun _ hs => gr (sub hs)) forward
  · have rev (s : ℝ) (hs : s ∈ Icc (-c) (-t)) : -s ∈ Icc a b :=
      ⟨by linarith [ht.1, hs.2], by linarith [hc.2, hs.1]⟩
    have revode {y : ℝ → E} (ode : ∀ s ∈ Icc a b, HasDerivAt y (V (y s)) s)
        (s : ℝ) (hs : s ∈ Icc (-c) (-t)) : HasDerivAt (fun u => y (-u)) (-V (y (-s))) s := by
      simpa [Function.comp_def] using (ode (-s) (rev s hs)).scomp s (hasDerivAt_neg s)
    have negLip : LipschitzOnWith K (fun p => -V p) S := by
      apply lipschitzOnWith_iff_dist_le_mul.mpr
      intro p hp q hq
      simpa using lip.dist_le_mul p hp q hq
    have bound := forward_distance negLip (revode fode) (revode gode)
      (fun s hs => fr (rev s hs)) (fun s hs => gr (rev s hs)) (neg_le_neg back)
    simpa only [neg_neg, abs_of_nonpos (sub_nonpos.mpr back), neg_sub_neg, neg_sub] using bound

/-- Pointwise smoothness near each member of a compact spatial enclosure gives one
spatial Lipschitz constant even if the enclosure is not convex. -/
theorem compact_lipschitz {V : E → E} {S : Set E} (compact : IsCompact S)
    (smooth : ∀ x ∈ S, ContDiffAt ℝ 1 V x) : ∃ K, LipschitzOnWith K V S := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact compact
  intro x hx
  obtain ⟨K, s, hs, lip⟩ := (smooth x hx).exists_lipschitzOnWith
  exact ⟨K, s, mem_nhdsWithin_of_mem_nhds hs, lip⟩

/-- A parameter-continuous birth map determines a jointly continuous family on the
whole finite time window. Only the vector field is required to be smooth in space. -/
theorem continuousOn_of_enclosed {V : E → E} {S : Set E} {a b c : ℝ} {Y : P → ℝ → E}
    (compact : IsCompact S) (smooth : ∀ x ∈ S, ContDiffAt ℝ 1 V x)
    (hc : c ∈ Icc a b) (birth : Continuous fun p => Y p c)
    (ode : ∀ p s, s ∈ Icc a b → HasDerivAt (Y p) (V (Y p s)) s)
    (inside : ∀ p, MapsTo (Y p) (Icc a b) S) :
    ContinuousOn (fun z : P × ℝ => Y z.1 z.2) (univ ×ˢ Icc a b) := by
  obtain ⟨K, lip⟩ := compact_lipschitz compact smooth
  intro ⟨p,t⟩ hz
  let D := (univ : Set P) ×ˢ Icc a b
  have onTime : ContinuousOn (Y p) (Icc a b) :=
    fun s hs => (ode p s hs).continuousAt.continuousWithinAt
  have curve : ContinuousOn (fun z : P × ℝ => Y p z.2) D :=
    onTime.comp continuous_snd.continuousOn fun _ h => h.2
  have base : Continuous (fun z : P × ℝ => Y z.1 c) := birth.comp continuous_fst
  have bd := tendsto_iff_dist_tendsto_zero.mp
    ((base.continuousAt (x := (p,t))).continuousWithinAt (s := D))
  have pt := tendsto_iff_dist_tendsto_zero.mp (curve (p,t) hz)
  have limit : Tendsto (fun z : P × ℝ => dist (Y z.1 c) (Y p c) * Real.exp (K * (b-a))
      + dist (Y p z.2) (Y p t)) (𝓝[D] (p,t)) (𝓝 0) := by
    simpa using (bd.mul_const (Real.exp (K * (b-a)))).add pt
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ limit
  filter_upwards [self_mem_nhdsWithin] with z (hz' : z ∈ D)
  have dt : |z.2 - c| ≤ b-a := abs_le.mpr
    ⟨by linarith [hz'.2.1, hc.2], by linarith [hz'.2.2, hc.1]⟩
  have grow := dist_from_birth lip hc hz'.2 (ode z.1) (ode p) (inside z.1) (inside p)
  exact (dist_triangle _ (Y p z.2) _).trans (add_le_add_left
    (grow.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left dt K.coe_nonneg)) dist_nonneg)) _)

end PlasmaLean.Fields.TrajectoryFamily
