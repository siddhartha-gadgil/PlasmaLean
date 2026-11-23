/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith

/-!
# Winding graphs of fixed action on a periodic launch strip

At each of two mirror heights, the transverse action must be continuous, strictly increasing
across the strip, and bracket the same target at its edges for every launch angle. Ordering the
two actions in the interior yields separated winding graphs. Application to guiding centres
requires separate evidence that both actions refer to regular mirror wells on the entire strip.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.PeriodicLevelGraphs

open Set Function

/-- Bracketing and transverse monotonicity of a single-valued action on a periodic strip. -/
structure Bracketed (action : ℝ → ℝ → ℝ) (lo hi turn target : ℝ) : Prop where
  ordered : lo ≤ hi
  continuous : ContinuousOn (fun p : ℝ × ℝ => action p.1 p.2) (univ ×ˢ Icc lo hi)
  periodic : ∀ r ∈ Icc lo hi, Periodic (fun s => action s r) turn
  monotone : ∀ s, StrictMonoOn (action s) (Icc lo hi)
  left_lt : ∀ s, action s lo < target
  lt_right : ∀ s, target < action s hi

variable {J L H : ℝ → ℝ → ℝ} {lo hi turn target : ℝ}

/-- A single-valued transverse action crossing gives one continuous winding graph. -/
theorem Bracketed.exists_level_graph (h : Bracketed J lo hi turn target) :
    ∃ u : ℝ → ℝ, Continuous u ∧ Periodic u turn ∧ ∀ s,
      u s ∈ Ioo lo hi ∧ J s (u s) = target ∧ ∀ r ∈ Icc lo hi, J s r = target → r = u s := by
  have existsRoot (s : ℝ) : ∃ r : Icc lo hi, J s r = target := by
    have hc : ContinuousOn (J s) (Icc lo hi) := h.continuous.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hr => ⟨trivial, hr⟩)
    obtain ⟨r, hr, he⟩ := intermediate_value_Icc h.ordered hc
      ⟨(h.left_lt s).le, (h.lt_right s).le⟩
    exact ⟨⟨r, hr⟩, he⟩
  choose u hu using existsRoot
  have unique (s : ℝ) {r : ℝ} (hr : r ∈ Icc lo hi) (he : J s r = target) : r = u s :=
    (h.monotone s).injOn hr (u s).2 (he.trans (hu s).symm)
  have hc : Continuous (fun p : ℝ × Icc lo hi => J p.1 p.2) := h.continuous.comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    (fun p => ⟨trivial, p.2.2⟩)
  have cont : Continuous u := by
    apply continuous_of_isClosed_graph
    have hg : u.graph = {p : ℝ × Icc lo hi | J p.1 p.2 = target} := by
      ext ⟨s, r⟩
      change (u s = r) ↔ _
      constructor
      · rintro rfl
        exact hu s
      · exact fun he => Subtype.ext (unique s r.2 he).symm
    rw [hg]
    exact isClosed_eq hc continuous_const
  refine ⟨(fun s => (u s : ℝ)), continuous_subtype_val.comp cont, ?_, ?_⟩
  · intro s
    apply unique s (u (s + turn)).2
    exact (h.periodic _ (u (s + turn)).2 s).symm.trans (hu _)
  · intro s
    have hl : lo ≠ (u s : ℝ) := by
      intro e
      exact (h.left_lt s).ne (e ▸ hu s)
    have hr : (u s : ℝ) ≠ hi := by
      intro e
      exact (h.lt_right s).ne ((e ▸ hu s).symm)
    exact ⟨⟨lt_of_le_of_ne (u s).2.1 hl, lt_of_le_of_ne (u s).2.2 hr⟩, hu s, fun _ => unique s⟩

/-- A uniform lower bound on the true transverse action derivative converts an action
residual into a radius error. A secant bound just at grid points does not imply the hypothesis. -/
theorem radius_error_of_action_residual {F : ℝ → ℝ} {u r e m : ℝ}
    (hc : ContinuousOn F (Icc lo hi)) (hm : 0 < m)
    (hder : ∀ x ∈ Ioo lo hi, m ≤ deriv F x)
    (hu : u ∈ Icc lo hi) (hr : r ∈ Icc lo hi) (root : F u = target)
    (residual : |F r - target| ≤ e) : |r - u| ≤ e / m := by
  have hd (x : ℝ) (hx : x ∈ interior (Icc lo hi)) : m ≤ deriv F x := by
    exact hder x (by simpa using hx)
  have df : DifferentiableOn ℝ F (interior (Icc lo hi)) := fun x hx =>
    (differentiableAt_of_deriv_ne_zero (hm.trans_le (hd x hx)).ne').differentiableWithinAt
  have grow := (convex_Icc lo hi).mul_sub_le_image_sub_of_le_deriv hc df hd
  apply (le_div_iff₀ hm).mpr
  rcases le_total u r with hus | hrs
  · rw [abs_of_nonneg (sub_nonneg.mpr hus), mul_comm]
    exact (grow u hu r hr hus).trans (by simpa [root] using (abs_le.mp residual).2)
  · rw [abs_of_nonpos (sub_nonpos.mpr hrs), neg_sub, mul_comm]
    exact (grow r hr u hu hrs).trans (by linarith [(abs_le.mp residual).1])

/-- On one action level, the root at the higher mirror height has smaller launch radius.
Periodicity and compactness give a positive lower bound on the separation over all angles. -/
theorem separated_level_graphs (hL : Bracketed L lo hi turn target)
    (hH : Bracketed H lo hi turn target) (hT : turn ≠ 0)
    (order : ∀ s r, r ∈ Ioo lo hi → L s r < H s r) :
    ∃ u v : ℝ → ℝ, Continuous u ∧ Periodic u turn ∧ Continuous v ∧ Periodic v turn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ s, u s ∈ Ioo lo hi ∧ v s ∈ Ioo lo hi ∧
        H s (u s) = target ∧ L s (v s) = target ∧ δ ≤ v s - u s := by
  obtain ⟨u, cu, pu, hu⟩ := hH.exists_level_graph
  obtain ⟨v, cv, pv, hv⟩ := hL.exists_level_graph
  have lt (s : ℝ) : u s < v s := by
    by_contra! hh
    have hle := (hL.monotone s).monotoneOn (Ioo_subset_Icc_self (hv s).1)
      (Ioo_subset_Icc_self (hu s).1) hh
    linarith [(hu s).2.1, (hv s).2.1, order s _ (hu s).1]
  have compact := (pv.sub pu).compact_of_continuous hT (cv.sub cu)
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ := compact.exists_isMinOn (range_nonempty _) continuousOn_id
  exact ⟨u, v, cu, pu, cv, pv, _, sub_pos.mpr (lt s), fun t =>
    ⟨(hu t).1, (hv t).1, (hu t).2.1, (hv t).2.1, hmin (mem_range_self t)⟩⟩

end PlasmaLean.PeriodicLevelGraphs
