/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.PeriodicLevelGraphs
public import PlasmaLean.Theory.Kinetic.MirrorWellCriterion

/-!
# Winding graphs from the orientation of crossings

A radial profile may fold away from the selected action. A positive radial derivative
at every crossing of that action, together with strict face bounds, still gives a
unique continuous periodic graph. Two such graphs cannot change order without a common
root. Thus one radial comparison at a single phase fixes their order on the whole annulus.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.PeriodicLevelGraphs

open Set Function

/-- A unique root in a compact fibre depends continuously on the launch parameters.
Both the equation and its target may vary with the parameters. -/
theorem exists_continuous_root_of_unique {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace Z] [T2Space Z]
    {F : X × Y → Z} {g : X → Z} (hF : Continuous F) (hg : Continuous g)
    (hroot : ∀ x, ∃! y, F (x, y) = g x) :
    ∃ u : X → Y, Continuous u ∧ ∀ x y, F (x, y) = g x ↔ y = u x := by
  choose u hu using hroot
  have eqn (x : X) (y : Y) : F (x, y) = g x ↔ y = u x :=
    ⟨(hu x).2 y, fun he => he ▸ (hu x).1⟩
  refine ⟨u, continuous_of_isClosed_graph ?_, eqn⟩
  have he : u.graph = {p : X × Y | F p = g p.1} := by
    ext ⟨x, y⟩
    exact eq_comm.trans (eqn x y).symm
  rw [he]
  exact isClosed_eq hF (hg.comp continuous_fst)

/-- At the target the radial derivative is positive. Away from the target it is unrestricted. -/
structure UpwardCrossings (action : ℝ → ℝ → ℝ) (lo hi turn target : ℝ) : Prop where
  ordered : lo < hi
  continuous : ContinuousOn (fun p : ℝ × ℝ => action p.1 p.2) (univ ×ˢ Icc lo hi)
  periodic : ∀ r ∈ Icc lo hi, Periodic (fun s => action s r) turn
  left_lt : ∀ s, action s lo < target
  lt_right : ∀ s, target < action s hi
  upward : ∀ s r, r ∈ Ioo lo hi → action s r = target → 0 < deriv (action s) r

variable {J L H : ℝ → ℝ → ℝ} {lo hi turn target : ℝ}

/-- The level is one simple winding graph. The action is below the target everywhere
to its left on the strip, and above the target everywhere to its right. -/
theorem UpwardCrossings.exists_level_graph (h : UpwardCrossings J lo hi turn target) :
    ∃ u : ℝ → ℝ, Continuous u ∧ Periodic u turn ∧ ∀ s,
      u s ∈ Ioo lo hi ∧ J s (u s) = target ∧ 0 < deriv (J s) (u s) ∧
      (∀ r ∈ Ico lo (u s), J s r < target) ∧ (∀ r ∈ Ioc (u s) hi, target < J s r) := by
  have crossing (s : ℝ) := Kinetic.MirrorWell.upward_crossing h.ordered
    (h.continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (show MapsTo (fun r => (s, r)) (Icc lo hi) (univ ×ˢ Icc lo hi) from
        fun _ hr => ⟨trivial, hr⟩)) (h.left_lt s) (h.lt_right s) (fun r hr he =>
      h.upward s r ⟨hr.1.lt_of_ne (fun e => (h.left_lt s).ne (e ▸ he)),
        hr.2.lt_of_ne (fun e => (h.lt_right s).ne (e ▸ he.symm))⟩ he)
  choose v hv ev dv before after using crossing
  have unique (s r : ℝ) (hr : r ∈ Icc lo hi) (he : J s r = target) : r = v s := by
    rcases lt_trichotomy r (v s) with hl | heq | hh
    · exact False.elim ((before s r ⟨hr.1, hl⟩).ne he)
    · exact heq
    · exact False.elim ((after s r ⟨hh, hr.2⟩).ne he.symm)
  have hc : Continuous (fun p : ℝ × Icc lo hi => J p.1 p.2) :=
    h.continuous.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨trivial, p.2.2⟩)
  obtain ⟨u, cu, hu⟩ := exists_continuous_root_of_unique hc (continuous_const (y := target))
    fun s => ⟨⟨v s, Ioo_subset_Icc_self (hv s)⟩, ev s, fun r he => Subtype.ext (unique s r r.2 he)⟩
  have ident : (fun s => (u s : ℝ)) = v := by
    funext s
    exact unique s (u s) (u s).2 ((hu s (u s)).mpr rfl)
  refine ⟨v, ident ▸ continuous_subtype_val.comp cu, ?_,
    fun s => ⟨hv s, ev s, dv s, before s, after s⟩⟩
  intro s
  have hr := Ioo_subset_Icc_self (hv (s + turn))
  exact unique s _ hr ((h.periodic _ hr s).symm.trans (ev _))

/-- Disjoint continuous periodic graphs are uniformly ordered in the direction witnessed
at any one phase. The witness `δ` is independent of phase. -/
theorem uniform_separation_of_disjoint {u v : ℝ → ℝ} (cu : Continuous u) (cv : Continuous v)
    (pu : Periodic u turn) (pv : Periodic v turn) (ht : turn ≠ 0)
    (disjoint : ∀ s, u s ≠ v s) {s₀ : ℝ} (anchor : u s₀ < v s₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s, δ ≤ v s - u s := by
  have lt (s : ℝ) : u s < v s := by
    by_contra! h
    obtain ⟨t, he⟩ := intermediate_value_univ₂ cu cv anchor.le h
    exact disjoint t he
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ := ((pv.sub pu).compact_of_continuous ht (cv.sub cu)).exists_isMinOn
    (range_nonempty _) continuousOn_id
  exact ⟨_, sub_pos.mpr (lt s), fun t => hmin (mem_range_self t)⟩

/-- Two levels bracketed on the faces give uniformly separated winding graphs if their
root sets are disjoint. One witness between the graphs at one phase determines the order. -/
theorem separated_graphs_of_upward_crossings (hL : UpwardCrossings L lo hi turn target)
    (hH : UpwardCrossings H lo hi turn target) (ht : turn ≠ 0)
    (no_common_root : ∀ s r, r ∈ Ioo lo hi → H s r = target → L s r ≠ target)
    {s₀ r₀ : ℝ} (hr₀ : r₀ ∈ Icc lo hi) (anchorL : L s₀ r₀ < target)
    (anchorH : target < H s₀ r₀) :
    ∃ u v : ℝ → ℝ, Continuous u ∧ Periodic u turn ∧ Continuous v ∧ Periodic v turn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ s, u s ∈ Ioo lo hi ∧ v s ∈ Ioo lo hi ∧
        H s (u s) = target ∧ L s (v s) = target ∧ δ ≤ v s - u s := by
  obtain ⟨u, cu, pu, hu⟩ := hH.exists_level_graph
  obtain ⟨v, cv, pv, hv⟩ := hL.exists_level_graph
  have disjoint (s : ℝ) (he : u s = v s) : False :=
    no_common_root s _ (hu s).1 (hu s).2.1 (he ▸ (hv s).2.1)
  have hleft : u s₀ < r₀ := by
    rcases lt_trichotomy (u s₀) r₀ with h | he | h
    · exact h
    · exact False.elim (anchorH.ne (he ▸ (hu s₀).2.1.symm))
    · exact False.elim (anchorH.not_gt ((hu s₀).2.2.2.1 r₀ ⟨hr₀.1, h⟩))
  have hright : r₀ < v s₀ := by
    rcases lt_trichotomy r₀ (v s₀) with h | he | h
    · exact h
    · exact False.elim (anchorL.ne (he ▸ (hv s₀).2.1))
    · exact False.elim (anchorL.not_gt ((hv s₀).2.2.2.2 r₀ ⟨h, hr₀.2⟩))
  obtain ⟨δ, hδ, gap⟩ := uniform_separation_of_disjoint cu cv pu pv ht disjoint (hleft.trans hright)
  exact ⟨u, v, cu, pu, cv, pv, δ, hδ, fun s =>
    ⟨(hu s).1, (hv s).1, (hu s).2.1, (hv s).2.1, gap s⟩⟩

/-- A zero-width radial interval cannot bracket a level. -/
theorem no_degenerate_upward_crossings : ¬ UpwardCrossings J lo lo turn target :=
  fun h => h.ordered.false

/-- The folded profile `r(2-r)` passes the crossing test on a strip extending past its
maximum at one, where it fails the older whole-strip monotonicity condition. -/
theorem folded_profile (turn : ℝ) :
    UpwardCrossings (fun _ r => r * (2 - r)) (-1) (3/2) turn 0 ∧
      ¬ StrictMonoOn (fun r : ℝ => r * (2 - r)) (Icc (-1) (3/2)) := by
  constructor
  · refine ⟨by norm_num, by fun_prop, fun _ _ _ => rfl, fun _ => by norm_num,
      fun _ => by norm_num, ?_⟩
    intro _ r hr he
    have hr0 : r = 0 := (mul_eq_zero.mp he).resolve_right (by linarith [hr.2])
    subst r
    have hd := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) 2).sub (hasDerivAt_id 0))
    change HasDerivAt (fun r : ℝ => r * (2 - r)) (1 * (2 - 0) + 0 * (0 - 1)) 0 at hd
    norm_num at hd
    rw [hd.deriv]
    norm_num
  · intro hm
    have he := hm (a := 1) (b := 3/2) (by norm_num) (by norm_num) (by norm_num)
    norm_num at he

end PlasmaLean.PeriodicLevelGraphs
