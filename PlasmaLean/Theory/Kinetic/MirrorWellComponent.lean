/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope
public import PlasmaLean.Theory.Kinetic.MirrorArclength
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The connected accessible component between two first mirror points -/

public section
noncomputable section
open Set Filter
open scoped Topology
namespace PlasmaLean.Kinetic.MirrorActionEnvelope

/-- The strict sublevel component containing the launch is exactly the open well.
No behavior of the profile outside its first two level hits is prescribed. -/
theorem LaunchWell.strict_component {f : ℝ → ℝ} {c h l r : ℝ} (w : LaunchWell f c h l r) :
    connectedComponentIn {t | f t < h} c = Ioo l r := by
  have cin : c ∈ Ioo l r := ⟨w.left_lt, w.lt_right⟩
  have member := mem_connectedComponentIn (F := {t | f t < h}) (x := c) (w.accessible c cin)
  have sub := connectedComponentIn_subset {t | f t < h} c
  have inside : Ioo l r ⊆ {t | f t < h} := fun t ht => w.accessible t ht
  apply Subset.antisymm _ (isPreconnected_Ioo.subset_connectedComponentIn cin inside)
  intro t ht
  constructor
  · by_contra! bad
    have seen := isPreconnected_connectedComponentIn.Icc_subset ht member
      (show l ∈ Icc t c from ⟨bad, w.left_lt.le⟩)
    exact (lt_irrefl h) (w.left_hit ▸ sub seen)
  · by_contra! bad
    have seen := isPreconnected_connectedComponentIn.Icc_subset member ht
      (show r ∈ Icc c t from ⟨w.lt_right.le, bad⟩)
    exact (lt_irrefl h) (w.right_hit ▸ sub seen)

/-- Forbidden points arbitrarily near the outward sides make the closed sublevel
component exactly the closed well, even if the field recurs farther out. -/
theorem LaunchWell.closed_component {f : ℝ → ℝ} {c h l r : ℝ} (w : LaunchWell f c h l r)
    (left : ∀ x < l, ∃ t ∈ Icc x l, h < f t) (right : ∀ x > r, ∃ t ∈ Icc r x, h < f t) :
    connectedComponentIn {t | f t ≤ h} c = Icc l r := by
  have cin : c ∈ Ioo l r := ⟨w.left_lt, w.lt_right⟩
  have member := mem_connectedComponentIn (F := {t | f t ≤ h}) (x := c) (w.accessible c cin).le
  have sub := connectedComponentIn_subset {t | f t ≤ h} c
  have inside : Icc l r ⊆ {t | f t ≤ h} := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with eq | lt
    · exact eq ▸ w.left_hit.le
    rcases eq_or_lt_of_le ht.2 with eq | gt
    · exact eq.symm ▸ w.right_hit.le
    exact (w.accessible _ ⟨lt, gt⟩).le
  apply Subset.antisymm _ (isPreconnected_Icc.subset_connectedComponentIn
    (Ioo_subset_Icc_self cin) inside)
  intro t ht
  constructor
  · by_contra! bad
    obtain ⟨q, hq, high⟩ := left t bad
    exact high.not_ge (sub (isPreconnected_connectedComponentIn.Icc_subset ht member
      (show q ∈ Icc t c from ⟨hq.1, hq.2.trans w.left_lt.le⟩)))
  · by_contra! bad
    obtain ⟨q, hq, high⟩ := right t bad
    exact high.not_ge (sub (isPreconnected_connectedComponentIn.Icc_subset member ht
      (show q ∈ Icc c t from ⟨w.lt_right.le.trans hq.1, hq.2⟩)))

/-- A positive derivative gives an over-level point before every larger clock value. -/
theorem outward_barrier {f : ℝ → ℝ} {a x v : ℝ}
    (d : HasDerivAt f v a) (pos : 0 < v) (later : a < x) :
    ∃ q ∈ Ioo a x, f a < f q := by
  have slopes := (d.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)).eventually (lt_mem_nhds pos)
  have small : ∀ᶠ q in 𝓝[>] a, q < x := (gt_mem_nhds later).filter_mono nhdsWithin_le_nhds
  have points : ∀ᶠ q in 𝓝[>] a, q ∈ Ioo a x ∧ f a < f q := by
    filter_upwards [self_mem_nhdsWithin, small, slopes] with q hq hx hs
    change a < q at hq
    rw [slope_def_field] at hs
    exact ⟨⟨hq, hx⟩, sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hq)).mp hs)⟩
  exact points.exists

/-- Transverse outward derivatives isolate the closed component of a launch well. -/
theorem LaunchWell.transverse_component {f : ℝ → ℝ} {c h l r v u : ℝ}
    (w : LaunchWell f c h l r) (dl : HasDerivAt (fun t => f (-t)) u (-l)) (ul : 0 < u)
    (dr : HasDerivAt f v r) (vr : 0 < v) :
    connectedComponentIn {t | f t ≤ h} c = Icc l r := by
  apply w.closed_component
  · intro x hx
    obtain ⟨q, hq, gt⟩ := outward_barrier dl ul (neg_lt_neg hx)
    refine ⟨-q, ⟨by linarith [hq.2], by linarith [hq.1]⟩, ?_⟩
    simpa only [neg_neg, w.left_hit] using gt
  · intro x hx
    obtain ⟨q, hq, gt⟩ := outward_barrier dr vr hx
    exact ⟨q, Ioo_subset_Icc_self hq, w.right_hit ▸ gt⟩

/-- Every point in an oriented physical well is a regular arclength mirror birth,
including when that point is used as a new origin for the geometric clock. -/
theorem LaunchWell.regular_at {B : Fields.Space → Fields.Space} {X : ℝ → Fields.Space}
    {speed : ℝ → ℝ} {c h l r t : ℝ} (w : LaunchWell (fun s => ‖B (X s)‖) c h l r)
    (ht : t ∈ Icc l r) (hc : ContinuousOn speed (Icc l r))
    (line : ∀ s ∈ Icc l r, 0 < speed s ∧ B (X s) ≠ 0 ∧
      HasDerivAt X (speed s • GCLittlejohn.bhat B (X s)) s)
    (dl : deriv (fun s => ‖B (X s)‖) l < 0) (dr : 0 < deriv (fun s => ‖B (X s)‖) r) :
    Contract.RegularMirrorBirth B (X t) h := by
  have shift {z : ℝ} (hz : z ∈ Icc (l - t) (r - t)) : z + t ∈ Icc l r :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have sol := MirrorWell.regularMirrorBirth_of_parametrized_roots
    (B := B) (X := fun z => X (z + t)) (speed := fun z => speed (z + t))
    (l := l - t) (r := r - t) (h := h) (by linarith [w.left_lt, w.lt_right])
    (show (0 : ℝ) ∈ Icc (l - t) (r - t) from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (hc.comp (continuous_id.add continuous_const).continuousOn (fun _ hz => shift hz))
    (fun z hz => ⟨(line _ (shift hz)).1, (line _ (shift hz)).2.1, by
      have clock : HasDerivAt (fun s : ℝ => s + t) 1 z := (hasDerivAt_id z).add_const t
      simpa only [Function.comp_def, one_smul] using ((line _ (shift hz)).2.2.scomp z clock)⟩)
    (by simpa using w.left_hit) (by simpa using w.right_hit)
    (fun z hz => w.accessible _ ⟨by linarith [hz.1], by linarith [hz.2]⟩)
    (by rw [deriv_comp_add_const (fun s => ‖B (X s)‖) t (l - t), sub_add_cancel]; exact dl)
    (by rw [deriv_comp_add_const (fun s => ‖B (X s)‖) t (r - t), sub_add_cancel]; exact dr)
  simpa using sol

/-- A tangential contact can leave the entire closed sublevel connected. -/
theorem tangent_closed_component :
    LaunchWell (fun t : ℝ => -(t ^ 2 - 1) ^ 2) 0 0 (-1) 1 ∧
      connectedComponentIn {t : ℝ | -(t ^ 2 - 1) ^ 2 ≤ 0} 0 = univ := by
  constructor
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t ht
    have : t ^ 2 - 1 < 0 := by nlinarith [mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr ht.1)]
    exact neg_neg_of_pos (sq_pos_of_ne_zero this.ne)
  · have full : {t : ℝ | -(t ^ 2 - 1) ^ 2 ≤ 0} = univ :=
      eq_univ_of_forall fun t => neg_nonpos.mpr (sq_nonneg _)
    rw [full]
    exact isPreconnected_univ.connectedComponentIn (mem_univ _)

end PlasmaLean.Kinetic.MirrorActionEnvelope
