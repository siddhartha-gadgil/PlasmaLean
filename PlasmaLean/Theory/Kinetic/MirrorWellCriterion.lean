/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.TrappedBirthBand
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Turning points from oriented crossings

Only the sign of the derivative at the specified mirror height is needed. The field
strength may oscillate above or below that height. The field-line corollary uses arclength.
-/

@[expose] public section
noncomputable section

open Set Filter Topology

namespace PlasmaLean.Kinetic.MirrorWell

/-- Once a continuous profile reaches a height at which every crossing has positive
derivative, it stays strictly above that height to the right. -/
private theorem above_to_right {f : ℝ → ℝ} {a b h : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : h ≤ f a)
    (hpos : ∀ x ∈ Icc a b, f x = h → 0 < deriv f x) : h < f b := by
  have closed : IsClosed ((f ⁻¹' Ici h) ∩ Icc a b) := by
    rw [inter_comm]
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have invariant : Icc a b ⊆ f ⁻¹' Ici h := by
    apply closed.Icc_subset_of_forall_mem_nhdsWithin ha
    rintro x ⟨hx, hxint⟩
    change h ≤ f x at hx
    have hxc : x ∈ Icc a b := Ico_subset_Icc_self hxint
    rcases hx.lt_or_eq with hlt | heq
    · have hm : Icc a b ∈ 𝓝[>] x :=
        mem_of_superset (Ioc_mem_nhdsGT hxint.2) (fun y hy => ⟨hxint.1.trans hy.1.le, hy.2⟩)
      have H := ((hf x hxc).mono_left (nhdsWithin_le_iff.mpr hm)).eventually
        (eventually_gt_nhds hlt)
      exact H.mono fun y hy => hy.le
    · have hd := hpos x hxc heq.symm
      have hr := (hasDerivAt_iff_tendsto_slope_left_right.mp
        (differentiableAt_of_deriv_ne_zero hd.ne').hasDerivAt).2.eventually (eventually_gt_nhds hd)
      filter_upwards [hr, self_mem_nhdsWithin] with y hy (hxy : x < y)
      exact hx.trans ((slope_pos_iff_of_le hxy.le).mp hy).le
  have hb := invariant (right_mem_Icc.mpr hab.le)
  change h ≤ f b at hb
  refine hb.lt_of_ne ?_
  intro heq
  have hd := hpos b (right_mem_Icc.mpr hab.le) heq.symm
  have hl := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (differentiableAt_of_deriv_ne_zero hd.ne').hasDerivAt).1.eventually (eventually_gt_nhds hd)
  have near : ∀ᶠ y in 𝓝[<] b, y ∈ Ioo a b := Ioo_mem_nhdsLT hab
  obtain ⟨y, hy, hySlope⟩ := (near.and hl).exists
  rw [slope_comm] at hySlope
  have := (slope_pos_iff_of_le hy.2.le).mp hySlope
  exact this.not_ge (heq ▸ invariant (Ioo_subset_Icc_self hy))

/-- An upward derivative at every occurrence of a bracketed height yields one simple root.
The profile is strictly below the height before that root and strictly above it afterwards. -/
theorem upward_crossing {f : ℝ → ℝ} {a b h : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < h) (hb : h < f b)
    (hpos : ∀ x ∈ Icc a b, f x = h → 0 < deriv f x) :
    ∃ r ∈ Ioo a b, f r = h ∧ 0 < deriv f r ∧
      (∀ x ∈ Ico a r, f x < h) ∧ (∀ x ∈ Ioc r b, h < f x) := by
  obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo hab.le hf (show h ∈ Ioo _ _ from ⟨ha, hb⟩)
  refine ⟨r, hr, heq, hpos r (Ioo_subset_Icc_self hr) heq, ?_, ?_⟩
  · intro x hx
    by_contra! hh
    have hs := Icc_subset_Icc hx.1 hr.2.le
    exact (above_to_right hx.2 (hf.mono hs) hh (fun y hy => hpos y (hs hy))).ne heq.symm
  · intro x hx
    have hs := Icc_subset_Icc hr.1.le hx.2
    exact above_to_right hx.1 (hf.mono hs) heq.ge (fun y hy => hpos y (hs hy))

/-- Two oriented crossings enclose the allowed component containing the launch point.
Within the tested interval, they are the only points at the mirror height. -/
theorem two_simple_mirrors {f : ℝ → ℝ} {a c b h : ℝ} (hac : a < c) (hcb : c < b)
    (hf : ContinuousOn f (Icc a b)) (ha : h < f a) (hc : f c < h) (hb : h < f b)
    (hneg : ∀ x ∈ Icc a c, f x = h → deriv f x < 0)
    (hpos : ∀ x ∈ Icc c b, f x = h → 0 < deriv f x) :
    ∃ l ∈ Ioo a c, ∃ r ∈ Ioo c b, f l = h ∧ f r = h ∧
      deriv f l < 0 ∧ 0 < deriv f r ∧ (∀ x ∈ Ioo l r, f x < h) ∧
      (∀ x ∈ Icc a b, f x = h ↔ x = l ∨ x = r) := by
  obtain ⟨l, hl, el, _, leftFar, leftNear⟩ :=
    upward_crossing (f := -f) hac (hf.mono (Icc_subset_Icc_right hcb.le)).neg
      (neg_lt_neg ha) (neg_lt_neg hc) fun x hx ex => by
        rw [deriv.neg]
        exact neg_pos.mpr (hneg x hx (neg_inj.mp ex))
  obtain ⟨r, hr, er, dr, rightNear, rightFar⟩ :=
    upward_crossing hcb (hf.mono (Icc_subset_Icc_left hac.le)) hc hb hpos
  have el' : f l = h := neg_inj.mp el
  have interior (x : ℝ) (hx : x ∈ Ioo l r) : f x < h := by
    rcases le_or_gt x c with h | h
    · exact neg_lt_neg_iff.mp (leftNear x ⟨hx.1, h⟩)
    · exact rightNear x ⟨h.le, hx.2⟩
  refine ⟨l, hl, r, hr, el', er, hneg l (Ioo_subset_Icc_self hl) el', dr, interior, ?_⟩
  intro x hx
  constructor
  · intro he
    by_contra! hn
    rcases lt_or_gt_of_ne hn.1 with h | h
    · exact (neg_lt_neg_iff.mp (leftFar x ⟨hx.1, h⟩)).ne he.symm
    · rcases lt_or_gt_of_ne hn.2 with hh | hh
      · exact (interior x ⟨h, hh⟩).ne he
      · exact (rightFar x ⟨hh, hx.2⟩).ne he.symm
  · rintro (rfl | rfl) <;> assumption

open PlasmaLean.Fields PlasmaLean.Kinetic.GCLittlejohn

/-- On an oriented arclength field line, the turning-point sign test establishes the
regular-mirror-birth condition for the launch at parameter zero. -/
theorem regularMirrorBirth_of_crossings {B : Space → Space} {line : ℝ → Space} {a b h : ℝ}
    (ha : a < 0) (hb : 0 < b)
    (fieldLine : ∀ t ∈ Icc a b, B (line t) ≠ 0 ∧ HasDerivAt line (bhat B (line t)) t)
    (hf : ContinuousOn (fun t => ‖B (line t)‖) (Icc a b))
    (hl : h < ‖B (line a)‖) (hc : ‖B (line 0)‖ < h) (hr : h < ‖B (line b)‖)
    (hneg : ∀ t ∈ Icc a 0, ‖B (line t)‖ = h → deriv (fun x => ‖B (line x)‖) t < 0)
    (hpos : ∀ t ∈ Icc 0 b, ‖B (line t)‖ = h → 0 < deriv (fun x => ‖B (line x)‖) t) :
    PlasmaLean.Contract.RegularMirrorBirth B (line 0) h := by
  obtain ⟨l, hleft, r, hright, el, er, dl, dr, allowed, _⟩ :=
    two_simple_mirrors ha hb hf hl hc hr hneg hpos
  exact ⟨line, l, r, hleft.2.trans hright.1, ⟨hleft.2.le, hright.1.le⟩, rfl,
    fun t ht => fieldLine t (Icc_subset_Icc hleft.1.le hright.2.le ht),
    el, er, allowed, dl, dr⟩

/-- A derivative enclosure on a closed height window proves regular mirror births at every
height in that window on the same arclength field line. -/
theorem regularMirrorBirth_on_height_window {B : Space → Space} {line : ℝ → Space}
    {a b low high : ℝ} (ha : a < 0) (hb : 0 < b)
    (fieldLine : ∀ t ∈ Icc a b, B (line t) ≠ 0 ∧ HasDerivAt line (bhat B (line t)) t)
    (hf : ContinuousOn (fun t => ‖B (line t)‖) (Icc a b))
    (hl : high < ‖B (line a)‖) (hc : ‖B (line 0)‖ < low) (hr : high < ‖B (line b)‖)
    (hneg : ∀ t ∈ Icc a 0, ‖B (line t)‖ ∈ Icc low high →
      deriv (fun x => ‖B (line x)‖) t < 0)
    (hpos : ∀ t ∈ Icc 0 b, ‖B (line t)‖ ∈ Icc low high →
      0 < deriv (fun x => ‖B (line x)‖) t) :
    ∀ h ∈ Icc low high, PlasmaLean.Contract.RegularMirrorBirth B (line 0) h := by
  intro h hh
  exact regularMirrorBirth_of_crossings ha hb fieldLine hf
    (hh.2.trans_lt hl) (hc.trans_le hh.1) (hh.2.trans_lt hr)
    (fun t ht e => hneg t ht (e ▸ hh)) (fun t ht e => hpos t ht (e ▸ hh))

end PlasmaLean.Kinetic.MirrorWell
