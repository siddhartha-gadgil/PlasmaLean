/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialMirrorHeightBand
public import PlasmaLean.Design.DommaschkSectorActionBand
public import PlasmaLean.Theory.Kinetic.MirrorActionTransverse

/-! # Height derivatives and first-well actions on the launch sector -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSectorHeightAction

open Set MeasureTheory Certificates.PositionFrameSlabs
open DommaschkRadialMirrorHeightBand DommaschkRadialFamilyContinuity DommaschkRibbonFirstMirrors
open DommaschkNativeWellAction DommaschkSectorActionBand DommaschkRadialSectionAction
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction Kinetic.MirrorActionFlight

abbrev delta : ℝ := 1 / 10000000
abbrev lowTarget : ℝ := target - 11 / 10000
abbrev highTarget : ℝ := target + 9 / 10000
abbrev reference : Heights := ⟨level,by norm_num [level,lower,upper]⟩
def clipped (y : ℝ → Plane) := action (field y) (density y) (-cap) cap

/-- The derivative is the physical one-way time between precisely these first mirrors.
All derivatives are ambient height derivatives, including at the ends of the band. -/
structure AtHeight (y : ℝ → Plane) (h : Heights) (l r : ℝ) : Prop where
  well : ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → LaunchWell (field y) φ h l r
  left : deriv (field y) l < 0
  right : 0 < deriv (field y) r
  mass : clipped y h = action (field y) (density y) l r h
  derivative : HasDerivAt (clipped y) (oneWayBounceTime (density y) (field y) h l r) (h : ℝ)
  time : 14 < oneWayBounceTime (density y) (field y) h l r ∧
    oneWayBounceTime (density y) (field y) h l r < 10000
  signs : field y 0 < h ∧ h < field y (-cap) ∧ h < field y cap

theorem at_height {y : ℝ → Plane} (e : Enclosed y (-cap) cap) (good : Verified y) (h : Heights) :
    ∃ l r, AtHeight y h l r := by
  obtain ⟨p,m,_,each⟩ := good
  obtain ⟨w,dl,dr,fin,low,high⟩ := each h
  have well := w 0 (by norm_num)
  have pos : 0 < derivativeFloor / (2 * (h : ℝ)) := div_pos (by norm_num [derivativeFloor])
    (mul_pos (by norm_num) ((by norm_num [lower,level] : 0 < lower).trans_le h.2.1))
  have sl := dl.trans (neg_neg_of_pos pos)
  have sr := pos.trans dr
  have mp := m.interior_time h
  have pp := p.interior_time h
  have al : -cap ≤ -m.time h := neg_le_neg mp.2.le
  have rb : p.time h ≤ cap := pp.2.le
  have left (t : ℝ) (ht : t ∈ Ico (-cap) (-m.time h)) : (h : ℝ) < field y t := by
    simpa only [neg_neg] using m.after h (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have right (t : ℝ) (ht : t ∈ Ioc (p.time h) cap) : (h : ℝ) < field y t := p.after h t ht
  have extL (t : ℝ) (ht : t ∈ Icc (-cap) (-m.time h)) : (h : ℝ) ≤ field y t :=
    ht.2.eq_or_lt.elim (fun eq => eq.symm ▸ well.left_hit.ge) (fun lt => (left t ⟨ht.1,lt⟩).le)
  have extR (t : ℝ) (ht : t ∈ Icc (p.time h) cap) : (h : ℝ) ≤ field y t :=
    ht.1.eq_or_lt.elim (fun eq => eq ▸ well.right_hit.ge) (fun lt => (right t ⟨lt,ht.2⟩).le)
  have cy : ContinuousOn y (Icc (-cap) cap) :=
    fun t ht => (e.ode t ht).continuousAt.continuousWithinAt
  have cw : ContinuousOn (density y) (Icc (-cap) cap) :=
    (DommaschkSignedTraceDensity.continuousOn_density_region cy e.region).congr
      (fun t ht => cartesian_weight e ht)
  have cf := signed_window e
  have lr := well.left_lt.le.trans well.lt_right.le
  have integrable : IntervalIntegrable (fun t => density y t / Real.sqrt (2 * ((h : ℝ)-field y t)))
      volume (-m.time h) (p.time h) := by
    apply fin.congr
    intro t ht
    rw [uIoc_of_le lr] at ht
    dsimp only
    rw [cartesian_weight e (Icc_subset_Icc al rb (Ioc_subset_Icc_self ht))]
  have d := hasDerivAt_two_mirrors al rb well cf cw left right
    (differentiableAt_of_deriv_ne_zero sl.ne).hasDerivAt sl.ne
    (differentiableAt_of_deriv_ne_zero sr.ne').hasDerivAt sr.ne'
  rw [time_eq_between al rb integrable extL extR] at d
  exact ⟨-m.time h,p.time h,w,sl,sr,action_eq_between al lr rb cf cw extL extR,d,
    ⟨low,high⟩,well.accessible 0 ⟨well.left_lt,well.lt_right⟩,
    left _ ⟨le_rfl,neg_lt_neg mp.2⟩,right _ ⟨pp.2,le_rfl⟩⟩

/-- The physical time bound controls action variation on the entire certified height interval. -/
theorem lipschitz {y : ℝ → Plane} (e : Enclosed y (-cap) cap) (good : Verified y) (h j : Heights) :
    |clipped y h - clipped y j| ≤ 10000 * |(h : ℝ) - j| := by
  have d (x : ℝ) (hx : x ∈ Icc lower upper) :
      DifferentiableAt ℝ (clipped y) x ∧ ‖deriv (clipped y) x‖ ≤ 10000 := by
    obtain ⟨l,r,facts⟩ := at_height e good ⟨x,hx⟩
    refine ⟨facts.derivative.differentiableAt,?_⟩
    rw [facts.derivative.deriv,Real.norm_eq_abs,abs_of_pos (by linarith [facts.time.1])]
    exact facts.time.2.le
  exact (convex_Icc lower upper).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (d x hx).1) (fun x hx => (d x hx).2) j.2 h.2

theorem in_band {h : ℝ} (hh : |h - level| ≤ delta) : h ∈ Icc lower upper := by
  obtain ⟨lo,hi⟩ := abs_le.mp hh
  unfold lower upper
  norm_num [delta] at lo hi
  constructor <;> linarith

end PlasmaLean.Design.DommaschkSectorHeightAction
