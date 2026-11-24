/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPairedFirstWellAction
public import PlasmaLean.Theory.Kinetic.MirrorActionAffineGain
public import PlasmaLean.Design.DommaschkPilotArcLength

/-! # Equal-height action separation on the whole closed QA2R height band -/

@[expose] public section
noncomputable section
set_option linter.style.longLine false
namespace PlasmaLean.Design.DommaschkClosedBandAction
open Set MeasureTheory Certificates.PositionFrameSlabs DommaschkPairedActionProfiles
open DommaschkMirrorLaunch
open DommaschkMirrorBandFlightIdentity (profile bound)
open DommaschkMirrorBandAction (Heights)
open DommaschkLowerActionPath (Signed density)
open Kinetic.MirrorHeightBand Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open DommaschkFirstMirrorLaunchSign (height)

/-- A one-way action integrated with respect to physical Cartesian arclength. -/
def J (y : ℝ → Plane) (l r h : ℝ) : ℝ := action (profile y) (DommaschkNativeWellAction.density y) l r h

def Separated (y z : ℝ → Plane) : Prop :=
  ∀ h ∈ Heights, ∃ l ∈ Ioo (-(325 / 64):ℝ) (-(316 / 64)), ∃ r ∈ Ioo (316 / 64:ℝ) (325 / 64),
    ∃ L ∈ Ioo (-327 / 64:ℝ) (-317 / 64), ∃ R ∈ Ioo (317 / 64:ℝ) (327 / 64),
      LaunchWell (profile y) 0 h l r ∧ LaunchWell (profile z) 0 h L R ∧ L ≤ l ∧ r ≤ R ∧
      2 / 625 < J z L R h - J y l r h ∧ 2 / 5 < (J z L R h - J y l r h) / (239 / 500 - 47 / 100)

private theorem action_eq {y : ℝ → Plane} {l r h : ℝ} (lr : l ≤ r)
    (eq : ∀ t ∈ Icc l r, DommaschkNativeWellAction.density y t = density y t) :
    J y l r h = action (profile y) (density y) l r h := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le lr] at ht
  exact congrArg (fun v => v * _) (eq t ht)

/-- The two original traces, the pilot's integral arclength and the pointwise field
comparison suffice. Both mirror pairs are selected at the very same height. -/
theorem on_paths {φ : ℝ} {y z : ℝ → Plane} {entryI entryO : State}
    {fi bi fo bo : List Step} {Ti To : ℝ}
    (pilot : Signed entryI fi bi Ti y) (outer : Signed entryO fo bo To z)
    (roomI : bound < Ti) (roomO : 327 / 64 < To)
    (regI : ∀ t ∈ Icc (-bound) bound, DommaschkSignedTraceDomain.Region (y t))
    (regO : ∀ t ∈ Icc (-(327 / 64) : ℝ) (327 / 64), DommaschkSignedTraceDomain.Region (z t))
    (times : DommaschkActionFlightFloor.TimeBounds φ y)
    (length : (9309 / 1000 : ℝ) ≤ ∫ t in (-(316 / 64) : ℝ)..(316 / 64), density y t)
    (full : ∀ t ∈ Icc (-bound) bound, Compared t (y t) (z t))
    (fwd : Branch (profile z) (317 / 64) (327 / 64) (height false) (height true) (1 / 400))
    (back : Branch (fun t => profile z (-t)) (317 / 64) (327 / 64) (height false) (height true) (1 / 400)) :
    Separated y z := by
  intro h hh
  obtain ⟨l, hl, r, hr, _, wi, cap, _⟩ := times h hh
  let H : Heights := ⟨h, hh⟩
  let R := fwd.time H
  let L := back.time H
  have hR : R ∈ Ioo (317 / 64:ℝ) (327 / 64) := fwd.interior_time H
  have hL : L ∈ Ioo (317 / 64:ℝ) (327 / 64) := back.interior_time H
  have wo : LaunchWell (profile z) 0 h (-L) R := by
    refine ⟨by linarith [hL.1],by linarith [hR.1],back.hit H, fwd.hit H,?_⟩
    intro t ht
    rcases le_total 0 t with p | n
    · exact fwd.before H t ⟨p, ht.2⟩
    · simpa only [neg_neg] using back.before H (-t) ⟨by linarith, by linarith [ht.1]⟩
  have innerSub : Icc l r ⊆ Icc (-bound) bound := Icc_subset_Icc hl.1.le hr.2.le
  have outerSub : Icc (-L) R ⊆ Icc (-(327 / 64):ℝ) (327 / 64) :=
    Icc_subset_Icc (neg_le_neg hL.2.le) hR.2.le
  obtain ⟨cf, cw, eq⟩ := pilot.inputs (fun t ht => Icc_subset_Ioo (neg_lt_neg roomI) roomI (innerSub ht))
    (fun t ht => regI t (innerSub ht))
  obtain ⟨gf, gv, ge⟩ := outer.inputs (fun t ht => Icc_subset_Ioo (neg_lt_neg roomO) roomO (outerSub ht))
    (fun t ht => regO t (outerSub ht))
  have wn (t) (ht : t ∈ Icc l r) : 0 ≤ density y t := by rw [← eq t ht]; exact norm_nonneg _
  have vn (t) (ht : t ∈ Icc (-L) R) : 0 ≤ density z t := by rw [← ge t ht]; exact norm_nonneg _
  have moved := intervalIntegral.integral_mono_interval (μ := volume) hl.2.le (by norm_num : -(316 / 64:ℝ) ≤ 316 / 64) hr.1.le
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => wn t (Ioc_subset_Icc_self ht)))
    (cw.intervalIntegrable_of_Icc (wi.left_lt.trans wi.lt_right).le)
  let a : ℝ := 99739881 / 100000000
  let b : ℝ := 759795 / 1000000000
  have base : LaunchWell (profile y) 0 h l r := wi
  obtain ⟨left, right, gain⟩ := base.affine_gain wo (d := 1 / 9000) (k := 3999 / 4000)
    (a := a) (b := b) (by norm_num) (by norm_num) (by norm_num [a, b])
    cf cw gf gv wn vn (fun t ht => by
      have c := full t (innerSub (Ioo_subset_Icc_self ht))
      exact ⟨c.2.2.2, by linarith only [c.2.2.1]⟩)
  have mass : action (profile y) (density y) l r h ≤ DommaschkActionArchiveMass.mass := cap
  have len := length.trans moved
  have physicalI := action_eq (h := h) (wi.left_lt.trans wi.lt_right).le eq
  have physicalO := action_eq (h := h) (wo.left_lt.trans wo.lt_right).le ge
  have diff : 2 / 625 < J z (-L) R h - J y l r h := by
    rw [physicalI, physicalO]
    norm_num [a, b, DommaschkActionArchiveMass.mass] at gain mass
    linarith only [gain, mass, len]
  refine ⟨l, hl, r, hr,-L,⟨by linarith [hL.2],by linarith [hL.1]⟩,R, hR, wi, wo, left, right, diff,?_⟩
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 239 / 500 - 47 / 100)]
  exact lt_of_eq_of_lt (by norm_num) diff

end PlasmaLean.Design.DommaschkClosedBandAction
