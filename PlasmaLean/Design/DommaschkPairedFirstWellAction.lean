/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkComparedTracePrefixes
public import PlasmaLean.Design.DommaschkLowerActionPath

/-! # Comparing the physical Cartesian actions of two first wells -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPairedFirstWellAction
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkPairedActionProfiles
open DommaschkEndpointTraceFamily DommaschkComparedTracePrefixes DommaschkLowerActionPath
open DommaschkMirrorBandAction (Heights)
open DommaschkMirrorBandFlightIdentity (profile bound)
open Kinetic.MirrorHeightBand Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open DommaschkFirstMirrorLaunchSign (height)

/-- The inequalities at each height refer to the same field lines, whose original
birth angles and cylindrical positions can be kept by the caller. -/
def Gains (y z : ℝ → Plane) : Prop :=
  ∀ h ∈ Heights, h + 1 / 18000 ∈ Heights →
    ∃ l r L R, LaunchWell (profile y) 0 (h + 1 / 18000) l r ∧
      L ∈ Ioo (-327 / 64 : ℝ) (-317 / 64) ∧ R ∈ Ioo (317 / 64 : ℝ) (327 / 64) ∧
      LaunchWell (profile z) 0 h L R ∧ L ≤ l ∧ r ≤ R ∧
      1 / 375 < action (profile z) (DommaschkNativeWellAction.density z) L R h -
        DommaschkActionHeightInverse.ambient y h

/-- Apply the paired certificate to two already chosen paths. This keeps the trajectory
used by the independent mirror-branch and arclength proofs. -/
theorem on_chosen_paths {i o : Checkpoint} {x : Plane} {y z : ℝ → Plane}
    (inner : DommaschkSignedObservable.Path i.length i.forwardExit i.backwardExit
      i.forwardRows i.backwardRows x y)
    (outer : Signed (MirrorEndpoint.start .q0r478) o.forwardRows o.backwardRows (o.length / 64) z)
    (hf : 325 ≤ i.forwardRows.length) (hb : 325 ≤ i.backwardRows.length)
    (cert : ComparedRows 325 i o) : ∀ t ∈ Icc (-bound) bound, Compared t (y t) (z t) := by
  have take_len {rs : List Step} (fits : 325 ≤ rs.length) : (rs.take 325).length = 325 := by
    simpa using min_eq_left fits
  have ne {rs : List Step} (fits : 325 ≤ rs.length) : rs.take 325 ≠ [] := by
    intro h
    have e := take_len fits
    rw [h] at e
    simp at e
  have f := cert.1.on_nonempty_prefix (moreR := i.forwardRows.drop 325)
    (moreQ := o.forwardRows.drop 325) (x := y) (y := z) (ne hf)
    (by simpa only [List.take_append_drop] using inner.forward)
    (by simpa only [List.take_append_drop] using outer.forward.contained)
  have b := cert.2.on_nonempty_prefix (moreR := i.backwardRows.drop 325)
    (moreQ := o.backwardRows.drop 325) (x := fun t => y (-t)) (y := fun t => z (-t)) (ne hb)
    (by simpa only [List.take_append_drop] using inner.backward)
    (by simpa only [List.take_append_drop] using outer.backward.contained)
  rw [take_len hf,zero_add,Nat.cast_ofNat] at f
  rw [take_len hb,zero_add,Nat.cast_ofNat] at b
  intro t ht
  rcases le_total 0 t with p | n
  · exact f t ⟨p,ht.2⟩
  · simpa only [neg_neg] using b (-t) ⟨neg_nonneg.mpr n, by
      have lower : -(325 / 64 : ℝ) ≤ t := ht.1
      linarith only [lower]⟩

/-- Enclosed physical branches, in either direction, give actual first-well actions
at all admissible heights. Only the pilot uses a height derivative. -/
theorem gains_of_branches {y z : ℝ → Plane} {φ T : ℝ} {entry : State} {fr br : List Step}
    (times : DommaschkActionFlightFloor.TimeBounds φ y)
    (test : DommaschkFiniteRadialAction.PairTest y)
    (full : ∀ t ∈ Icc (-bound) bound, Compared t (y t) (z t))
    (outer : Signed entry fr br T z) (room : 327 / 64 < T)
    (valid : ∀ t ∈ Icc (-327 / 64 : ℝ) (327 / 64), DommaschkSignedTraceDomain.Region (z t))
    (fwd : Branch (profile z) (317 / 64) (327 / 64) (height false) (height true) (1 / 400))
    (back : Branch (fun t => profile z (-t)) (317 / 64) (327 / 64)
      (height false) (height true) (1 / 400)) : Gains y z := by
  intro h h0 h1
  let H : Heights := ⟨h,h0⟩
  let r := fwd.time H
  let l := back.time H
  have hr : r ∈ Ioo (317 / 64 : ℝ) (327 / 64) := fwd.interior_time H
  have hl : l ∈ Ioo (317 / 64 : ℝ) (327 / 64) := back.interior_time H
  have well : LaunchWell (profile z) 0 h (-l) r := by
    refine ⟨by linarith [hl.1],by linarith [hr.1],back.hit H,fwd.hit H,?_⟩
    intro t ht
    rcases le_total 0 t with p | n
    · exact fwd.before H t ⟨p,ht.2⟩
    · simpa only [neg_neg] using back.before H (-t) ⟨neg_nonneg.mpr n,by linarith [ht.1]⟩
  have inside : Icc (-l) r ⊆ Ioo (-T) T :=
    fun t ht => ⟨by linarith [hl.2,ht.1],by linarith [hr.2,ht.2]⟩
  have region : ∀ t ∈ Icc (-l) r, DommaschkSignedTraceDomain.Region (z t) :=
    fun t ht => valid t ⟨by linarith [hl.2,ht.1],by linarith [hr.2,ht.2]⟩
  obtain ⟨cf,cw,eq⟩ := outer.inputs inside region
  obtain ⟨a,b,inner,left,right,gain⟩ :=
    increment_of_compared times test full h0 h1 well cf cw
      (fun t ht => by
        change 0 ≤ DommaschkLowerActionPath.density z t
        rw [← eq t ht]
        exact norm_nonneg _)
  refine ⟨a,b,-l,r,inner,⟨by linarith [hl.2],by linarith [hl.1]⟩,hr,well,left,right,?_⟩
  have same :
      action (profile z) (DommaschkNativeWellAction.density z) (-l) r h =
        action (profile z) (DommaschkMirrorBandFlightIdentity.density z) (-l) r h := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith [hl.1,hr.1])] at ht
    exact congrArg (fun a => a * _) (eq t ht)
  rwa [same]

/-- The two endpoint actions alone give a radial secant: the same pilot branches
work for every height. The pilot integral here is taken between its two physical mirrors. -/
theorem physical_secant {y z : ℝ → Plane} (pilot : DommaschkMirrorBandAction.ActionFamily y)
    (gains : Gains y z) :
    ∃ (p : DommaschkMirrorBandAction.Outward y 1) (m : DommaschkMirrorBandAction.Outward y (-1)),
      ∀ h : Heights, (h : ℝ) + 1 / 18000 ∈ Heights → ∃ L R,
        L ∈ Ioo (-327 / 64 : ℝ) (-317 / 64) ∧ R ∈ Ioo (317 / 64 : ℝ) (327 / 64) ∧
        LaunchWell (profile z) 0 (h : ℝ) L R ∧
        1 / 3 < (action (profile z) (DommaschkNativeWellAction.density z) L R h -
          DommaschkMirrorBandAction.wellAction y p m h) / (239 / 500 - 47 / 100) := by
  obtain ⟨p,m,_,_,value⟩ := pilot
  refine ⟨p,m,fun h raised => ?_⟩
  obtain ⟨_,_,L,R,_,lo,hi,well,_,_,gap⟩ := gains h h.2 raised
  refine ⟨L,R,lo,hi,well,?_⟩
  rw [value h]
  have spacing : (239 / 500 - 47 / 100 : ℝ) = 1 / 125 := by norm_num
  rw [spacing, lt_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 125)]
  exact lt_of_eq_of_lt (by norm_num) gap

open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- The embedded surfaces are chosen once for all angles. Each outer observation
retains its own physical approach from the interpolated birth to the section. -/
def OnCommonTori (c : MirrorEndpoint → Checkpoint) (P : ℝ → (ℝ → Plane) → Prop) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → ∃ y : ℝ → Plane,
      y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ) ∧ P φ y ∧
      AtBirth .q0r478 uC zC uA zA φ (fun z =>
        Signed (MirrorEndpoint.start .q0r478) (c .q0r478).forwardRows
          (c .q0r478).backwardRows ((c .q0r478).length / 64) z ∧ Gains y z)

/-- Use the same witness family for the calibrated pilot and the longer outer path. -/
theorem common {c : MirrorEndpoint → Checkpoint} {P : ℝ → (ℝ → Plane) → Prop}
    (family : DommaschkCommonPilotObservables.Common c P)
    (hf : 325 ≤ (c .q0r470).forwardRows.length) (hb : 325 ≤ (c .q0r470).backwardRows.length)
    (cert : ComparedRows 325 (c .q0r470) (c .q0r478))
    (gain : ∀ {φ y z}, P φ y →
      Signed (MirrorEndpoint.start .q0r478) (c .q0r478).forwardRows
        (c .q0r478).backwardRows ((c .q0r478).length / 64) z →
      (∀ t ∈ Icc (-bound) bound, Compared t (y t) (z t)) → Gains y z) : OnCommonTori c P := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,each,calibrate⟩ := family
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ?_⟩
  obtain ⟨x,y,born,path,obs⟩ := calibrate φ small
  refine ⟨y,born,obs,?_⟩
  have passage := each .q0r478 φ
    (by simpa [MirrorEndpoint.opposite, MirrorEndpoint.width, azimuth] using small)
  apply observe rfl passage
  intro z signed
  exact ⟨signed,gain obs signed (on_chosen_paths path signed hf hb cert)⟩

end PlasmaLean.Design.DommaschkPairedFirstWellAction
