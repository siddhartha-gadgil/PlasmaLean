/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCompactLaunchPhases
public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnEnvelope

/-! # A common time for every regular pilot birth arc in the archived cylindrical envelope -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkEnclosedLaunchArcs
open Set Fields Contract Contract.TrappedBirthCoordinates DommaschkCartesianAngleFlow
open DommaschkCommonLittlejohnTime DommaschkCompactLittlejohnArc DommaschkCompactLaunchPhases
open DommaschkFirstMirrorLaunchSign DommaschkSignedTraceDomain Kinetic.VacuumLittlejohnWindow
open Certificates.PositionFrameSlabs (coordinates Plane)

/-- Cartesian image of the full cylindrical range through which the central arcs pass. -/
def positions : Set Space :=
  (fun v : ℝ × ℝ × ℝ => cylPoint v.1 v.2.1 v.2.2) ''
    (Icc (7 / 8) 1 ×ˢ (Icc (-(316 / 64)) (316 / 64) ×ˢ Icc (-(5 / 64)) (5 / 64)))

theorem positions_compact : IsCompact positions :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
    (continuous_cylinder continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd))

theorem positions_regular {x : Space} (hx : x ∈ positions) :
    x ∈ DommaschkLocalLittlejohnBirth.vacuumRegion := by
  obtain ⟨⟨r,t,z⟩,⟨hr,_,hz⟩,rfl⟩ := hx
  let p : Plane := coordinates.symm ![r,z]
  have box : Region p := ⟨hr,abs_le.mpr hz⟩
  have reg := in_regular box t
  exact ⟨reg.1,field_ne_zero reg⟩

set_option maxRecDepth 12000 in
/-- For either sign the entire lifted family fits a fixed compact velocity and moment range. -/
private theorem seeds_enclosed {m lo hi : ℝ} (hm : 0 < m) (hlo : 0 < lo) {X : Set Space}
    (domain : X ⊆ positions) (neg : Bool) :
    seeds m X lo hi neg ⊆ positions ×ˢ
      (Icc (-Real.sqrt (2 * hi / m)) (Real.sqrt (2 * hi / m)) ×ˢ
        Icc 0 (hi / (height false : ℝ))) := by
  rintro p ⟨⟨x,e,h⟩,⟨hx,he,hh⟩,rfl⟩
  have lowPos : 0 < (height false : ℝ) := by norm_num [height]
  have hp := lowPos.trans_le hh.1
  have ep := hlo.trans_le he.1
  have mom : 0 ≤ e / h := (div_pos ep hp).le
  have vel := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((sub_le_self e (mul_nonneg mom (norm_nonneg (B x)))).trans he.2)
      (by norm_num : (0 : ℝ) ≤ 2)) hm.le)
  have vel0 := Real.sqrt_nonneg (2 * (e - (e / h) * ‖B x‖) / m)
  have top := Real.sqrt_nonneg (2 * hi / m)
  have cap : e / h ≤ hi / (height false : ℝ) :=
    (div_le_div_of_nonneg_right he.2 hp.le).trans
      (div_le_div_of_nonneg_left (ep.le.trans he.2) lowPos hh.1)
  refine ⟨domain hx,?_,mom,cap⟩
  cases neg
  · exact ⟨(neg_nonpos.mpr top).trans vel0,vel⟩
  · exact ⟨neg_le_neg vel,(neg_nonpos.mpr vel0).trans top⟩

/-- All seeds use a single duration and controlled open subset of the reference, including
when no continuity of a chosen family of trajectories with respect to its launch is available. -/
def Simultaneous (X : Set Space) : Prop :=
  ∀ m q lo hi d : ℝ, 0 < m → q ≠ 0 → 0 < lo → lo ≤ hi → 0 < d →
    ∃ T > 0, ∀ (S : Set GCBirth) (energies pitches : Set ℝ),
      (∀ neg, seeds m X lo hi neg ⊆ interior S) → Icc lo hi ⊆ interior energies →
      (∀ h ∈ heights, 1 / h ∈ interior pitches) →
      ∃ W : Set GCBirth, Window m q lo hi d T X S W energies pitches

set_option maxRecDepth 12000 in
/-- A family of regular trapped positions anywhere in the certified compact envelope can
share one open controlled neighborhood over the energy-height rectangle and both signs. -/
theorem uniform_enclosed {X : Set Space} (exists_x : X.Nonempty) (domain : X ⊆ positions)
    (all : ∀ x ∈ X, UniformAt x) : Simultaneous X := by
  intro m q lo hi d hm hq hlo order hd
  let C : Set GCBirth := positions ×ˢ
    (Icc (-Real.sqrt (2 * hi / m)) (Real.sqrt (2 * hi / m)) ×ˢ Icc 0 (hi / (height false : ℝ)))
  have compactC : IsCompact C := positions_compact.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨T,ht,applyTo⟩ := common_enclosure_time (DommaschkQA2R.field_vacuum _) m q hd
    compactC (fun _ hp => positions_regular hp.1)
  refine ⟨T,ht,?_⟩
  intro S energies pitches support energy pitch
  let R := trappedReference B m S energies pitches
  let K := seeds m X lo hi false ∪ seeds m X lo hi true
  have here (neg : Bool) {p : GCBirth} (hp : p ∈ seeds m X lo hi neg) :
      p ∈ interior R ∧ p ∈ signSet neg := by
    obtain ⟨⟨x,e,h⟩,⟨hx,he,hh⟩,rfl⟩ := hp
    obtain ⟨_,_,groups⟩ := all x hx m q e h d hm hq (hlo.trans_le he.1) hh hd
      (fun _ => S) energies pitches (fun n => support n ⟨(x,e,h),⟨hx,he,hh⟩,rfl⟩)
      (energy he) (pitch h hh)
    obtain ⟨U,op,mem,valid,_⟩ := groups neg
    exact ⟨interior_maximal (valid.trans inter_subset_left) op mem,(valid mem).2⟩
  have inside : K ⊆ interior R :=
    union_subset (fun _ h => (here false h).1) (fun _ h => (here true h).1)
  obtain ⟨W,op,inc,ref,control⟩ := applyTo K R
    (union_subset (seeds_enclosed hm hlo domain false) (seeds_enclosed hm hlo domain true)) inside
  have contains (neg : Bool) : seeds m X lo hi neg ⊆ W := by
    cases neg
    · exact subset_union_left.trans inc
    · exact subset_union_right.trans inc
  refine ⟨W,op,contains,ref,?_,control⟩
  intro neg
  obtain ⟨x,hx⟩ := exists_x
  have hh : (height false : ℝ) ∈ heights := ⟨le_rfl,by norm_num [height]⟩
  have seed : lift B m x lo (height false) neg ∈ seeds m X lo hi neg :=
    ⟨(x,lo,(height false : ℝ)),⟨hx,⟨le_rfl,order⟩,hh⟩,rfl⟩
  exact ⟨_,contains neg seed,(here neg seed).2⟩

end PlasmaLean.Design.DommaschkEnclosedLaunchArcs
