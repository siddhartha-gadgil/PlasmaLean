/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhaseZeroRegularBirth
public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnCompact

/-! # Uniform guiding-centre time for a whole pilot arc and closed energy-height bands -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCompactLittlejohnArc
open Set MeasureTheory Contract Fields Contract.TrappedBirthCoordinates
open Kinetic.VacuumLittlejohnWindow DommaschkFirstMirrorWell DommaschkCartesianAngleFlow
open DommaschkFirstMirrorLaunchSign DommaschkCommonLittlejohnTime DommaschkPhaseZeroRegularBirth
open DommaschkSignedTraceDomain DommaschkSignedObservable
open Certificates.PositionFrameSlabs (Plane State Step)

abbrev heights : Set ℝ := Icc (height false : ℝ) (height true)

/-- Velocity and moment lifts over the positions and closed energy-height rectangle. -/
def seeds (m : ℝ) (X : Set Space) (lo hi : ℝ) (neg : Bool) : Set GCBirth :=
  (fun p : Space × ℝ × ℝ => lift B m p.1 p.2.1 p.2.2 neg) '' (X ×ˢ (Icc lo hi ×ˢ heights))

set_option maxRecDepth 12000 in
private theorem compact_seeds {X : Set Space} (compact : IsCompact X)
    (field : ContinuousOn (fun x => ‖B x‖) X) (m lo hi : ℝ) (neg : Bool) :
    IsCompact (seeds m X lo hi neg) := by
  let D := X ×ˢ (Icc lo hi ×ˢ heights)
  apply (compact.prod (isCompact_Icc.prod isCompact_Icc)).image_of_continuousOn
  have cx : ContinuousOn (fun p : Space × ℝ × ℝ => p.1) D := continuous_fst.continuousOn
  have ce : ContinuousOn (fun p : Space × ℝ × ℝ => p.2.1) D :=
    (continuous_fst.comp continuous_snd).continuousOn
  have ch : ContinuousOn (fun p : Space × ℝ × ℝ => p.2.2) D :=
    (continuous_snd.comp continuous_snd).continuousOn
  have cb := field.comp cx (fun p hp => hp.1)
  have positive : 0 < (height false : ℝ) := by norm_num [height]
  have cm := ce.div ch (fun p hp => ne_of_gt (positive.trans_le hp.2.2.1))
  have cv : ContinuousOn (fun p : Space × ℝ × ℝ =>
      Real.sqrt (2 * (p.2.1 - (p.2.1 / p.2.2) * ‖B p.1‖) / m)) D :=
    ((continuousOn_const.mul (ce.sub (cm.mul cb))).div_const m).sqrt
  cases neg
  · exact cx.prodMk (cv.prodMk cm)
  · exact cx.prodMk (cv.neg.prodMk cm)

/-- A controlled open set contains both complete signed families, and actually meets each sign. -/
structure Window (m q lo hi d T : ℝ) (X : Set Space) (S W : Set GCBirth)
    (energies pitches : Set ℝ) : Prop where
  isOpen : IsOpen W
  contains : ∀ neg, seeds m X lo hi neg ⊆ W
  reference : W ⊆ trappedReference B m S energies pitches
  both : ∀ neg, (W ∩ signSet neg).Nonempty
  control : ∀ p ∈ W, Control B m q T d p

/-- The one controlled set contains a positive-radius metric tube around the union of
both complete families in five-dimensional birth space. -/
theorem Window.thickening {m q lo hi d T : ℝ} {X : Set Space} {S W : Set GCBirth}
    {energies pitches : Set ℝ} (w : Window m q lo hi d T X S W energies pitches)
    (compact : IsCompact X) (field : ContinuousOn (fun x => ‖B x‖) X) :
    ∃ ε > 0, Metric.cthickening ε (seeds m X lo hi false ∪ seeds m X lo hi true) ⊆ W := by
  have K := (compact_seeds compact field m lo hi false).union
    (compact_seeds compact field m lo hi true)
  exact K.exists_cthickening_subset_open w.isOpen
    (union_subset (w.contains false) (w.contains true))

/-- The measured fraction has the mass of this single open controlled set in the numerator.
The two parallel velocity signs each have positive measure in that same set. -/
theorem Window.measured {m q lo hi d T : ℝ} {X : Set Space} {S W : Set GCBirth}
    {energies pitches : Set ℝ} (w : Window m q lo hi d T X S W energies pitches)
    (hm : 0 < m) (hq : q ≠ 0) (hd : 0 < d) (ht : 0 < T)
    (ν : Measure GCBirth) [Measure.IsOpenPosMeasure ν] {axis : Set Space}
    (axis_ne : axis.Nonempty) (axis_compact : IsCompact axis)
    (meas : MeasurableSet (trappedReference B m S energies pitches))
    (finite : ν (trappedReference B m S energies pitches) ≠ ⊤) :
    (∀ neg, 0 < ν (W ∩ signSet neg)) ∧ GuidingCentreBand B m q axis ν S W energies pitches
      (ν.real W / ν.real (trappedReference B m S energies pitches)) d T :=
  ⟨fun neg => (w.isOpen.inter (signSet_open neg)).measure_pos ν (w.both neg),
    guidingCentreBand ν hm hq axis_ne axis_compact ht hd w.isOpen
      ((w.both false).mono inter_subset_left) w.reference meas finite w.control⟩

/-- Fix species, a positive excursion cap, and any closed positive energy interval contained
in the energy cut. The single time and open set serve both signs and every height and energy. -/
def Uniform (X : Set Space) : Prop :=
  ∀ m q lo hi d : ℝ, 0 < m → q ≠ 0 → 0 < lo → lo ≤ hi → 0 < d →
    ∀ (S : Set GCBirth) (energies pitches : Set ℝ),
      (∀ neg, seeds m X lo hi neg ⊆ interior S) → Icc lo hi ⊆ interior energies →
      (∀ h ∈ heights, 1 / h ∈ interior pitches) →
      ∃ T > 0, ∃ W : Set GCBirth, Window m q lo hi d T X S W energies pitches ∧
        ∃ ε > 0, Metric.cthickening ε (seeds m X lo hi false ∪ seeds m X lo hi true) ⊆ W

/-- A compact position family of compatible physical mirror births admits uniform local
orbit control throughout the prescribed height band. -/
theorem of_compact {X : Set Space} (compact : IsCompact X) (exists_x : X.Nonempty)
    (field : ContinuousOn (fun x => ‖B x‖) X) (all : ∀ x ∈ X, UniformAt x) : Uniform X := by
  intro m q lo hi d hm hq hlo order hd S energies pitches support energy pitch
  let R := trappedReference B m S energies pitches
  have each (neg : Bool) : FamilyControl B m q d (R ∩ signSet neg) (seeds m X lo hi neg) := by
    apply familyControl_of_local (compact_seeds compact field m lo hi neg)
    rintro _ ⟨⟨x,e,h⟩,⟨hx,he,hh⟩,rfl⟩
    have supp (n : Bool) : lift B m x e h n ∈ interior S :=
      support n ⟨(x,e,h),⟨hx,he,hh⟩,rfl⟩
    obtain ⟨T,ht,groups⟩ := all x hx m q e h d hm hq (hlo.trans_le he.1) hh hd
      (fun _ => S) energies pitches supp (energy he) (pitch h hh)
    obtain ⟨W,op,mem,inside,controls⟩ := groups neg
    exact ⟨T,ht,W,op,singleton_subset_iff.mpr mem,inside,controls⟩
  obtain ⟨T,ht,U,ou,cu,ru,gu⟩ := each false
  obtain ⟨V,hv,W,ow,cw,rw,gw⟩ := each true
  have some_seed (neg : Bool) : (seeds m X lo hi neg).Nonempty := by
    obtain ⟨x,hx⟩ := exists_x
    have hh : (height false : ℝ) ∈ heights := ⟨le_rfl,by norm_num [height]⟩
    exact ⟨_,(x,lo,(height false : ℝ)),⟨hx,⟨le_rfl,order⟩,hh⟩,rfl⟩
  have observed : Window m q lo hi d (min T V) X S (U ∪ W) energies pitches := by
    refine ⟨ou.union ow,?_,?_,?_,?_⟩
    · intro neg
      cases neg
      · exact cu.trans subset_union_left
      · exact cw.trans subset_union_right
    · exact union_subset (ru.trans inter_subset_left) (rw.trans inter_subset_left)
    · intro neg
      cases neg
      · obtain ⟨p,hp⟩ := some_seed false
        exact ⟨p,Or.inl (cu hp),(ru (cu hp)).2⟩
      · obtain ⟨p,hp⟩ := some_seed true
        exact ⟨p,Or.inr (cw hp),(rw (cw hp)).2⟩
    · intro p hp
      exact hp.elim (fun h => (gu p h).mono (min_le_left _ _))
        (fun h => (gw p h).mono (min_le_right _ _))
  exact ⟨min T V,lt_min ht hv,U ∪ W,observed,observed.thickening compact field⟩

/-- The standard positive dimensionless unit choices and unrestricted cuts give a nonempty
instance for the whole energy interval from one through two. -/
theorem Uniform.unrestricted {X : Set Space} (family : Uniform X) {d : ℝ} (hd : 0 < d) :
    ∃ T > 0, ∃ W : Set GCBirth, Window 1 1 1 2 d T X univ W univ univ ∧
      ∃ ε > 0, Metric.cthickening ε (seeds 1 X 1 2 false ∪ seeds 1 X 1 2 true) ⊆ W :=
  family 1 1 1 2 d (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd univ univ univ
    (by simp) (by simp) (by simp)

/-- Apply compactness to the Cartesian image of the entire closed central arc of this
actual signed trajectory, including both angular endpoints. -/
theorem of_path {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {a : ℝ} (p : Path n fs bs fr br x y) (ha : 0 ≤ a) (room : a < n / 64)
    (region : ∀ t ∈ Icc (-a) a, Region (y t)) (population : Population a y) :
    Uniform (point y '' Icc (-a) a) := by
  have cart (t : ℝ) (ht : t ∈ Icc (-a) a) := in_regular (region t ht) t
  have cy : ContinuousOn (point y) (Icc (-a) a) := by
    intro t ht
    have mid : t ∈ Ioo (-(n : ℝ) / 64) (n / 64) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have dy := (p.ode t (Ioo_subset_Icc_self mid)).hasDerivAt (Icc_mem_nhds mid.1 mid.2)
    exact (cartesian_ode dy (region t ht)).continuousAt.continuousWithinAt
  apply of_compact (isCompact_Icc.image_of_continuousOn cy)
    ((nonempty_Icc.mpr (neg_le_self ha)).image _)
  · rintro _ ⟨t,ht,rfl⟩
    exact (strength_smooth (cart t ht)).continuousAt.continuousWithinAt
  · rintro _ ⟨t,ht,rfl⟩
    exact (population.1 t ht).2.2.1

end PlasmaLean.Design.DommaschkCompactLittlejohnArc
