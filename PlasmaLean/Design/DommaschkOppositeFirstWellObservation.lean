/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkOppositeInnerTrajectory
public import PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues
public import PlasmaLean.Design.DommaschkShiftedActionSubwell
public import PlasmaLean.Certificates.ActionCoverAgreement
public import PlasmaLean.Theory.Fields.ClosedIntervalODEAgreement

/-! # Opposite-section observations on the first well of the actual birth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeFirstWellObservation
open Set Certificates.PositionFrameSlabs DommaschkLowerActionPath DommaschkMirrorLaunch
open DommaschkOppositeInnerTrajectory DommaschkOppositeInnerSeed DommaschkSignedTraceDomain
open DommaschkRadialFamilyContinuity DommaschkBounceField DommaschkMirrorTubeCrossing
open DommaschkJacobian (euclideanFlow)
open DommaschkPhysicalActionPanel DommaschkShiftedActionSubwell
open Kinetic.MirrorActionEnvelope Certificates.MirrorActionQuadrature

abbrev valueF (y : ℝ → Plane) (t : ℝ) := strength (phase+t) (y t)
abbrev valueW (y : ℝ → Plane) (t : ℝ) := arcDensity (y t 0) (phase+t) (y t 1)

private theorem first_box {fr br : List Step} {y : ℝ → Plane} {n : ℕ} (positive : 0 < n)
    (hf : 0 < fr.length) (hb : 0 < br.length) (f : packed fr[0] = true) (b : packed br[0] = true)
    (tr : Tracks fr br n y) {t : ℝ} (ht : t ∈ Icc (-(1 / 64)) (1 / 64)) : Region (y t) := by
  rcases le_total 0 t with pos | neg
  · obtain ⟨p,row⟩ := tr.1 0 positive hf
    have h : t ∈ Icc (0:ℝ) (1/64) := ⟨pos,ht.2⟩
    apply region_of_mem (s := p) (a := 0) (t := t) f (by simpa only [zero_add] using h)
    simpa only [Nat.cast_zero,zero_div,Bool.false_eq_true,↓reduceIte] using row t (by simpa using h)
  · obtain ⟨p,row⟩ := tr.2 0 positive hb
    have h : -t ∈ Icc (0:ℝ) (1/64) := ⟨neg_nonneg.mpr neg,by linarith [ht.1]⟩
    apply region_of_mem (s := p) (a := 0) (t := -t) b (by simpa only [zero_add] using h)
    simpa only [Nat.cast_zero,zero_div,↓reduceIte,neg_neg] using row (-t) (by simpa using h)

/-- The relative clock locates the released point itself anywhere in the launch arc.
The approach and the true signed trajectory therefore yield the same birth position. -/
theorem born {uC zC uA zA : Theory.KAM.FA} {φ : ℝ} {n : ℕ} {fr br : List Step}
    {P : (ℝ → Plane) → Prop} (small : |φ - phase| ≤ width) (positive : 0 < n)
    (hf : 0 < fr.length) (hb : 0 < br.length) (f : packed fr[0] = true) (b : packed br[0] = true)
    (arrived : DommaschkOppositeInnerTrajectory.FromBirth uC zC uA zA φ n fr br P) :
    ∃ (x : Plane) (y : ℝ → Plane), Trace n fr br x y ∧
      y (φ-phase) = coordinates.symm (birth uC zC uA zA u φ) ∧ P y := by
  obtain ⟨sign,a,y,unit,clock,start,approach,trace,props⟩ := arrived
  have wide : (1/64:ℝ) ≤ n / 64 := by gcongr; exact_mod_cast positive
  have eq := DommaschkPhysicalFirstMirrorValues.original_position (phase := phase) wide
    (small.trans (by norm_num [width])) unit clock trace.1 approach
    (by simpa only [neg_div] using trace.2.1)
    (fun _ ht => first_box positive hf hb f b trace.2.2 ht)
  exact ⟨_,y,trace,by simpa only [start] using eq,props⟩

/-- The comparison curve is only required to solve the physical equation on its own
observed interval. Local uniqueness uses regularity along this comparison curve. -/
theorem agree_on_overlap {n : ℕ} {fr br : List Step} {x : Plane} {y Y : ℝ → Plane}
    {φ l r : ℝ} (trace : Trace n fr br x y) (observer : Enclosed Y l r)
    (birth : y (φ - phase) = Y φ) (clock : φ - phase ∈ Icc (-(n : ℝ) / 64) (n / 64))
    (inside : φ ∈ Icc l r) :
    ∀ t ∈ Icc (max (-(n:ℝ)/64) (l-phase)) (min (n/64) (r-phase)), y t = Y (phase+t) := by
  let s := Icc (max (-(n:ℝ)/64) (l-phase)) (min (n/64) (r-phase))
  have part : s ⊆ Icc (-(n:ℝ)/64) (n/64) := Icc_subset_Icc (le_max_left ..) (min_le_left ..)
  have shift : MapsTo (fun t => phase+t) s (Icc l r) := by
    intro t ht
    have a := (le_max_right _ _).trans ht.1
    have b := ht.2.trans (min_le_right _ _)
    exact ⟨by linarith,by linarith⟩
  have start : φ-phase ∈ s :=
    ⟨max_le clock.1 (by linarith [inside.1]),le_min clock.2 (by linarith [inside.2])⟩
  let z := fun t => Y (phase+t)
  have zd (t) (ht : t ∈ s) : HasDerivWithinAt z (euclideanFlow phase 1 t (z t)) s t := by
    have dκ : HasDerivAt (fun v : ℝ => phase+v) 1 t := (hasDerivAt_id t).const_add phase
    have comp := (observer.ode (phase+t) (shift ht)).scomp t dκ
    have eq : euclideanFlow 0 1 (phase+t) (z t) = euclideanFlow phase 1 t (z t) := by
      simp [euclideanFlow,DommaschkBounceField.physicalFlow]
    simpa only [Function.comp_def,one_smul,eq,z] using comp.hasDerivWithinAt (s := s)
  have toCoord (v : ℝ → Plane) (t : ℝ)
      (dv : HasDerivWithinAt v (euclideanFlow phase 1 t (v t)) s t) :
      HasDerivWithinAt (fun q => coordinates (v q))
        (physicalFlow phase 1 t (coordinates (v t))) s t :=
    (coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t dv).congr_deriv
      (coordinates.apply_symm_apply _)
  have same := Fields.ode_eqOn_of_value start
    (fun t ht => toCoord y t ((trace.2.1 t (part ht)).mono part))
    (fun t ht => toCoord z t (zd t ht)) (fun t ht => by
      have box := observer.region (phase+t) (shift ht)
      have den := DommaschkSignedTraceDenominator.regular (phase+t) box.1 box.2
      apply DommaschkSignedBirthApproach.physical_smooth
      · exact (by norm_num : (0:ℝ) < 7/8).trans_le box.1.1
      · have rad : coordinates (z t) 0 = (z t) 0 := rfl
        have vert : coordinates (z t) 1 = (z t) 1 := rfl
        simpa only [clockPoly,one_mul,rad,vert,z] using
          ((by norm_num : (0:ℝ) < 1/64).trans den).ne')
    (by
      rw [show z (φ-phase) = Y φ by simp only [z,add_sub_cancel]]
      exact congrArg coordinates birth)
  exact fun _ ht => coordinates.injective (same ht)

/-- An independently observed first well either contains the entire positive-speed core,
or a claimed first hit inside the core contradicts ODE uniqueness at that very point.
The observer's differential equation and regularity are only required inside its own well. -/
theorem observed_cover {n : ℕ} {fr br : List Step} {x : Plane} {y Y : ℝ → Plane} {φ l r h : ℝ}
    {bs : List (Block false)} (len : bs.length = n + n)
    (positive : bs.all (fun b => Certificates.PositiveSubwell.positive 48 b.packed) = true)
    (trace : Trace n fr br x y) (birth : y (φ - phase) = Y φ)
    (clock : φ - phase ∈ Icc (-(n : ℝ) / 64) (n / 64))
    (cells : Covers false (valueW y) (valueF y) h (-(n : ℝ) / 64) bs)
    (observer : Enclosed Y l r) (well : LaunchWell (DommaschkNativeWellAction.field Y) φ h l r) :
    l ≤ phase - n/64 ∧ phase + n/64 ≤ r ∧
    Covers false (arcAt phase Y) (fieldAt phase Y) h (-(n:ℝ)/64) bs := by
  have stop : -(n:ℝ)/64 + bs.length/64 = n/64 := by rw [len,Nat.cast_add]; ring
  have below := Certificates.PositiveSubwell.below positive cells
  rw [stop] at below
  have common := agree_on_overlap trace observer birth clock ⟨well.left_lt.le,well.lt_right.le⟩
  have agree (t) (win : t ∈ Icc (-(n:ℝ)/64) (n/64)) (hw : phase+t ∈ Icc l r) :
      y t = Y (phase+t) := common t
    ⟨max_le win.1 (by linarith [hw.1]),le_min win.2 (by linarith [hw.2])⟩
  have low : l ≤ phase - n/64 := by
    by_contra! bad
    have hpos : l-phase ∈ Ico (-(n:ℝ)/64) (n/64) :=
      ⟨by linarith,by linarith [clock.2,well.left_lt]⟩
    have eq : phase+(l-phase) = l := by ring
    have bound := below _ hpos
    rw [valueF,agree _ (Ico_subset_Icc_self hpos)
      (by rw [eq]; exact left_mem_Icc.mpr (well.left_lt.trans well.lt_right).le),eq] at bound
    exact bound.ne well.left_hit
  have high : phase + n/64 ≤ r := by
    by_contra! bad
    have hpos : r-phase ∈ Ico (-(n:ℝ)/64) (n/64) :=
      ⟨by linarith [clock.1,well.lt_right],by linarith⟩
    have eq : phase+(r-phase) = r := by ring
    have bound := below _ hpos
    rw [valueF,agree _ (Ico_subset_Icc_self hpos)
      (by rw [eq]; exact right_mem_Icc.mpr (well.left_lt.trans well.lt_right).le),eq] at bound
    exact bound.ne well.right_hit
  refine ⟨low,high,cells.congr_on ?_⟩
  intro t ht
  rw [stop] at ht
  have eq := agree t ht ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simp only [arcAt,fieldAt,DommaschkNativeWellAction.field,valueW,valueF,eq, and_self]

/-- A measurement through the actual embedded-torus birth. Its own first-well interval
is the entire domain on which a regular physical equation is required. -/
def Measures (uC zC uA zA : Theory.KAM.FA) (φ h J : ℝ) : Prop :=
  ∃ (Y : ℝ → Plane) (l r : ℝ), Y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
    Enclosed Y l r ∧ LaunchWell (DommaschkNativeWellAction.field Y) φ h l r ∧
    Kinetic.MirrorHeightAction.action (DommaschkNativeWellAction.field Y)
      (DommaschkNativeWellAction.density Y) l r h = J

theorem lower_on_measurement {uC zC uA zA : Theory.KAM.FA} {n : ℕ} {fr br : List Step}
    {x : Plane} {y : ℝ → Plane} {φ h J : ℝ} {bs : List (Block false)}
    (len : bs.length = n + n)
    (positive : bs.all (fun b => Certificates.PositiveSubwell.positive 48 b.packed) = true)
    (trace : Trace n fr br x y) (born_at : y (φ - phase) = coordinates.symm (birth uC zC uA zA u φ))
    (clock : φ - phase ∈ Icc (-(n : ℝ) / 64) (n / 64))
    (cells : Covers false (valueW y) (valueF y) h (-(n : ℝ) / 64) bs)
    (measurement : Measures uC zC uA zA φ h J) : total bs / (3072 * 1099511627776 : ℝ) ≤ J := by
  obtain ⟨Y,l,r,byBirth,observer,well,value⟩ := measurement
  have overlap := observed_cover len positive trace (born_at.trans byBirth.symm) clock cells
    observer well
  obtain ⟨w,cf,cw,nn,eq⟩ := shifted (s := phase) observer well
  have mass := Certificates.PositiveSubwell.floor_in_first_well len positive overlap.2.2 clock w
    nn cf cw
  rw [eq,value] at mass
  exact mass.2.2

end PlasmaLean.Design.DommaschkOppositeFirstWellObservation
