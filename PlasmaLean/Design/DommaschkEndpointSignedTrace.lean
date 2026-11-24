/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkEndpointFirstSlab
public import PlasmaLean.Design.DommaschkMirrorTwoSided

/-! # Signed field lines at both Dommaschk launch sections -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkEndpointSignedTrace

open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkBounceField Set
open DommaschkJacobian (euclideanFlow velocityJacobian)
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- One increasing-angle physical solution through the common section state. The backward
archive is indexed by elapsed outward angle and encloses this same solution at negative time. -/
def Joined (phase T : ℝ) (x : Plane) (fe be : Set Plane)
    (fs bs : List (Fields.TrajectorySlabs.Slab Plane)) : Prop :=
  ∃ y : ℝ → Plane, y 0 = x ∧ y (-T) ∈ be ∧ y T ∈ fe ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc (-T) T) t) ∧
    (∀ s ∈ fs, ∀ t ∈ Icc s.start s.stop, y t ∈ s.tube t) ∧
    (∀ s ∈ bs, ∀ t ∈ Icc s.start s.stop, y (-t) ∈ s.tube t)

/-- Any two chains with a common section state and outward duration give one signed field line.
The two tube lists can have different subdivisions and shapes. -/
theorem of_chains {phase T : ℝ} {x : Plane} {entry fe be : Set Plane}
    {fs bs : List (Fields.TrajectorySlabs.Slab Plane)}
    (f : Fields.TrajectorySlabs.Chain (euclideanFlow phase 1) 0 entry T fe fs)
    (b : Fields.TrajectorySlabs.Chain (euclideanFlow phase (-1)) 0 entry T be bs)
    (hx : x ∈ entry) : Joined phase T x fe be fs bs := by
  obtain ⟨yf, fsame, fend, fode, ftube⟩ := f.exists_trajectory hx
  obtain ⟨yb, bsame, bend, bode, btube⟩ := b.exists_trajectory hx
  obtain ⟨y, left, right, ode⟩ := join_physical_clocks f.ordered (bsame.trans fsame.symm) fode bode
  refine ⟨y, (right ⟨le_rfl, f.ordered⟩).trans fsame, ?_, ?_, ode, ?_, ?_⟩
  · rw [left ⟨le_rfl, neg_nonpos.mpr b.ordered⟩]
    simpa using bend
  · rw [right ⟨f.ordered, le_rfl⟩]
    exact fend
  · intro s hs t ht
    rw [right (f.subinterval hs ht)]
    exact ftube s hs t ht
  · intro s hs t ht
    have interval := b.subinterval hs ht
    rw [left ⟨neg_le_neg interval.2, neg_nonpos.mpr interval.1⟩]
    simpa using btube s hs t ht

/-- A birth reaches its section by the physical approach and then follows the signed solution. -/
def FromBirth (e : MirrorEndpoint) (uC zC uA zA : FA) (φ T : ℝ) (fe be : Set Plane)
    (fs bs : List (Fields.TrajectorySlabs.Slab Plane)) : Prop :=
  let phase := azimuth e.opposite
  let duration := |φ - phase|
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State),
    |s| = 1 ∧ φ + s * duration = phase ∧ a 0 = birth uC zC uA zA e.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt a (physicalFlow φ s t (a t)) (Icc 0 duration) t) ∧
    Joined phase T (coordinates.symm (a duration)) fe be fs bs

/-- Use the physical state reached by the approach as the initial point of both chains. -/
theorem from_entry {e : MirrorEndpoint} {uC zC uA zA : FA} {φ T : ℝ} {fe be : Set Plane}
    {fs bs : List (Fields.TrajectorySlabs.Slab Plane)}
    (entry : SectionEntry e uC zC uA zA φ)
    (f : Fields.TrajectorySlabs.Chain (euclideanFlow (azimuth e.opposite) 1)
      0 (stateSet e.start) T fe fs)
    (b : Fields.TrajectorySlabs.Chain (euclideanFlow (azimuth e.opposite) (-1))
      0 (stateSet e.start) T be bs) : FromBirth e uC zC uA zA φ T fe be fs bs := by
  obtain ⟨s, a, hs, ha, src, ode, inside⟩ := entry
  have frame : e.start.frame = ⟨2^40, 0, 0, 2^40⟩ := by cases e <;> rfl
  exact ⟨s, a, hs, ha, src, ode, of_chains f b ((mem_stateSet_identity frame _).mpr inside)⟩

/-- A concrete first-row bound supplies the physical chain used on that branch. -/
theorem first_chain {e : MirrorEndpoint} {lim : Limits} {r : Step} {sign : ℝ}
    (h : test lim e.start r = true)
    (g : FieldBounds e.start r 0 (euclideanFlow (azimuth e.opposite) sign)
      (velocityJacobian (azimuth e.opposite) sign) ballDomain) :
    Fields.TrajectorySlabs.Chain (euclideanFlow (azimuth e.opposite) sign) 0 (stateSet e.start)
      (1/64) (stateSet (next r)) (physicalSlabs e.start 0 [r]) := by
  have full : FieldBoundsOn (euclideanFlow (azimuth e.opposite) sign)
      (velocityJacobian (azimuth e.opposite) sign) e.start 0 [[r]].flatten ballDomain :=
    ⟨g, trivial⟩
  simpa using (DommaschkEndpointFirstSlab.singleton h).physical full

/-- One pair of physical flux surfaces supports all signed endpoint traces, including at π/2. -/
def Common {ι : Type*} (endpoint : ι → MirrorEndpoint) (T : ℝ) (fe be : ι → Set Plane)
    (fs bs : ι → List (Fields.TrajectorySlabs.Slab Plane)) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    ∀ i φ, |φ - azimuth (endpoint i).opposite| ≤ (endpoint i).width →
      FromBirth (endpoint i) uC zC uA zA φ T (fe i) (be i) (fs i) (bs i)

theorem common_of_chains {ι : Type*} (endpoint : ι → MirrorEndpoint)
    {T : ℝ} {fe be : ι → Set Plane} {fs bs : ι → List (Fields.TrajectorySlabs.Slab Plane)}
    (f : ∀ i, Fields.TrajectorySlabs.Chain (euclideanFlow (azimuth (endpoint i).opposite) 1)
      0 (stateSet (endpoint i).start) T (fe i) (fs i))
    (b : ∀ i, Fields.TrajectorySlabs.Chain (euclideanFlow (azimuth (endpoint i).opposite) (-1))
      0 (stateSet (endpoint i).start) T (be i) (bs i)) :
    Common endpoint T fe be fs bs := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, entries⟩ :=
    exists_nested_section_entry
  exact ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, fun i φ hp =>
    from_entry (entries (endpoint i) φ hp) (f i) (b i)⟩

end PlasmaLean.Design.DommaschkEndpointSignedTrace
