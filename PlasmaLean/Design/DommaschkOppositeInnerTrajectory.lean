/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkOppositeInnerSeed
public import PlasmaLean.Design.DommaschkRibbonThroughChains

/-! # Independent signed physical chains through the original opposite-section birth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeInnerTrajectory

open Set Certificates.PositionFrameSlabs DommaschkLowerActionPath
open DommaschkJacobian (euclideanFlow)
open DommaschkEndpointSignedTrace DommaschkRibbonThroughChains DommaschkOppositeInnerSeed
open DommaschkMirrorLaunch DommaschkBounceField

abbrev phase : ℝ := Real.pi / 2

def Trace (n : ℕ) (fr br : List Step) (x : Plane) (y : ℝ → Plane) : Prop :=
  y 0 = x ∧ (∀ t ∈ Icc (-(n:ℝ)/64) (n/64),
    HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc (-(n:ℝ)/64) (n/64)) t) ∧
    Tracks fr br n y

private theorem tracked {entry : Certificates.PositionFrameSlabs.State} {rs : List Step}
    {z : ℝ → Plane} (mem : ∀ s ∈ physicalSlabs entry 0 rs,
      ∀ t ∈ Icc s.start s.stop, z t ∈ s.tube t) {i : ℕ} (hi : i < rs.length) :
    ∃ prev, ∀ t ∈ Icc ((i:ℝ)/64) (((i:ℝ)+1)/64),
      z t ∈ (physicalSlab prev rs[i] (i/64)).tube t := by
  obtain ⟨prev,m⟩ := DommaschkSignedObservable.slab_at entry 0 hi
  rw [zero_add] at m
  refine ⟨prev,fun t ht => mem _ m t ?_⟩
  change t ∈ Icc ((i:ℝ)/64) ((i:ℝ)/64+1/64)
  rwa [show (i:ℝ)/64+1/64 = (i+1:ℝ)/64 by ring]

theorem from_seed {n : ℕ} {fr br : List Step} {fend bend : Certificates.PositionFrameSlabs.State}
    (f : Steps (euclideanFlow phase 1) 0 seed n fend fr)
    (b : Steps (euclideanFlow phase (-1)) 0 seed n bend br) {x : Plane} (hx : x ∈ stateSet seed) :
    ∃ y, Trace n fr br x y := by
  obtain ⟨y,eq,_,_,ode,fw,bw⟩ := of_chains
    (by simpa only [Nat.cast_zero,zero_div] using f.chain)
    (by simpa only [Nat.cast_zero,zero_div] using b.chain) hx
  refine ⟨y,eq,by simpa only [neg_div] using ode,?_,?_⟩
  · intro i _ hi
    exact tracked fw hi
  · intro i _ hi
    exact tracked (z := fun t => y (-t)) bw hi

/-- The field-line approach to the common section and the two signed chains meet
at the same physical point in the seed. -/
def FromBirth (uC zC uA zA : Theory.KAM.FA) (φ : ℝ) (n : ℕ) (fr br : List Step)
    (P : (ℝ → Plane) → Prop) : Prop :=
  let t := |φ-phase|
  ∃ (sign : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |sign|=1 ∧ φ+sign*t=phase ∧ a 0 = birth uC zC uA zA u φ ∧
    (∀ s ∈ Icc 0 t, HasDerivWithinAt a (physicalFlow φ sign s (a s)) (Icc 0 t) s) ∧
    Trace n fr br (coordinates.symm (a t)) y ∧ P y

theorem from_entry {uC zC uA zA : Theory.KAM.FA} {φ : ℝ} (entry : Entry uC zC uA zA φ)
    {n : ℕ} {fr br : List Step} {fend bend : Certificates.PositionFrameSlabs.State}
    (f : Steps (euclideanFlow phase 1) 0 seed n fend fr)
    (b : Steps (euclideanFlow phase (-1)) 0 seed n bend br) {P : (ℝ → Plane) → Prop}
    (panels : ∀ y, Tracks fr br n y → P y) : FromBirth uC zC uA zA φ n fr br P := by
  obtain ⟨sign,a,hs,hφ,orig,ode,ball⟩ := entry
  have ident : seed.frame = ⟨2^40,0,0,2^40⟩ := rfl
  let point := coordinates.symm (a |φ-phase|)
  have inside : point ∈ stateSet seed := (mem_stateSet_identity ident point).mpr ball
  obtain ⟨y,trace⟩ := from_seed f b inside
  exact ⟨sign,a,y,hs,hφ,orig,ode,trace,panels y trace.2.2⟩

end PlasmaLean.Design.DommaschkOppositeInnerTrajectory
