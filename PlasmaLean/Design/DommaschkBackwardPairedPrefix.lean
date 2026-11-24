/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBackwardPrefixRadius
public import PlasmaLean.Design.DommaschkMirrorTwoSided

/-! # Join equally long certified trace prefixes at their actual Q-16 entry state

The backward tubes refer to increasing elapsed time on the negative branch.
The joined physical field line uses increasing geometric azimuth throughout.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkBackwardPairedPrefix
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkKamC KamNewton Set
open DommaschkJacobian (euclideanFlow velocityJacobian)
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2

/-- Certificates for one specified sign and sequence of outward rows. -/
structure Direction (sign : ℝ) (n : ℕ) (exit : State) (rows : List Step) : Prop where
  checked : Chain pilotLimits (MirrorEndpoint.start .q0r470) [rows] n exit
  bounds : FieldBoundsOn (euclideanFlow 0 sign) (velocityJacobian 0 sign)
    (MirrorEndpoint.start .q0r470) 0 rows ballDomain

/-- Geometry, ODE and both chronologically ordered sets of tubes for one physical line. -/
def SignedTrace (n : ℕ) (fexit bexit : State) (frows brows : List Step) (x : Plane) : Prop :=
  let T := (n:ℝ)/64
  ∃ y : ℝ → Plane, y 0 = x ∧ y (-T) ∈ stateSet bexit ∧ y T ∈ stateSet fexit ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-T) T) t) ∧
    (∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 frows,
      ∀ t ∈ Icc slab.start slab.stop, y t ∈ slab.tube t) ∧
    (∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 brows,
      ∀ t ∈ Icc slab.start slab.stop, y (-t) ∈ slab.tube t)

/-- The two certified branches can always be taken from the very same entry. -/
theorem signedTrace {n : ℕ} {fexit bexit : State} {frows brows : List Step}
    (f : Direction 1 n fexit frows) (b : Direction (-1) n bexit brows) {x : Plane}
    (hx : x ∈ stateSet (MirrorEndpoint.start .q0r470)) :
    SignedTrace n fexit bexit frows brows x := by
  let T := (n:ℝ)/64
  have pos : 0 ≤ T := by dsimp [T]; positivity
  have paths {sign : ℝ} {e : State} {rs : List Step} (d : Direction sign n e rs) :
      Fields.TrajectorySlabs.Chain (euclideanFlow 0 sign) 0
        (stateSet (MirrorEndpoint.start .q0r470)) T (stateSet e)
        (physicalSlabs (MirrorEndpoint.start .q0r470) 0 rs) := by
    have hb : FieldBoundsOn (euclideanFlow 0 sign) (velocityJacobian 0 sign)
        (MirrorEndpoint.start .q0r470) 0 [rs].flatten ballDomain := by simpa using d.bounds
    simpa [T] using d.checked.physical hb
  have fp := paths f
  have bp := paths b
  obtain ⟨yf,fs,fe,fd,ft⟩ := fp.exists_trajectory hx
  obtain ⟨yb,bs,be,bd,bt⟩ := bp.exists_trajectory hx
  obtain ⟨y,left,right,ode⟩ := join_physical_clocks pos (bs.trans fs.symm) fd bd
  refine ⟨y,(right ⟨le_rfl,pos⟩).trans fs,?_,?_,ode,?_,?_⟩
  · rw [left ⟨le_rfl,neg_nonpos.mpr pos⟩]
    simpa using be
  · rw [right ⟨pos,le_rfl⟩]
    exact fe
  · intro slab hs t ht
    rw [right (fp.subinterval hs ht)]
    exact ft slab hs t ht
  · intro slab hs t ht
    have tmem := bp.subinterval hs ht
    rw [left ⟨neg_le_neg tmem.2,neg_nonpos.mpr tmem.1⟩]
    simpa using bt slab hs t ht

/-- A physical launch from nested Q-16 surfaces followed by a single signed trace. -/
def BirthPassage (n : ℕ) (fexit bexit : State) (frows brows : List Step) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    ∀ φ : ℝ, |φ| ≤ 1 / 2^19 →
      ∃ (sign : ℝ) (approach : ℝ → DommaschkBounceField.State),
        |sign| = 1 ∧ φ + sign * |φ| = 0 ∧ approach 0 = birth uC zC uA zA (47/100) φ ∧
        (∀ t ∈ Icc 0 |φ|, HasDerivWithinAt approach
          (DommaschkBounceField.physicalFlow φ sign t (approach t)) (Icc 0 |φ|) t) ∧
        SignedTrace n fexit bexit frows brows (coordinates.symm (approach |φ|))

/-- The same physical approach supplies the initial state for both certified prefixes. -/
theorem birthPassage {n : ℕ} {fexit bexit : State} {frows brows : List Step}
    (f : Direction 1 n fexit frows) (b : Direction (-1) n bexit brows) :
    BirthPassage n fexit bexit frows brows := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entries⟩ := exists_nested_section_entry
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ hp => ?_⟩
  have enter := entries .q0r470 φ (by
    simpa [MirrorEndpoint.width,MirrorEndpoint.opposite,azimuth] using hp)
  obtain ⟨sign,approach,hs,ha,hb,ode,inside⟩ := enter
  simp only [MirrorEndpoint.opposite,azimuth,Bool.false_eq_true,↓reduceIte,sub_zero]
    at ha ode inside
  have member : coordinates.symm (approach |φ|) ∈ stateSet (MirrorEndpoint.start .q0r470) :=
    (mem_stateSet_identity (by rfl) _).mpr inside
  have radius : MirrorEndpoint.radius .q0r470 = 47/100 := by norm_num [MirrorEndpoint.radius]
  exact ⟨sign,approach,hs,ha,radius ▸ hb,ode,signedTrace f b member⟩

end PlasmaLean.Design.DommaschkBackwardPairedPrefix
