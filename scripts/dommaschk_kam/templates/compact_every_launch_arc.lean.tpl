module
public import PlasmaLean.Design.DommaschkEnclosedLaunchArcs
public import CommonLaunchPhaseCache.$PHASE

/-! # One guiding-centre time across every actual launch's whole central field-line arc -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.$NAME
open Set Certificates.PositionFrameSlabs DommaschkPhaseZeroRegularBirth DommaschkSignedTraceDomain
open DommaschkEnclosedLaunchArcs DommaschkCompactLittlejohnArc DommaschkCompactLaunchPhases
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 DommaschkKamC KamNewton
open DommaschkMirrorLaunch
open $FAMILY (checkpoint)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false

abbrev angles := Icc (-(1/2^19):ℝ) (1/2^19)
abbrev central := Icc (-(316/64):ℝ) (316/64)
def allPositions (Y : angles → ℝ → Plane) : Set Fields.Space :=
  ⋃ φ : angles, DommaschkFirstMirrorWell.point (Y φ) '' central

/-- A family of genuine pilot trajectories, with one trajectory for each admitted original
launch, shares the same positive local time across all of their central arcs and velocity lifts. -/
theorem every_arc :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      Uniform (location uC zC uA zA (47/100) '' angles) ∧
      ∃ Y : angles → ℝ → Plane, (∀ φ, ∃ x,
        Y φ φ = coordinates.symm (birth uC zC uA zA (47/100) φ) ∧
        DommaschkSignedObservable.Path (checkpoint .q0r470).length
          (checkpoint .q0r470).forwardExit (checkpoint .q0r470).backwardExit
          (checkpoint .q0r470).forwardRows (checkpoint .q0r470).backwardRows x (Y φ) ∧
        Population (316/64) (Y φ)) ∧ Simultaneous (allPositions Y) := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,uniform,actual⟩ := $PHASE.original_phases
  have each (φ : angles) := actual φ (abs_le.mpr φ.2)
  choose x Y source path populations using each
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,uniform,Y,
    fun φ => ⟨x φ,source φ,path φ,populations φ⟩,?_⟩
  apply uniform_enclosed
  · let j : angles := ⟨0,by constructor <;> norm_num⟩
    exact ⟨_,mem_iUnion.mpr ⟨j,0,by constructor <;> norm_num,rfl⟩⟩
  · intro v inside
    obtain ⟨j,⟨t,ht,rfl⟩⟩ := mem_iUnion.mp inside
    have reg := on_path (path j) (by change 0 < 391; norm_num) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) rfl rfl
    have atTime := reg t (by change -(391:ℝ)/64 ≤ t ∧ t ≤ 391/64
                             constructor <;> linarith [ht.1,ht.2])
    exact ⟨((Y j t) 0,t,(Y j t) 1),⟨atTime.1,ht,abs_le.mp atTime.2⟩,rfl⟩
  · intro v inside
    obtain ⟨j,⟨t,ht,rfl⟩⟩ := mem_iUnion.mp inside
    exact ((populations j).1 t ht).2.2.1

end PlasmaLean.Design.$NAME
