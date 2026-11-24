module
public import PlasmaLean.Design.DommaschkJointLaunchArcs
public import PlasmaLean.Design.DommaschkCommonPilotObservables
public import SecondaryRegularBirthCache.DommaschkQ0R478RegularBirths

/-! # A common guiding-centre time across both phase-zero radii and every launch angle -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJointRegularLaunchArcs
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointTraceFamily
open DommaschkJointLaunchArcs DommaschkEnclosedLaunchArcs DommaschkPhaseZeroRegularBirth
open DommaschkCommonPilotObservables DommaschkSignedObservable DommaschkSignedTraceDomain
open DommaschkLowerActionPath DommaschkQ0R478MirrorBranch327 DommaschkKamC KamNewton
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

abbrev angles := Icc (-(1/2^19):ℝ) (1/2^19)

def Actual (p s : Checkpoint) (Q : ℝ → (ℝ → Plane) → Prop) (uC zC uA zA : FA)
    (φ : angles) (y z : ℝ → Plane) : Prop :=
  y φ = coordinates.symm (birth uC zC uA zA (47/100) φ) ∧ Q φ y ∧
    (∃ x, DommaschkSignedObservable.Path p.length p.forwardExit p.backwardExit p.forwardRows p.backwardRows x y) ∧
    z φ = coordinates.symm (birth uC zC uA zA (239/500) φ) ∧
    Signed (MirrorEndpoint.start .q0r478) s.forwardRows s.backwardRows (s.length/64) z

def Joint (c : MirrorEndpoint → Checkpoint) (Q : ℝ → (ℝ → Plane) → Prop) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∃ Y Z : angles → ℝ → Plane, (∀ φ, Actual (c .q0r470) (c .q0r478) Q uC zC uA zA φ (Y φ) (Z φ) ∧
      Admitted (316/64) (Y φ) ∧ Admitted (317/64) (Z φ)) ∧
      Simultaneous (arcUnion (fun _ : angles => 316/64) Y ∪ arcUnion (fun _ : angles => 317/64) Z)

set_option maxRecDepth 65536 in
theorem from_family {c : MirrorEndpoint → Checkpoint} {Q : ℝ → (ℝ → Plane) → Prop}
    (family : DommaschkCommonPilotObservables.Common c (fun φ y => Q φ y ∧ Population (316/64) y))
    (first : 316 ≤ (c .q0r470).length) (second : 327 < (c .q0r478).length)
    (lengths : ∀ e, (c e).forwardRows.length = (c e).length ∧ (c e).backwardRows.length = (c e).length)
    (rf : (c .q0r470).forwardRows.all packed = true) (rb : (c .q0r470).backwardRows.all packed = true)
    (sf : (c .q0r478).forwardRows.all packed = true) (sb : (c .q0r478).backwardRows.all packed = true)
    {F G : List Step} (frows : (c .q0r478).forwardRows = fwdRows ++ F)
    (brows : (c .q0r478).backwardRows = backRows ++ G) : Joint c Q := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,each,pilot⟩ := family
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,?_⟩
  let _ : Nonempty angles := ⟨⟨0,by constructor <;> norm_num⟩⟩
  apply two_families (by norm_num) (by norm_num)
  intro φ
  have small : |(φ:ℝ)| ≤ 1/2^19 := abs_le.mpr φ.2
  obtain ⟨x,y,born,path,obs,pop⟩ := pilot φ small
  have pass := each .q0r478 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small)
  have n0 : (316:ℝ) ≤ (c .q0r470).length := by exact_mod_cast first
  have n1 : (327:ℝ) < (c .q0r478).length := by exact_mod_cast second
  obtain ⟨z,bornZ,signed,popZ⟩ := DommaschkQ0R478RegularBirths.from_passage small pass
    (by linarith) (lengths _).1 (lengths _).2 sf sb frows brows
  have signedY := signed_of_clock path path.forward path.backward
  have regY := regions signedY.forward signedY.backward (by omega : 0 < (c .q0r470).length)
    (lengths _).1 (lengths _).2 rf rb
  have regZ := regions signed.forward signed.backward (by omega : 0 < (c .q0r478).length)
    (lengths _).1 (lengths _).2 sf sb
  refine ⟨y,z,⟨born,obs,⟨x,path⟩,bornZ,signed⟩,⟨pop,?_⟩,⟨popZ,?_⟩⟩
  · intro t ht
    exact regY t ⟨by linarith [ht.1],by linarith [ht.2]⟩
  · intro t ht
    exact regZ t ⟨by linarith [ht.1],by linarith [ht.2]⟩

end PlasmaLean.Design.DommaschkJointRegularLaunchArcs
