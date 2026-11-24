module
public import TopHeightSecantCache.PARENT
public import PlasmaLean.Design.DommaschkRadialActionAlternative

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.NAME
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkPhaseZeroRegularBirth
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkRadialActionAlternative PARENT

/-- An interpolating capped family need only identify its two endpoint trajectories. -/
theorem of_secant {y z : ℝ → Plane} (bounded : UpperSecant y z) : OnInterpolations y z := by
  obtain ⟨l, _, r, _, L, _, R, _, pilot, outer, _, _, low, high, _⟩ := bounded
  exact of_endpoint_wells pilot outer low high

theorem from_common_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC)
      DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA)
      DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ : ℝ, |φ| ≤ 1/2^19 → ∃ y z : ℝ → Plane,
      y φ = coordinates.symm (birth uC zC uA zA (47/100) φ) ∧
      z φ = coordinates.symm (birth uC zC uA zA (239/500) φ) ∧
      UpperSecant y z ∧ OnInterpolations y z := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,pick⟩ := PARENT.from_common_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ?_⟩
  obtain ⟨y,z,byl,_,byr,_,_,bounds⟩ := pick φ small
  exact ⟨y,z,byl,byr,bounds,of_secant bounds⟩

end PlasmaLean.Design.NAME
