module
public import RadialFieldLineContinuationCache.DommaschkRadialFlowOnSUFFIX
public import PlasmaLean.Design.FACE_MODULE

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.FACE_MODULEOnSUFFIX
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch
open DommaschkLowerActionPath (regions)
open DommaschkEndpointMirrorBranch DommaschkQ0R478MirrorBranch327 DommaschkPhaseZeroRegularBirth
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkCommonEndpointTracesSUFFIX (checkpoint all_from_entry)
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkNativeWellAction
open FACE_MODULE
set_option maxHeartbeats 3200000
set_option maxRecDepth 65536
set_option linter.style.longLine false

theorem from_entries {uC zC uA zA : FA} {φ : ℝ} (small : |φ| ≤ 1/2^19)
    (entryI : SectionEntry .q0r470 uC zC uA zA φ) (entryO : SectionEntry .q0r478 uC zC uA zA φ) :
    FACE_PROPERTY uC zC uA zA φ := by
ENDPOINT_WITNESSES
  exact of_endpoint_witnesses
    ⟨by linarith [(abs_le.mp small).1],by linarith [(abs_le.mp small).2]⟩ py pz bornI bornO
    innerWell outerWell (Icc_subset_Icc (by linarith [hl.1]) (by linarith [hr.2]))
    (Icc_subset_Icc (by linarith [hL.1]) (by linarith [hR.2])) INNER_BOUND OUTER_BOUND

theorem from_nested_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ : ℝ, |φ| ≤ 1/2^19 →
      DommaschkRadialSectionAction.Entries uC zC uA zA φ ∧
      DommaschkRadialFlowOnSUFFIX.FromRadialPassages uC zC uA zA φ ∧ FACE_PROPERTY uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,entries,tiles⟩ := DommaschkRadialRibbonEntry.from_nested_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ?_⟩
  have left := entries .q0r470 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small)
  have right := entries .q0r478 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small)
  exact ⟨fun u => tiles u u.2 φ small,DommaschkRadialFlowOnSUFFIX.from_entries small left right,
    from_entries small left right⟩

end PlasmaLean.Design.FACE_MODULEOnSUFFIX
