/-
Axiom check for heavy certificates kept out of the default build (on-demand top modules).
Build the top modules first, `lake build PlasmaLean.Design.RationalStellaratorGCEwFamily`,
`lake build PlasmaLean.Design.RationalStellaratorGCMuWide`,
`lake build PlasmaLean.Design.RationalStellaratorGCMuQuarter` and
`lake build PlasmaLean.Design.CoilKamCert`, `lake build PlasmaLean.Design.DommaschkKamCAdm`, `lake build PlasmaLean.Design.DommaschkKamCConsts`,
`lake build PlasmaLean.Design.DommaschkKamCContract`,
`lake build PlasmaLean.Design.DommaschkKamCRes`, `lake build PlasmaLean.Design.DommaschkKamCFinal`,
`lake build PlasmaLean.Design.DommaschkKamCQSTransfer`, `lake build PlasmaLean.Design.DommaschkKamCQSIdent`, `lake build PlasmaLean.Design.DommaschkKamCQS`, `lake build PlasmaLean.Design.DommaschkKamCQSL2`, `lake build PlasmaLean.Design.DommaschkKamNested`, `lake build PlasmaLean.Design.DommaschkKamEmbedded`
(bounded, dependencies first),
then run `lake env lean scripts/check_axioms_heavy.lean`.

Like `scripts/check_axioms.lean`, this script **fails** if any declaration covered by it depends
on an axiom other than `propext`, `Classical.choice` and `Quot.sound` (so `sorryAx`,
`Lean.ofReduceBool`, native `bv_decide` axioms and project axioms are rejected).

Exactly what is covered: the declarations of the modules whose FIRST name component is
`PlasmaLean` (the test is component-wise, ``(`PlasmaLean).isPrefixOf``), in the import closure of
the imports listed below. Not covered: modules of the `PlasmaLeanMeta` library (its first
component is `PlasmaLeanMeta`, so its meta code, the certificate tactics included, is not
audited here; the terms those tactics produce inside `PlasmaLean` modules are); modules that
are not in the import closure of the list below; and the option `debug.skipKernelTC`, which
leaves no axiom behind and is not detected by an axiom check.
-/
import PlasmaLean.Design.RationalStellaratorGCEwFamily
import PlasmaLean.Certificates.DyadicTaylorCover
import PlasmaLean.Design.DommaschkReflectedProjectedTrial
import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
import PlasmaLean.Design.DommaschkMirrorBracketSlab
import PlasmaLean.Certificates.PositionFrameObservables
import PlasmaLean.Design.DommaschkSublevelActionGrids
import PlasmaLean.Design.DommaschkPreMirrorSigns
import PlasmaLean.Design.DommaschkSignedObservable
import PlasmaLean.Design.DommaschkSublevelArchiveNodes
import PlasmaLean.Design.DommaschkSpeedHistogramQ0R470
import PlasmaLean.Design.DommaschkSpeedHistogramQ0R478
import PlasmaLean.Design.DommaschkSpeedHistogramQ0R523
import PlasmaLean.Design.DommaschkSpeedHistogramQ0R531
import PlasmaLean.Design.DommaschkSpeedHistogramQ1R456
import PlasmaLean.Design.DommaschkSpeedHistogramQ1R464
import PlasmaLean.Design.DommaschkSpeedHistogramQ1R509
import PlasmaLean.Design.DommaschkSpeedHistogramQ1R517
import PlasmaLean.Design.DommaschkOppositeHarmonic
import PlasmaLean.Design.DommaschkPerturbedFieldModel
import PlasmaLean.Design.DommaschkUniformFieldError
import PlasmaLean.Design.DommaschkPhysicalActionCap
import PlasmaLean.Design.DommaschkReflectedPilot
import PlasmaLean.Design.DommaschkBackwardRectangle
import PlasmaLean.Design.DommaschkEndpointSignedTrace
import PlasmaLean.Design.DommaschkArcDensitySensitivity
import PlasmaLean.Design.DommaschkFirstMirrorWell
import PlasmaLean.Design.DommaschkFirstMirrorActionFloor
import PlasmaLean.Design.DommaschkSignedBirthApproach
import PlasmaLean.Design.DommaschkFirstMirrorBounceTime
import PlasmaLean.Design.DommaschkMirrorBandPassage
import PlasmaLean.Design.DommaschkMirrorBirthArea
import PlasmaLean.Design.DommaschkMirrorFlightBounds
import PlasmaLean.Design.DommaschkMirrorBandFlightIdentity
import PlasmaLean.Design.DommaschkSharpFlightBounds
import PlasmaLean.Design.DommaschkFullBandFlightBounds
import PlasmaLean.Design.DommaschkRowFlightBudget
import PlasmaLean.Design.DommaschkActionHeightInverse
import PlasmaLean.Design.DommaschkNativeWellAction
import PlasmaLean.Design.DommaschkCartesianMirrorBirth
import PlasmaLean.Design.DommaschkTrappedBirthCoordinates
import PlasmaLean.Design.DommaschkActionFlightFloor
import PlasmaLean.Design.DommaschkSignedTracePrefix
import PlasmaLean.Design.DommaschkPhysicalCentralJet
import PlasmaLean.Design.DommaschkCommonLittlejohnTime
import PlasmaLean.Design.DommaschkLocalLittlejohnBirth
import PlasmaLean.Design.DommaschkGroupedMirrorModels
import PlasmaLean.Design.DommaschkEndpointMirrorBranch
import PlasmaLean.Design.DommaschkEndpointTraceFamily
import PlasmaLean.Design.DommaschkCenteredStrength
import PlasmaLean.Design.DommaschkLowerActionWindows
import PlasmaLean.Design.DommaschkSubmirrorPrefixObservation
import PlasmaLean.Design.DommaschkLowerActionPath
import PlasmaLean.Design.DommaschkGroupedProfileCompare
import PlasmaLean.Design.DommaschkGroupGapRadius
import PlasmaLean.Design.DommaschkGroupedHarmonicGap
import PlasmaLean.Design.DommaschkComparedTracePrefixes
import PlasmaLean.Design.DommaschkSecondaryActionCore
import PlasmaLean.Design.DommaschkPairedArcRatio
import PlasmaLean.Design.DommaschkNativePairedProfiles
import PlasmaLean.Design.DommaschkOppositeMirrorExclusion
import PlasmaLean.Design.DommaschkPairedActionBirth
import PlasmaLean.Design.DommaschkCommonPilotObservables
import PlasmaLean.Design.DommaschkPilotBirthVariation
import PlasmaLean.Design.DommaschkFiniteRadialAction
import PlasmaLean.Design.DommaschkRadialActionCriterion
import PlasmaLean.Design.DommaschkToroidalEnvelopeTest
import PlasmaLean.Design.DommaschkEndpointContinuation
import PlasmaLean.Design.DommaschkNativeActionReflection
import PlasmaLean.Design.DommaschkNativeActionColumns
import PlasmaLean.Design.DommaschkNativeActionControls
import PlasmaLean.Certificates.NativeActionArchivePair
import PlasmaLean.Certificates.MirrorActionBlockBounds
import PlasmaLean.Design.DommaschkReflectedActionBounds
import PlasmaLean.Certificates.MirrorActionUniformCells
import PlasmaLean.Design.DommaschkPhysicalArcTrace
import PlasmaLean.Design.DommaschkCompensatedAction
import PlasmaLean.Design.DommaschkSignedMirrorSlope
import PlasmaLean.Design.DommaschkMirrorStrengthSlope
import PlasmaLean.Design.RationalStellaratorGCMuWide
import PlasmaLean.Design.RationalStellaratorGCMu3Confined
import PlasmaLean.Design.RationalStellaratorGCMu4Confined
import PlasmaLean.Design.RationalStellaratorGCMu5Confined
import PlasmaLean.Design.RationalStellaratorGCMuQuarter
import PlasmaLean.Design.CoilKamCert
import Lean.Util.CollectAxioms
import PlasmaLean.Design.DommaschkKamCAdm
import PlasmaLean.Design.DommaschkKamCConsts
import PlasmaLean.Design.DommaschkKamCContract
import PlasmaLean.Design.DommaschkKamCRes
import PlasmaLean.Design.DommaschkKamCFinal
import PlasmaLean.Design.DommaschkKamCQSTransfer
import PlasmaLean.Design.DommaschkKamCQSIdent
import PlasmaLean.Design.DommaschkKamCQS
import PlasmaLean.Design.DommaschkKamCQSL2
import PlasmaLean.Design.DommaschkKamNested
import PlasmaLean.Design.DommaschkKamQ16
import PlasmaLean.Design.DommaschkKamEmbedded
import PlasmaLean.Design.DommaschkKamLoopCurrent
import PlasmaLean.Design.DommaschkInterfaceArcWitness
import PlasmaLean.Design.DommaschkInterfaceFundamentalForms
import PlasmaLean.Design.DommaschkActionQuadrature
import PlasmaLean.Design.DommaschkLocalMirrorGraphs
import PlasmaLean.Design.DommaschkMirrorSectorFlow
import PlasmaLean.Design.DommaschkBounceObservables
import PlasmaLean.Design.DommaschkMirrorFirstPassage
import PlasmaLean.Design.DommaschkMirrorTwoSlabs
import PlasmaLean.Design.DommaschkMirrorBidirectional
import PlasmaLean.Design.DommaschkMirrorTwoSided
import PlasmaLean.Design.DommaschkBackwardPairedPrefix
import PlasmaLean.Design.DommaschkProjectedTrial
import PlasmaLean.Design.DommaschkReflectedBack001
import PlasmaLean.Design.DommaschkJacobianForward042
import PlasmaLean.Design.DommaschkStoredPowers
import PlasmaLean.Design.DommaschkHarmonicTrace
import PlasmaLean.Design.DommaschkBounceTaylorFirst
import PlasmaLean.Design.DommaschkReferenceFirstDefect
import PlasmaLean.Design.DommaschkPhysicalJacobian
import PlasmaLean.Design.DommaschkJacobianFirstBound
import PlasmaLean.Design.DommaschkTraceResidualBack000
import PlasmaLean.Design.DommaschkTraceResidualForward390
import PlasmaLean.Certificates.PositionFrameChain
import PlasmaLean.Theory.Fields.MovingFrameSlabs
import PlasmaLean.Design.DommaschkRadialSlabsS0H0
import PlasmaLean.Design.DommaschkRadialSlabsS0H1
import PlasmaLean.Design.DommaschkRadialSlabsS1H0
import PlasmaLean.Design.DommaschkRadialSlabsS1H1
import PlasmaLean.Design.DommaschkSecondaryActionHeight
import PlasmaLean.Design.DommaschkPairedFirstWellAction
import PlasmaLean.Certificates.CoarseActionCells
import PlasmaLean.Design.DommaschkCoarseActionPhase
import PlasmaLean.Design.DommaschkSecondaryHeightCollar
import PlasmaLean.Design.DommaschkIncomingHeightAction
import PlasmaLean.Certificates.WeakenLowerActionCells
import PlasmaLean.Design.DommaschkPhaseZeroRegularBirth
import PlasmaLean.Design.DommaschkCompactLittlejohnArc
import PlasmaLean.Certificates.WeakenLowerActionCover
import PlasmaLean.Design.DommaschkGroupedTrialJet
import PlasmaLean.Design.DommaschkEnclosedLaunchArcs
import PlasmaLean.Design.DommaschkOriginalBirthMargin
import PlasmaLean.Certificates.ActionFloorShells
import PlasmaLean.Design.DommaschkFirstContactHeightBudget
import PlasmaLean.Design.DommaschkJointLaunchArcs
import PlasmaLean.Certificates.MirrorGapAtTime
import PlasmaLean.Design.DommaschkClosedBandAction
import PlasmaLean.Design.DommaschkPilotArcLengthPacket
import PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues
import PlasmaLean.Design.DommaschkVariableHorner
import PlasmaLean.Design.DommaschkRadialActionAlternative
import PlasmaLean.Design.DommaschkFirstMirrorHeightSampling
import PlasmaLean.Design.DommaschkRadialRibbonEntry
import PlasmaLean.Design.DommaschkRadialFamilyContinuity
import PlasmaLean.Design.DommaschkRadialSectionAction
import PlasmaLean.Certificates.PositionFrameWide
import PlasmaLean.Design.DommaschkWideTraceFields
import PlasmaLean.Design.DommaschkRibbonThroughChains
import PlasmaLean.Design.DommaschkRibbonGrazingAlternative
import PlasmaLean.Design.DommaschkRibbonSlopeCover
import PlasmaLean.Design.DommaschkDyadicHorner
import PlasmaLean.Design.DommaschkSectorAction
import PlasmaLean.Design.DommaschkRadialAccessibleBirth
import PlasmaLean.Design.DommaschkSectorFaces

/-! Audit all declarations owned by project modules in the import closure (the on-demand top
modules and everything they import). Fails on any non-standard axiom. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => (`PlasmaLean).isPrefixOf env.allImportedModuleNames[idx.toNat]!
      | none => false
    if owned then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations found: audit did not run"
  logInfo m!"Heavy axiom audit passed for {checked} PlasmaLean declarations."

#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_confined_forever_energy_window
#print axioms PlasmaLean.Design.RationalStellaratorGC.alphaEwVel_volume_pos
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_ew_confined_forever_velocity_set
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_passing_confined_forever_wide
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu2.rationalStellarator_gc_mu_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu3.rationalStellarator_gc_mu_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu4.rationalStellarator_gc_mu_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu5.rationalStellarator_gc_mu_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGC.quarter_cells_cover
#print axioms PlasmaLean.Design.RationalStellaratorGC.quarter_passing_margin
#print axioms PlasmaLean.Design.RationalStellaratorGC.rationalStellarator_gc_mu_confined_forever_quarter
#print axioms PlasmaLean.Design.RationalStellaratorGC.gc_mu_passing_confined_forever_SI_quarter
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_passing_confined_forever_quarter
#print axioms PlasmaLean.Design.CoilKam.coilTorus_resR_Bd
#print axioms PlasmaLean.Design.CoilKam.coilTorus_resZ_Bd
#print axioms PlasmaLean.Design.DommaschkKamC.dk_adm
#print axioms PlasmaLean.Design.DommaschkKamC.dk_hadm
#print axioms PlasmaLean.Design.DommaschkKamC.AdmO.toG
#print axioms PlasmaLean.Design.DommaschkKamC.ballA_all
#print axioms PlasmaLean.Design.DommaschkKamC.eval_polyT
#print axioms PlasmaLean.Design.DommaschkKamC.polyT_reject
#print axioms PlasmaLean.Design.DommaschkKamC.consts_sharp
#print axioms PlasmaLean.Design.DommaschkKamC.dk_globalHG
#print axioms PlasmaLean.Design.DommaschkKamC.dk_kamHG
#print axioms PlasmaLean.Design.DommaschkKamC.dk_exact_of_res
#print axioms PlasmaLean.Design.DommaschkKamC.cDK_ok
#print axioms PlasmaLean.Design.DommaschkKamC.dk_small_fails
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_C1
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_iotaOnTorus
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_C1_of_exact
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.iotaOnTorus
#print axioms PlasmaLean.Design.DommaschkKamC.not_C1_iotaMin
#print axioms PlasmaLean.Design.DommaschkKamC.radial_ge_of_close
#print axioms PlasmaLean.Design.DommaschkKamC.Bd_radQ_surr
#print axioms PlasmaLean.Design.DommaschkKamC.radQ_surr_ne
#print axioms PlasmaLean.Design.DommaschkKamC.thProj_mode
#print axioms PlasmaLean.Design.DommaschkKamC.dk_e0R
#print axioms PlasmaLean.Design.DommaschkKamC.dk_e0Z
#print axioms PlasmaLean.Design.DommaschkKamC.ballH_all
#print axioms PlasmaLean.Design.DommaschkKamC.kron_gridR
#print axioms PlasmaLean.Design.DommaschkKamC.Bd_ctr_of_node
#print axioms PlasmaLean.Design.DommaschkKamC.e0q_not_tiny
#print axioms PlasmaLean.Design.DommaschkKamC.fldZ_reject
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_C1_unconditional
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_iotaOnTorus_unconditional
#print axioms PlasmaLean.Design.DommaschkKamC.qsd_bounds
#print axioms PlasmaLean.Design.DommaschkKamC.QSDefBounds.pointwise
#print axioms PlasmaLean.Design.DommaschkKamC.qsd_defect_real
#print axioms PlasmaLean.Design.DommaschkKamC.qsd_numbers
#print axioms PlasmaLean.Design.DommaschkKamC.qsd_near
#print axioms PlasmaLean.Design.DommaschkKamC.qsdMj_spec
#print axioms PlasmaLean.Design.DommaschkKamC.ballQ_all
#print axioms PlasmaLean.Design.DommaschkKamC.surr_G
#print axioms PlasmaLean.Design.DommaschkKamC.surr_F
#print axioms PlasmaLean.Design.DommaschkKamC.surr_G_ne
#print axioms PlasmaLean.Design.DommaschkKamC.qsNg_instance
#print axioms PlasmaLean.Design.DommaschkKamC.qsd_not_tiny
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.torusQADefect_eq
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.boozerChartHyp'
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.torusQADefectLe_delta
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.oracleDefect_le
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.torusPot_add_pi
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_qaDefect
#print axioms PlasmaLean.Design.DommaschkKamC.not_torusPeriodic_four
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_C1_qaDefect
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_C1_oracleDefect
#print axioms PlasmaLean.Design.DommaschkKamC.oracleDefect_bound_num
#print axioms PlasmaLean.Design.DommaschkKamC.dommaschk_C1_oracleDefect_L2
#print axioms PlasmaLean.Design.DommaschkKamC.oracleDefect_L2_num
#print axioms PlasmaLean.Design.DommaschkKamC.torusAvg_eval_psi
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.four_mul_sqJ_eq
#print axioms PlasmaLean.Design.DommaschkKamC.ExactTorusC.weightedL2Sq_le_mF
#print axioms PlasmaLean.Design.DommaschkKamC.l2_numbers
#print axioms PlasmaLean.Design.DommaschkKamC.not_l2_tiny
#print axioms PlasmaLean.Design.DommaschkKamC.torusAvg_eval_psi_one
#print axioms PlasmaLean.Design.DommaschkKamA.dk_adm
#print axioms PlasmaLean.Design.DommaschkKamA.dk_e0R
#print axioms PlasmaLean.Design.DommaschkKamA.dk_e0Z
#print axioms PlasmaLean.Design.DommaschkKamA.dk_globalHG
#print axioms PlasmaLean.Design.DommaschkKamA.dommaschkA_C1_unconditional
#print axioms PlasmaLean.Design.DommaschkKamA.dommaschkA_iotaOnTorus_unconditional
#print axioms PlasmaLean.Design.DommaschkKamA.gaugeA_gt
#print axioms PlasmaLean.Design.DommaschkKamA.gaugeC_lt
#print axioms PlasmaLean.Design.DommaschkKamA.iotaqA_close
#print axioms PlasmaLean.Design.DommaschkKamA.iotaqA_ne_iotaqC
#print axioms PlasmaLean.Design.DommaschkKamA.not_C1_iotaMin_A
#print axioms PlasmaLean.Design.DommaschkKamA.pos_of_sq_mul
#print axioms PlasmaLean.Design.DommaschkKamA.radA_pos
#print axioms PlasmaLean.Design.DommaschkKamA.radC_pos
#print axioms PlasmaLean.Design.DommaschkKamNested.dommaschk_nested
#print axioms PlasmaLean.Design.DommaschkKamNested.dommaschk_nested_C1
#print axioms PlasmaLean.Design.DommaschkKamNested.nested_of_exact
#print axioms PlasmaLean.Design.DommaschkKamNested.nestedTori_circles
#print axioms PlasmaLean.Design.DommaschkKamNested.NestedTori.disjoint
#print axioms PlasmaLean.Design.DommaschkKamNested.NestedTori.inside
#print axioms PlasmaLean.Design.DommaschkKamNested.not_nested_C1_quarter
#print axioms PlasmaLean.Design.DommaschkKamNested.not_nestedTori_swap
#print axioms PlasmaLean.Design.DommaschkKamA.ExactTorusA.torusQADefectLe_delta
#print axioms PlasmaLean.Design.DommaschkKamA.ExactTorusA.torusQADefect_eq
#print axioms PlasmaLean.Design.DommaschkKamA.ExactTorusA.weightedL2Sq_le_mF
#print axioms PlasmaLean.Design.DommaschkKamA.dommaschkA_C1_qaDefect
#print axioms PlasmaLean.Design.DommaschkKamA.dommaschkA_oracleDefect
#print axioms PlasmaLean.Design.DommaschkKamA.dommaschkA_oracleDefect_L2
#print axioms PlasmaLean.Design.DommaschkKamA.l2_numbers
#print axioms PlasmaLean.Design.DommaschkKamA.not_l2_tiny
#print axioms PlasmaLean.Design.DommaschkKamA.oracleDefectA_L2_num
#print axioms PlasmaLean.Design.DommaschkKamA.qsd_bounds
#print axioms PlasmaLean.Design.DommaschkKamA.qsd_not_tiny
#print axioms PlasmaLean.Design.DommaschkKamA.qsd_numbers
#print axioms PlasmaLean.Design.DommaschkKamA.surr_G_ne
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.torusC_embedded
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.torusA_embedded
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.dommaschkC_embedded_C1
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.dommaschkA_embedded_C1
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.dommaschk_nested_embedded_C1
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.dommaschk_nested_embedded_current_eq_zero
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.dommaschk_Q16_embedded
#print axioms PlasmaLean.Design.DommaschkKamEmbedded.dommaschk_Q16_strong_embedded
#print axioms PlasmaLean.Design.DommaschkKamQ16.dommaschk_Q16_strong
#print axioms PlasmaLean.Design.DommaschkKamQ16.dommaschk_Q16_vacuum
#print axioms PlasmaLean.Design.DommaschkKamQ16.dommaschk_Q16_chart
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.candidate_imax_zero
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.exactTorusC_loopCurrent
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.exactTorusA_loopCurrent
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.exactTorusC_period
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.exactTorusA_period
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.exactTorusC_routes_agree
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.exists_fieldTorus_loopCurrent_eq_zero
#print axioms PlasmaLean.Design.DommaschkKamLoopCurrent.dommaschk_nested_current_eq_zero
#print axioms PlasmaLean.Design.DommaschkKamQ16.nested_C1_of_exact
#print axioms PlasmaLean.Design.DommaschkKamQ16.not_q16_C_tiny
#print axioms PlasmaLean.Design.DommaschkKamQ16.q16_bounds_lt_strong

#print axioms PlasmaLean.Design.KamNewton.ProfileAngle.first_error
#print axioms PlasmaLean.Design.KamNewton.ProfileAngle.second_error
#print axioms PlasmaLean.Design.DommaschkKamAInterfaceMoments.gridJet_error
#print axioms PlasmaLean.Design.DommaschkInterfaceArcBounds.obstruction_of_close
#print axioms PlasmaLean.Design.DommaschkInterfaceArcBounds.seedMargins
#print axioms PlasmaLean.Design.DommaschkInterfaceArcBounds.exactTorusA_obstruction
#print axioms PlasmaLean.Design.DommaschkInterfaceArcWitness.exists_embedded_oriented_torus_obstruction
#print axioms PlasmaLean.Design.DommaschkInterfaceArcOrientation.normal_dot_polarRay_positive
#print axioms PlasmaLean.Design.DommaschkInterfaceFundamentalForms.surface_derivatives
#print axioms PlasmaLean.Design.DommaschkInterfaceFundamentalForms.field_eq_speed_tangent
#print axioms PlasmaLean.Design.DommaschkInterfaceFundamentalForms.exactTorusA_field_normalDerivative_obstruction
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.exists_nested_collar
#print axioms PlasmaLean.Design.DommaschkBounceField.physical_trace_tangent
#print axioms PlasmaLean.Fields.TrajectorySlabs.Chain.exists_trajectory
#print axioms PlasmaLean.Fields.TrajectorySlabs.MovingFrame.step_of_defect
#print axioms PlasmaLean.Design.DommaschkLocalMirrorGraphs.sector_graphs
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.exists_nested_section_entry
#print axioms PlasmaLean.Design.DommaschkPositionFramesBack.checked
#print axioms PlasmaLean.Design.DommaschkPositionFramesFwd.checked
#print axioms PlasmaLean.Design.DommaschkHarmonicTrace.all_times
#print axioms PlasmaLean.Design.DommaschkBounceTaylorFirst.physical_clock_ranges
#print axioms PlasmaLean.Design.DommaschkReferenceFirst.framed_defect
#print axioms PlasmaLean.Certificates.PositionFrameSlabs.Chain.cartesian_trajectory
#print axioms PlasmaLean.Design.DommaschkJacobian.physical_derivative
#print axioms PlasmaLean.Design.DommaschkJacobian.physical_clock_log_norm
#print axioms PlasmaLean.Design.DommaschkTraceResidualBack000.physical_defect
#print axioms PlasmaLean.Design.DommaschkTraceResidualForward390.physical_defect
#print axioms PlasmaLean.Design.DommaschkPhysicalFirstStep.physical_first_step
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.exists_nested_firstPassage
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.exists_nested_frame_paths
#print axioms PlasmaLean.Design.DommaschkPhysicalSecondStep.physical_second_step
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.exists_nested_two_slabs
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.two_tube_error
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.exists_nested_bidirectional
#print axioms PlasmaLean.Certificates.PositionFrameProjection.coordinates_le
#print axioms PlasmaLean.Design.DommaschkPhysicalBackwardSecondStep.physical_step
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.join_physical_clocks
#print axioms PlasmaLean.Design.DommaschkMirrorLaunch.exists_nested_four_slabs
#print axioms PlasmaLean.Design.DommaschkBackwardPairedPrefix.birthPassage
#print axioms PlasmaLean.Design.DommaschkProjectedTrial.trial_membership
#print axioms PlasmaLean.Design.DommaschkReflectedBack001.physical_defect
#print axioms PlasmaLean.Design.DommaschkJacobianForward042.physical_clock_log_norm
#print axioms PlasmaLean.Design.DommaschkStoredPowers.checkedChunk
#print axioms PlasmaLean.Certificates.TrajectoryTaylorModel.dyadic_cover
#print axioms PlasmaLean.Design.DommaschkProjectedTrial.reflected_membership
#print axioms PlasmaLean.Design.DommaschkMirrorTubeCrossing.first_on_tube
#print axioms PlasmaLean.Design.DommaschkFirstMirrorLaunchSign.first_tube_below
#print axioms PlasmaLean.Design.DommaschkMirrorEndpointSign.physical_sign
#print axioms PlasmaLean.Design.DommaschkMirrorBracketSlab.hit
#print axioms PlasmaLean.Certificates.PositionFrameSlabs.first_contact_after_prefix
#print axioms PlasmaLean.Certificates.SublevelActionGrid.action_target
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q0R470.endpoint
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q0R478.endpoint
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q0R523.endpoint
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q0R531.endpoint
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q1R456.endpoint
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q1R464.endpoint
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q1R509.endpoint
#print axioms PlasmaLean.Design.DommaschkSublevelActionGrids.Q1R517.endpoint
#print axioms PlasmaLean.Design.DommaschkPreMirrorSigns.Matches.mem
#print axioms PlasmaLean.Design.DommaschkSignedObservable.Path.at_row
#print axioms PlasmaLean.Design.DommaschkSignedObservable.Path.below_on
#print axioms PlasmaLean.Design.DommaschkSignedObservable.birth_with
#print axioms PlasmaLean.Certificates.MirrorSublevelQuadrature.covers_sublevel
#print axioms PlasmaLean.Design.DommaschkSublevelArchiveNodes.Upper.node
#print axioms PlasmaLean.Design.DommaschkSublevelArchiveNodes.Lower.node
#print axioms PlasmaLean.Design.DommaschkMirrorStrengthSlope.forward_of_physical
#print axioms PlasmaLean.Design.DommaschkMirrorStrengthSlope.backward_of_physical
#print axioms PlasmaLean.Design.DommaschkMirrorStrengthSlope.at_positive_level
#print axioms PlasmaLean.Certificates.MirrorSpeedHistogram.scan_spec
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ0R470.endpoint
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ0R478.endpoint
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ0R523.endpoint
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ0R531.endpoint
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ1R456.endpoint
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ1R464.endpoint
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ1R509.endpoint
#print axioms PlasmaLean.Design.DommaschkSpeedHistogramQ1R517.endpoint
#print axioms PlasmaLean.Design.DommaschkOppositeHarmonic.first
#print axioms PlasmaLean.Design.DommaschkPhysicalPolynomialError.field_error
#print axioms PlasmaLean.Design.DommaschkPerturbedFieldModel.transfer
#print axioms PlasmaLean.Design.DommaschkUniformFieldError.dD_bound
#print axioms PlasmaLean.Design.DommaschkUniformFieldError.dnR_bound
#print axioms PlasmaLean.Design.DommaschkUniformFieldError.dnZ_bound
#print axioms PlasmaLean.Design.DommaschkSignedMirrorSlope.clock_odes
#print axioms PlasmaLean.Design.DommaschkSignedMirrorSlope.first_transverse
#print axioms PlasmaLean.Design.DommaschkPhysicalActionPanel.norm_deriv_eq_density
#print axioms PlasmaLean.Design.DommaschkPhysicalActionPanel.upper_columns
#print axioms PlasmaLean.Design.DommaschkPhysicalActionPanel.arcDensity_le_of_ranges
#print axioms PlasmaLean.Design.DommaschkPhysicalActionPanel.zero_speed_of_monotone
#print axioms PlasmaLean.Design.DommaschkReflectedPath.endpoint_trajectory
#print axioms PlasmaLean.Design.DommaschkReflectedPath.action
#print axioms PlasmaLean.Design.DommaschkReflectedPilot.archive
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.cells_of_floor
#print axioms PlasmaLean.Design.DommaschkCompensatedAction.gap_from_shift
#print axioms PlasmaLean.Design.DommaschkPhysicalActionPanel.arcDensity_on_path
#print axioms PlasmaLean.Design.DommaschkEndpointFirstSlab.common_births
#print axioms PlasmaLean.Design.DommaschkEndpointSignedTrace.first_chain
#print axioms PlasmaLean.Design.DommaschkEndpointSignedTrace.common_of_chains
#print axioms PlasmaLean.Design.DommaschkShiftedTrial.membership
#print axioms PlasmaLean.Design.DommaschkBackwardRectangle.field_bounds
#print axioms PlasmaLean.Design.DommaschkReflectedActionBounds.transfer
#print axioms PlasmaLean.Design.DommaschkArcDensitySensitivity.density_lipschitz
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.action_le_uniform
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.covers_append_iff
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.covers_of_floor
#print axioms PlasmaLean.Design.DommaschkHarmonicHorner.expand_sound
#print axioms PlasmaLean.Design.DommaschkNativeActionGeometry.compensated_numerator
#print axioms PlasmaLean.Design.DommaschkNativeActionReflection.norm
#print axioms PlasmaLean.Design.DommaschkNativeActionColumns.physical
#print axioms PlasmaLean.Design.DommaschkNativeActionControls.unreversed_record_differs
#print axioms PlasmaLean.Design.DommaschkNativeActionControls.small_root_rejected
#print axioms PlasmaLean.Design.DommaschkNativeActionControls.large_root_fails_minimality
#print axioms PlasmaLean.Certificates.NativeActionInterval.forward_cells
#print axioms PlasmaLean.Certificates.NativeActionInterval.backward_cells
#print axioms PlasmaLean.Design.DommaschkSignedTraceDomain.on_path
#print axioms PlasmaLean.Design.DommaschkSignedTraceDenominator.regular
#print axioms PlasmaLean.Design.DommaschkSignedTraceDensity.continuousOn_density_region
#print axioms PlasmaLean.Design.DommaschkSignedActionFloor.strict_floor
#print axioms PlasmaLean.Design.DommaschkFirstMirrorActionFloor.from_core
#print axioms PlasmaLean.Design.DommaschkFirstMirrorWell.identify
#print axioms PlasmaLean.Design.DommaschkSignedBirthApproach.birth_position
#print axioms PlasmaLean.Design.DommaschkSignedBirthApproach.from_birthWith
#print axioms PlasmaLean.Design.DommaschkFirstMirrorBounceTime.of_contacts
#print axioms PlasmaLean.Design.DommaschkSignedMirrorBand.attach
#print axioms PlasmaLean.Design.DommaschkSignedMirrorBand.branches
#print axioms PlasmaLean.Design.DommaschkSignedMirrorBand.Branches.first_transverse
#print axioms PlasmaLean.Design.DommaschkMirrorBandAction.family
#print axioms PlasmaLean.Design.DommaschkMirrorBandPassage.on_path
#print axioms PlasmaLean.Design.DommaschkMirrorBirthArea.rectangle_area
#print axioms PlasmaLean.Design.DommaschkMirrorBirthArea.of_passage
#print axioms PlasmaLean.Design.DommaschkEndpointContinuation.forward_rectangle
#print axioms PlasmaLean.Design.DommaschkEndpointContinuation.cons_step
#print axioms PlasmaLean.Design.DommaschkEndpointContinuation.with_pilot_of_entry
#print axioms PlasmaLean.Design.DommaschkMirrorFlightBounds.density_upper
#print axioms PlasmaLean.Design.DommaschkMirrorFlightBounds.of_passage
#print axioms PlasmaLean.Design.DommaschkMirrorBandFlightIdentity.on_path
#print axioms PlasmaLean.Design.DommaschkHarmonicBoxes.run_mem
#print axioms PlasmaLean.Design.DommaschkHarmonicBoxes.row_mem
#print axioms PlasmaLean.Design.DommaschkHarmonicBoxes.rows_mem
#print axioms PlasmaLean.Design.DommaschkHarmonicBoxes.wave_mem
#print axioms PlasmaLean.Design.DommaschkHarmonicBoxes.enclosure_mem
#print axioms PlasmaLean.Design.DommaschkToroidalEnvelope.cylBphi_lower
#print axioms PlasmaLean.Design.DommaschkToroidalEnvelope.boundary_value
#print axioms PlasmaLean.Design.DommaschkToroidalFieldBounds.strength_lower
#print axioms PlasmaLean.Design.DommaschkToroidalFieldBounds.density_upper
#print axioms PlasmaLean.Design.DommaschkToroidalFieldBounds.speed_upper
#print axioms PlasmaLean.Design.DommaschkSharpFlightBounds.half_upper
#print axioms PlasmaLean.Design.DommaschkSharpFlightBounds.of_passage
#print axioms PlasmaLean.Design.DommaschkCoreClearance.of_gap
#print axioms PlasmaLean.Design.DommaschkFullBandFlightBounds.on_path
#print axioms PlasmaLean.Design.DommaschkRowTimeClearance.of_gap
#print axioms PlasmaLean.Design.DommaschkRowTimeClearance.reciprocal_le
#print axioms PlasmaLean.Design.DommaschkRowFlightBudget.Budget.append
#print axioms PlasmaLean.Design.DommaschkRowFlightBudget.from_row
#print axioms PlasmaLean.Design.DommaschkRowFlightBudget.complete
#print axioms PlasmaLean.Design.DommaschkActionHeightInverse.of_identity
#print axioms PlasmaLean.Design.DommaschkActionHeightInverse.endpoint_width
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.exact_upper_mass
#print axioms PlasmaLean.Design.DommaschkActionArchiveMass.integer_mass
#print axioms PlasmaLean.Design.DommaschkActionArchiveMass.target_gap
#print axioms PlasmaLean.Design.DommaschkActionArchiveMass.closed_upper
#print axioms PlasmaLean.Design.DommaschkNativeWellAction.continuous_inputs
#print axioms PlasmaLean.Design.DommaschkNativeWellAction.first_well
#print axioms PlasmaLean.Design.DommaschkCartesianAngleFlow.isOpen_regular
#print axioms PlasmaLean.Design.DommaschkCartesianAngleFlow.velocity_smooth
#print axioms PlasmaLean.Design.DommaschkCartesianAngleFlow.strength_smooth
#print axioms PlasmaLean.Design.DommaschkCartesianAngleFlow.aligned
#print axioms PlasmaLean.Design.DommaschkCartesianAngleFlow.cartesian_ode
#print axioms PlasmaLean.Design.DommaschkCartesianMirrorBirth.flow_bracket
#print axioms PlasmaLean.Design.DommaschkCartesianMirrorBirth.neighborhood
#print axioms PlasmaLean.Design.DommaschkTrappedBirthCoordinates.strict_at_birth
#print axioms PlasmaLean.Design.DommaschkTrappedBirthCoordinates.from_path
#print axioms PlasmaLean.Design.DommaschkSignedObservable.Path.take_through
#print axioms PlasmaLean.Kinetic.MirrorActionEnvelope.LaunchWell.time_floor_of_action_cap
#print axioms PlasmaLean.Design.DommaschkActionFlightFloor.of_passage
#print axioms PlasmaLean.Design.DommaschkActionFlightFloor.join_bounds
#print axioms PlasmaLean.Design.DommaschkPhysicalCentralJet.of_memberships
#print axioms PlasmaLean.Design.DommaschkRadialActionCriterion.slope_gt_third
#print axioms PlasmaLean.Design.DommaschkRadialActionCriterion.at_first_well
#print axioms PlasmaLean.Design.DommaschkEndpointTraceFamily.common_of_entry
#print axioms PlasmaLean.Design.DommaschkEndpointTraceFamily.pilot_chain
#print axioms PlasmaLean.Design.DommaschkEndpointTraceFamily.pilot_from_entry
#print axioms PlasmaLean.Design.DommaschkLocalLittlejohnBirth.parallel
#print axioms PlasmaLean.Design.DommaschkLocalLittlejohnBirth.interior_of_reference
#print axioms PlasmaLean.Design.DommaschkLocalLittlejohnBirth.from_path
#print axioms PlasmaLean.Design.DommaschkGroupedMirrorModels.Fits.mem
#print axioms PlasmaLean.Design.DommaschkGroupedMirrorModels.Covers.below
#print axioms PlasmaLean.Design.DommaschkEndpointMirrorBranch.of_joined
#print axioms PlasmaLean.Design.DommaschkEndpointMirrorBranch.branch
#print axioms PlasmaLean.Design.DommaschkCommonLittlejohnTime.from_path
#print axioms PlasmaLean.Design.DommaschkCommonLittlejohnTime.UniformAt.band
#print axioms PlasmaLean.Design.DommaschkFiniteRadialAction.height_scale
#print axioms PlasmaLean.Design.DommaschkFiniteRadialAction.endpoint_width
#print axioms PlasmaLean.Design.DommaschkFiniteRadialAction.first_action
#print axioms PlasmaLean.Design.DommaschkFiniteRadialAction.pair_test
#print axioms PlasmaLean.Design.DommaschkBirthVariation.birth_derivative
#print axioms PlasmaLean.Design.DommaschkBirthVariation.geometry
#print axioms PlasmaLean.Design.DommaschkBirthVariation.pilot_numerators
#print axioms PlasmaLean.Design.DommaschkBirthVariation.observable_slopes
#print axioms PlasmaLean.Design.DommaschkBirthVariation.pilot_of_close
#print axioms PlasmaLean.Design.DommaschkBirthVariation.line_of_section
#print axioms PlasmaLean.Design.DommaschkBirthVariation.common_pilot
#print axioms PlasmaLean.Design.DommaschkCommonPilotObservables.of_paths
#print axioms PlasmaLean.Design.DommaschkPairedActionProfiles.field_range
#print axioms PlasmaLean.Design.DommaschkPairedActionProfiles.weight_range
#print axioms PlasmaLean.Design.DommaschkPairedActionProfiles.compare_ranges
#print axioms PlasmaLean.Design.DommaschkPairedActionBirth.Launch.weight
#print axioms PlasmaLean.Design.DommaschkPairedActionBirth.from_launch
#print axioms PlasmaLean.Design.DommaschkCenteredStrength.mean_value
#print axioms PlasmaLean.Design.DommaschkCenteredStrength.physical_derivative
#print axioms PlasmaLean.Design.DommaschkCenteredStrength.centered
#print axioms PlasmaLean.Design.DommaschkCenteredStrength.compare
#print axioms PlasmaLean.Design.DommaschkOppositeMirrorExclusion.FitsRow.below
#print axioms PlasmaLean.Design.DommaschkOppositeMirrorExclusion.from_passage
#print axioms PlasmaLean.Design.DommaschkPairedArcRatio.physical_identity
#print axioms PlasmaLean.Design.DommaschkPairedArcRatio.compare
#print axioms PlasmaLean.Design.DommaschkPairedArcRatio.compared_of_squared
#print axioms PlasmaLean.Design.DommaschkNativePairedProfiles.native_weight_identity
#print axioms PlasmaLean.Design.DommaschkNativePairedProfiles.native_ratio
#print axioms PlasmaLean.Design.DommaschkNativePairedProfiles.native_field
#print axioms PlasmaLean.Certificates.NativeActionInterval.lower_cells
#print axioms PlasmaLean.Certificates.NativeActionInterval.exact_lower_mass
#print axioms PlasmaLean.Design.DommaschkSecondaryActionMass.floor_of_cover
#print axioms PlasmaLean.Design.DommaschkSecondaryActionCore.crosses_target
#print axioms PlasmaLean.Design.DommaschkSecondaryActionCore.floor_on_enclosing_interval
#print axioms PlasmaLean.Certificates.PositionFrameSlabs.OnPairedTubes.cons_at
#print axioms PlasmaLean.Certificates.PositionFrameSlabs.OnPairedTubes.on_nonempty_prefix
#print axioms PlasmaLean.Design.DommaschkComparedTracePrefixes.compare_birth
#print axioms PlasmaLean.Design.DommaschkComparedTracePrefixes.increment_of_compared
#print axioms PlasmaLean.Design.DommaschkGroupGapRadius.at_lower
#print axioms PlasmaLean.Design.DommaschkGroupedHarmonicGap.harmonic_mem
#print axioms PlasmaLean.Design.DommaschkGroupedHarmonicGap.estimate_mem
#print axioms PlasmaLean.Design.DommaschkGroupedProfileCompare.row_inputs
#print axioms PlasmaLean.Design.DommaschkGroupedProfileCompare.compare_rows
#print axioms PlasmaLean.Design.DommaschkLowerActionPath.from_joined
#print axioms PlasmaLean.Design.DommaschkLowerActionPath.Signed.inputs
#print axioms PlasmaLean.Design.DommaschkLowerActionPath.regions
#print axioms PlasmaLean.Certificates.PositionFrameSlabs.OnTubes.take
#print axioms PlasmaLean.Certificates.PositionFrameSlabs.OnTubes.on_initial
#print axioms PlasmaLean.Design.DommaschkSubmirrorPrefixObservation.of_birth
#print axioms PlasmaLean.Design.DommaschkLowerActionWindows.mass_monotone
#print axioms PlasmaLean.Design.DommaschkLowerActionWindows.first_crossing
#print axioms PlasmaLean.Design.DommaschkLowerActionWindows.at_cutoff
#print axioms PlasmaLean.Design.DommaschkLowerActionWindows.action_on_enclosing_interval
#print axioms PlasmaLean.Certificates.LowerActionHeightShift.clipped_lower
#print axioms PlasmaLean.Certificates.LowerActionHeightShift.covers
#print axioms PlasmaLean.Design.DommaschkSecondaryActionHeight.shifted_cover
#print axioms PlasmaLean.Design.DommaschkSecondaryActionHeight.first_well
#print axioms PlasmaLean.Design.DommaschkPairedFirstWellAction.on_chosen_paths
#print axioms PlasmaLean.Design.DommaschkPairedFirstWellAction.gains_of_branches
#print axioms PlasmaLean.Design.DommaschkPairedFirstWellAction.physical_secant
#print axioms PlasmaLean.Design.DommaschkPairedFirstWellAction.common
#print axioms PlasmaLean.Certificates.NativeActionInterval.coarse_time_mem
#print axioms PlasmaLean.Certificates.NativeActionInterval.directed_cells
#print axioms PlasmaLean.Design.DommaschkCoarseActionPhase.physical_phase
#print axioms PlasmaLean.Design.DommaschkSecondaryHeightCollar.time_near_upper
#print axioms PlasmaLean.Kinetic.MirrorActionEnvelope.action_add_shoulders
#print axioms PlasmaLean.Design.DommaschkIncomingHeightAction.closed_inputs
#print axioms PlasmaLean.Design.DommaschkIncomingHeightAction.lower_on_window
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.cells_of_lowerColumnsLE
#print axioms PlasmaLean.Kinetic.MirrorHeightBand.Branch.central_below
#print axioms PlasmaLean.Kinetic.MirrorHeightBand.Branch.bracket
#print axioms PlasmaLean.Design.DommaschkCommonLittlejohnTime.uniform_of_lifted
#print axioms PlasmaLean.Design.DommaschkPhaseZeroRegularBirth.open_birth
#print axioms PlasmaLean.Design.DommaschkPhaseZeroRegularBirth.tube_of_centers
#print axioms PlasmaLean.Design.DommaschkPhaseZeroRegularBirth.population
#print axioms PlasmaLean.Design.DommaschkPhaseZeroRegularBirth.at_original_birth
#print axioms PlasmaLean.Kinetic.VacuumLittlejohnWindow.familyControl_of_local
#print axioms PlasmaLean.Kinetic.VacuumLittlejohnWindow.FamilyControl.thickening
#print axioms PlasmaLean.Kinetic.VacuumLittlejohnWindow.exists_control_compact
#print axioms PlasmaLean.Kinetic.VacuumLittlejohnWindow.compact_guidingCentreBand
#print axioms PlasmaLean.Design.DommaschkCompactLittlejohnArc.Window.measured
#print axioms PlasmaLean.Design.DommaschkCompactLittlejohnArc.Window.thickening
#print axioms PlasmaLean.Design.DommaschkCompactLittlejohnArc.Uniform.unrestricted
#print axioms PlasmaLean.Design.DommaschkCompactLittlejohnArc.of_compact
#print axioms PlasmaLean.Design.DommaschkCompactLittlejohnArc.of_path
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.covers_of_blocksLowerLE
#print axioms PlasmaLean.Certificates.MirrorActionQuadrature.blocksLowerLE_append
#print axioms PlasmaLean.Design.DommaschkGroupedTrialJet.BoxMap.mem
#print axioms PlasmaLean.Design.DommaschkGroupedTrialJet.Pullback.mem
#print axioms PlasmaLean.Kinetic.VacuumLittlejohnWindow.common_enclosure_time
#print axioms PlasmaLean.Kinetic.VacuumLittlejohnWindow.control_of_compact_enclosure
#print axioms PlasmaLean.Design.DommaschkCompactLaunchPhases.continuous_cylinder
#print axioms PlasmaLean.Design.DommaschkCompactLaunchPhases.continuous_location
#print axioms PlasmaLean.Design.DommaschkCompactLaunchPhases.uniform_launches
#print axioms PlasmaLean.Design.DommaschkEnclosedLaunchArcs.positions_compact
#print axioms PlasmaLean.Design.DommaschkEnclosedLaunchArcs.positions_regular
#print axioms PlasmaLean.Design.DommaschkEnclosedLaunchArcs.uniform_enclosed
#print axioms PlasmaLean.Design.DommaschkOriginalBirthMargin.from_passage
#print axioms PlasmaLean.Certificates.PolynomialActionFloor.point
#print axioms PlasmaLean.Certificates.PolynomialActionFloor.integral_group
#print axioms PlasmaLean.Certificates.PolynomialActionFloor.shell_of_bounds
#print axioms PlasmaLean.Certificates.PolynomialActionFloor.Shell.adjoin
#print axioms PlasmaLean.Design.DommaschkFirstContactHeightBudget.good_height_measure
#print axioms PlasmaLean.Design.DommaschkFirstContactHeightBudget.majority
#print axioms PlasmaLean.Design.DommaschkJointLaunchArcs.in_positions
#print axioms PlasmaLean.Design.DommaschkJointLaunchArcs.simultaneous
#print axioms PlasmaLean.Design.DommaschkJointLaunchArcs.two_families
#print axioms PlasmaLean.Certificates.TrajectoryTaylorModel.strength_at
#print axioms PlasmaLean.Kinetic.MirrorActionEnvelope.affine_le_speed
#print axioms PlasmaLean.Kinetic.MirrorActionEnvelope.LaunchWell.affine_gain
#print axioms PlasmaLean.Design.DommaschkPilotArcLength.exact_sum
#print axioms PlasmaLean.Design.DommaschkPilotArcLength.packet
#print axioms PlasmaLean.Design.DommaschkClosedBandAction.on_paths
#print axioms PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues.vector_differentiableOn
#print axioms PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues.on_signed
#print axioms PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues.Side.inputs
#print axioms PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues.original_position
#print axioms PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues.from_passage
#print axioms PlasmaLean.Design.DommaschkVariableHorner.Steps.mem
#print axioms PlasmaLean.Design.DommaschkVariableHorner.Run.mem
#print axioms PlasmaLean.Design.DommaschkVariableHorner.row_mem
#print axioms PlasmaLean.Design.DommaschkVariableHorner.rows_mem
#print axioms PlasmaLean.Design.DommaschkVariableHorner.channel_cons
#print axioms PlasmaLean.Design.DommaschkRadialActionAlternative.of_endpoint_wells
#print axioms PlasmaLean.Design.DommaschkFirstMirrorHeightSampling.of_launch
#print axioms PlasmaLean.Design.DommaschkFirstMirrorHeightSampling.of_launch_width
#print axioms PlasmaLean.Design.DommaschkRadialRibbonEntry.from_close
#print axioms PlasmaLean.Design.DommaschkRadialRibbonEntry.from_nested_tori
#print axioms PlasmaLean.Design.DommaschkRadialFamilyContinuity.capped_of_births
#print axioms PlasmaLean.Design.DommaschkRadialFamilyContinuity.Enclosed.agree
#print axioms PlasmaLean.Design.DommaschkRadialFamilyContinuity.transfer_well
#print axioms PlasmaLean.Design.DommaschkRadialFamilyContinuity.alternative_of_passages
#print axioms PlasmaLean.Design.DommaschkRadialFamilyContinuity.prescribed_of_regular
#print axioms PlasmaLean.Design.DommaschkRadialSectionAction.from_section
#print axioms PlasmaLean.Design.DommaschkRadialSectionAction.realized_of_sections
#print axioms PlasmaLean.Certificates.PositionFrameWide.physical_step_on
#print axioms PlasmaLean.Design.DommaschkWideTraceFields.forward_rectangle
#print axioms PlasmaLean.Design.DommaschkWideTraceFields.backward_rectangle
#print axioms PlasmaLean.Design.DommaschkRibbonThroughChains.from_chains
#print axioms PlasmaLean.Design.DommaschkCompensatedMirrorSlope.numerator_eq
#print axioms PlasmaLean.Design.DommaschkRibbonSlopeCover.slope
#print axioms PlasmaLean.Design.DommaschkRibbonFirstMirrors.attach
#print axioms PlasmaLean.Design.DommaschkRibbonFirstMirrors.attach_below
#print axioms PlasmaLean.Design.DommaschkRibbonFirstMirrors.no_grazing
#print axioms PlasmaLean.Design.DommaschkRibbonFirstMirrors.NoGrazing.well_slopes
#print axioms PlasmaLean.Design.DommaschkRibbonFirstMirrors.NoGrazing.excludes_localMax
#print axioms PlasmaLean.Certificates.DyadicHornerStep.Fits.mem
#print axioms PlasmaLean.Certificates.DyadicHornerStep.MulAdd.mem
#print axioms PlasmaLean.Design.DommaschkDyadicHorner.Run.mem
#print axioms PlasmaLean.Design.DommaschkDyadicHorner.channel_cons
#print axioms PlasmaLean.Design.DommaschkSectorAction.continuous_sector_birth
#print axioms PlasmaLean.Design.DommaschkSectorAction.capped_sector
#print axioms PlasmaLean.Design.DommaschkSectorAction.sector_of_sections
#print axioms PlasmaLean.Design.DommaschkRadialAccessibleBirth.from_seed
#print axioms PlasmaLean.Design.DommaschkRadialAccessibleBirth.well_at_birth
#print axioms PlasmaLean.Design.DommaschkSectorFaces.of_endpoint_witnesses
