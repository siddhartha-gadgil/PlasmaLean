import PlasmaLean
import Lean.Util.CollectAxioms

/-! Audit all declarations owned by project modules, including definitions and generated
lemmas. The only allowed logical axioms are Lean's standard classical foundations.
This fails on sorryAx, native_decide trust, or any added project/model axiom. -/
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
  logInfo m!"Axiom audit passed for {checked} PlasmaLean declarations."

#print axioms PlasmaLean.Certificates.BlockCertificate.sound
#print axioms PlasmaLean.Certificates.local_fixedPoint
#print axioms PlasmaLean.Design.validated_scalar_root
#print axioms PlasmaLean.Design.synthetic_slab_model_margin
#print axioms PlasmaLean.Fields.filamentField_bound
#print axioms PlasmaLean.Fields.circularCoil_axis_field
#print axioms PlasmaLean.Design.VacuumPair.field_bound
#print axioms PlasmaLean.Design.VacuumPair.midpoint_field_positive
#print axioms PlasmaLean.Fields.inverseCube_derivative_bound
#print axioms PlasmaLean.Design.VacuumPair.field_difference
#print axioms PlasmaLean.Fields.filamentField_perturbation
#print axioms PlasmaLean.Fields.filamentField_derivative
#print axioms PlasmaLean.Fields.filamentField_derivative_bound
#print axioms PlasmaLean.Design.VacuumPair.robust_probe_field
#print axioms PlasmaLean.Design.VacuumPair.manufactured_field_derivative
#print axioms PlasmaLean.Design.VacuumPair.manufactured_tube_clearance
#print axioms PlasmaLean.Geometry.placedCircle_position_error
#print axioms PlasmaLean.Sanity.probe_fieldLine_duration
#print axioms PlasmaLean.Fields.filamentField_vacuum_maxwell
#print axioms PlasmaLean.Stability.suydamForm_coercive
#print axioms PlasmaLean.Stability.suydam_necessary
#print axioms PlasmaLean.Stability.hardy_sharp
#print axioms PlasmaLean.Fields.fieldLine_bounded
#print axioms PlasmaLean.Design.ClebschTorus.fieldLine_stays_in_torus
#print axioms PlasmaLean.Kinetic.energy_conserved
#print axioms PlasmaLean.Kinetic.helix_orbit
#print axioms PlasmaLean.Kinetic.alpha_3_5MeV_5T
#print axioms PlasmaLean.Fields.clebsch_divergence_free
#print axioms PlasmaLean.Design.ClebschTorus.field_divergence_free
#print axioms PlasmaLean.Design.ClebschTorus.field_not_vacuum
#print axioms PlasmaLean.Stability.picone_certificate
#print axioms PlasmaLean.Stability.suydam_from_picone
#print axioms PlasmaLean.Kinetic.canonicalMomentum_conserved
#print axioms PlasmaLean.Kinetic.orbit_trapped_until
#print axioms PlasmaLean.Design.PolyTokamak.orbit_confined
#print axioms PlasmaLean.Design.PolyTokamak.ripple_orbit_confined
#print axioms PlasmaLean.Design.ScrewPinchExample.suydam_margin
#print axioms PlasmaLean.Design.ScrewPinchExample.beta_eq
#print axioms PlasmaLean.Design.Solovev.force_balance
#print axioms PlasmaLean.Design.Solovev.orbit_confined
#print axioms PlasmaLean.Design.Solovev.iter_like_deuteron_confined
#print axioms PlasmaLean.Design.Solovev.iter_like_beta
#print axioms PlasmaLean.Kinetic.noetherMomentum_conserved
#print axioms PlasmaLean.Kinetic.noether_orbit_trapped
#print axioms PlasmaLean.Design.HelicalStellarator.orbit_confined
#print axioms PlasmaLean.Design.HelicalStellarator.field_not_axisymmetric
#print axioms PlasmaLean.Certificates.QPoly.checkOn_sound
#print axioms PlasmaLean.Certificates.QPoly.riccati_poly_certificate
#print axioms PlasmaLean.Certificates.QPoly.example_beyond_constant
#print axioms PlasmaLean.Design.HelicalFamily.field_divergence_free
#print axioms PlasmaLean.Design.HelicalEquilibrium.force_balance
#print axioms PlasmaLean.Design.HelicalEquilibrium.orbit_confined
#print axioms PlasmaLean.Design.HelicalReactorScale.reactor_deuteron_confined
#print axioms PlasmaLean.Design.HelicalReactorScale.scaled_force_balance
#print axioms PlasmaLean.Stability.ScrewPinchModes.suydam_limit_weight
#print axioms PlasmaLean.Design.ScrewPinchModes.stable_low_m
#print axioms PlasmaLean.Design.ScrewPinchModes.stable_uniform
#print axioms PlasmaLean.Design.BurnWindow.m1_sustained_burn
#print axioms PlasmaLean.Design.BurnWindow.m1_burn_window
#print axioms PlasmaLean.Transport.le_of_isLowerBarrier
#print axioms PlasmaLean.Transport.mem_Icc_of_barriers
#print axioms PlasmaLean.Vacuum.weak_maximum_principle
#print axioms PlasmaLean.Vacuum.VacuumField.error_le_of_frontier
#print axioms PlasmaLean.Design.TransportBarrier.m2_core_barrier
#print axioms PlasmaLean.Design.BurnWindowScaling.m1_scaling_window_loss
#print axioms PlasmaLean.Design.ScrewPinchModesHighM.stable_all_modes
#print axioms PlasmaLean.Vacuum.VacuumField.not_closed_fieldLine_transverse_minB
#print axioms PlasmaLean.Design.SolovevAlpha.reactor_alpha_confined
#print axioms PlasmaLean.Design.HelicalTransportBarrier.helical_core_barrier
#print axioms PlasmaLean.Design.BurnWindowStellarator.stellaris_window_loss
#print axioms PlasmaLean.Design.ValidatedBVP.validated_bvp
#print axioms PlasmaLean.Design.NearAxisQA.alpha_trapped_reactorQA
#print axioms PlasmaLean.Design.NearAxisQAAveraged.alpha_trapped_reactorQA_averaged
#print axioms PlasmaLean.Design.ValidatedSlab.validated_slab_equilibrium
#print axioms PlasmaLean.Design.SolovevMercier.reactor_q_ge
#print axioms PlasmaLean.Design.SolovevBand.solovev_one_plasma
#print axioms PlasmaLean.Design.QuasilinearBarrier.quasilinear_band
#print axioms PlasmaLean.Design.SolovevMercierCertified.reactor_mercier_stable
#print axioms PlasmaLean.Design.SolovevFluxGeometry.solovev_one_plasma_actual
#print axioms PlasmaLean.Design.SolovevBandIgnited.solovev_one_plasma_ignited_actual
#print axioms PlasmaLean.Design.SolovevBallooning.reactor_ballooning_s1
#print axioms PlasmaLean.Design.RationalStellarator.field_vacuum
#print axioms PlasmaLean.Design.RationalStellarator.Confined.rationalStellarator_confined_local
#print axioms PlasmaLean.Design.SolovevCoarea.solovev_one_plasma_actual_coarea
#print axioms PlasmaLean.Design.SolovevBallooning.reactor_ballooning_all
#print axioms PlasmaLean.Design.RationalStellarator.Coils.coil_stellarator_confined
#print axioms PlasmaLean.Design.NearAxisQATrappedResonance.exactQA_nonresonant
#print axioms PlasmaLean.Design.LandremanEquilibrium.force_balance
#print axioms PlasmaLean.Fields.torus_trapping_forever
#print axioms PlasmaLean.Design.KamTorusA.torusA_error_le
#print axioms PlasmaLean.Design.PolygonCoil.coil_stellarator_confined_concrete
#print axioms PlasmaLean.Theory.KAM.kam_sequence
#print axioms PlasmaLean.Design.KamTorusA.Frame.torusA_twist
#print axioms PlasmaLean.Design.LandremanFamily2.family2_shear
#print axioms PlasmaLean.Design.LandremanMercier.family1_mercier_unstable
#print axioms PlasmaLean.Design.RationalStellarator.rationalStellarator_confined_forever
#print axioms PlasmaLean.Design.RationalStellarator.rationalStellarator_confined_forever_exists
#print axioms PlasmaLean.Design.PolygonCoil.coil_stellarator_confined_concrete_N
#print axioms PlasmaLean.Design.RationalStellaratorGC.gc_exact_torus
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGCNeg.alpha_gc_confined_forever_pm
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_confined_forever_robust
