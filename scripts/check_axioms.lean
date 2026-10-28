import LeanTheory
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
      | some idx => (`LeanTheory).isPrefixOf env.allImportedModuleNames[idx.toNat]!
      | none => false
    if owned then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations found: audit did not run"
  logInfo m!"Axiom audit passed for {checked} LeanTheory declarations."

#print axioms LeanTheory.Certificates.BlockCertificate.sound
#print axioms LeanTheory.Certificates.local_fixedPoint
#print axioms LeanTheory.Stability.suydamForm_coercive
#print axioms LeanTheory.Stability.suydam_necessary
#print axioms LeanTheory.Stability.hardy_sharp
#print axioms LeanTheory.Stability.picone_certificate
#print axioms LeanTheory.Stability.suydam_from_picone
#print axioms LeanTheory.Certificates.QPoly.checkOn_sound
#print axioms LeanTheory.Certificates.QPoly.riccati_poly_certificate
#print axioms LeanTheory.Certificates.QPoly.example_beyond_constant
#print axioms LeanTheory.Theory.KAM.kam_sequence
#print axioms LeanTheory.Theory.KAM.norm_sub_interp_le
#print axioms LeanTheory.Theory.KAM.PQG.valid_of_nodesOK
#print axioms LeanTheory.Fields.lieBracket_gradient
#print axioms LeanTheory.Fields.lieBracket_gradient_of_contDiffAt
#print axioms LeanTheory.Fields.lieBracket_gradient_of_killing
#print axioms LeanTheory.Sanity.quasisymmetry_not_pde_symmetry
#print axioms LeanTheory.Sanity.qs_lieBracket_X_gradP
#print axioms LeanTheory.Sanity.qs_strain_term
#print axioms LeanTheory.Stability.riccati_le_initial
#print axioms LeanTheory.Stability.riccati_exp_decay
#print axioms LeanTheory.Stability.riccati_hyp_exp
#print axioms ConcLean.SubsetSum.subsetSum_correct
#print axioms LeanTheory.Example.energy_conserved
#print axioms LeanTheory.Example.not_oscillatorLaw_exp
#print axioms LeanTheory.Example.cos_energy
#print axioms LeanTheory.Example.free_velocity_const
#print axioms LeanTheory.Example.amplitude_bound
#print axioms LeanTheory.Example.initialStates_energy_le
#print axioms LeanTheory.Example.amplitude_cert
#print axioms LeanTheory.Fields.curl_fderiv_smul
#print axioms LeanTheory.Fields.invariantBarrier_forward
#print axioms LeanTheory.Fields.ODEGlobal.existsUnique_global
#print axioms LeanTheory.Certificates.EvalCert.ECert.sound
#print axioms LeanTheory.Certificates.KronProof.kernelFact_fixture
