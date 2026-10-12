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
