/-
Axiom check for heavy certificates kept out of the default build (on-demand top modules).
Build the top modules first, `lake build PlasmaLean.Design.RationalStellaratorGCEwFamily`,
`lake build PlasmaLean.Design.RationalStellaratorGCMuWide`,
`lake build PlasmaLean.Design.RationalStellaratorGCMuQuarter` and
`lake build PlasmaLean.Design.CoilKamCert` (bounded, dependencies first),
then run `lake env lean scripts/check_axioms_heavy.lean`.

Like `scripts/check_axioms.lean`, this script **fails** if any declaration owned by a
`PlasmaLean*` module in its import closure depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound` (so `sorryAx`, `Lean.ofReduceBool`, native `bv_decide`
axioms and project axioms are rejected).
-/
import PlasmaLean.Design.RationalStellaratorGCEwFamily
import PlasmaLean.Design.RationalStellaratorGCMuWide
import PlasmaLean.Design.RationalStellaratorGCMu3Confined
import PlasmaLean.Design.RationalStellaratorGCMu4Confined
import PlasmaLean.Design.RationalStellaratorGCMu5Confined
import PlasmaLean.Design.RationalStellaratorGCMuQuarter
import PlasmaLean.Design.CoilKamCert
import Lean.Util.CollectAxioms

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
