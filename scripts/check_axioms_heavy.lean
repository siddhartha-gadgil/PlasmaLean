/-
Axiom check for heavy certificates kept out of the default build (on-demand top modules).
Build the top modules first, `lake build PlasmaLean.Design.RationalStellaratorGCEwFamily`,
`lake build PlasmaLean.Design.RationalStellaratorGCMuWide`,
`lake build PlasmaLean.Design.RationalStellaratorGCMuQuarter` and
`lake build PlasmaLean.Design.CoilKamCert`, `lake build PlasmaLean.Design.DommaschkKamCAdm`, `lake build PlasmaLean.Design.DommaschkKamCConsts`,
`lake build PlasmaLean.Design.DommaschkKamCContract`,
`lake build PlasmaLean.Design.DommaschkKamCRes`, `lake build PlasmaLean.Design.DommaschkKamCFinal`,
`lake build PlasmaLean.Design.DommaschkKamCQSTransfer`, `lake build PlasmaLean.Design.DommaschkKamCQSIdent`, `lake build PlasmaLean.Design.DommaschkKamCQS`
(bounded, dependencies first),
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
import PlasmaLean.Design.DommaschkKamCAdm
import PlasmaLean.Design.DommaschkKamCConsts
import PlasmaLean.Design.DommaschkKamCContract
import PlasmaLean.Design.DommaschkKamCRes
import PlasmaLean.Design.DommaschkKamCFinal
import PlasmaLean.Design.DommaschkKamCQSTransfer
import PlasmaLean.Design.DommaschkKamCQSIdent
import PlasmaLean.Design.DommaschkKamCQS

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
