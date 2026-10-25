/-
Axiom check for heavy certificates kept out of the default build (on-demand top modules).
Build the top modules first, `lake build PlasmaLean.Design.RationalStellaratorGCEwFamily` and
`lake build PlasmaLean.Design.RationalStellaratorGCMuWide`,
then run `lake env lean scripts/check_axioms_heavy.lean`.
-/
import PlasmaLean.Design.RationalStellaratorGCEwFamily
import PlasmaLean.Design.RationalStellaratorGCMuWide
import PlasmaLean.Design.RationalStellaratorGCMu3Confined
import PlasmaLean.Design.RationalStellaratorGCMu4Confined
import PlasmaLean.Design.RationalStellaratorGCMu5Confined

#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_confined_forever_energy_window
#print axioms PlasmaLean.Design.RationalStellaratorGC.alphaEwVel_volume_pos
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_ew_confined_forever_velocity_set
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_passing_confined_forever_wide
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu2.rationalStellarator_gc_mu_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu3.rationalStellarator_gc_mu_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu4.rationalStellarator_gc_mu_confined_forever
#print axioms PlasmaLean.Design.RationalStellaratorGC.Mu5.rationalStellarator_gc_mu_confined_forever
