/-
Axiom check for heavy certificates kept out of the default build (on-demand top modules).
Build the top modules first, e.g. `lake build PlasmaLean.Design.RationalStellaratorGCEwFamily`,
then run `lake env lean scripts/check_axioms_heavy.lean`.
-/
import PlasmaLean.Design.RationalStellaratorGCEwFamily

#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_confined_forever_energy_window
#print axioms PlasmaLean.Design.RationalStellaratorGC.alphaEwVel_volume_pos
#print axioms PlasmaLean.Design.RationalStellaratorGC.alpha_gc_ew_confined_forever_velocity_set
