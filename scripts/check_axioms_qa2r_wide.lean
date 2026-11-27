import Lean.Util.CollectAxioms
import WideTube.DommaschkWideTubeRows000Lower
/-! Axiom audit of the script-generated wide-tube modules (`generated/qa2r_wide/`, library
`QA2RWide`, note N-216). Run by `scripts/qa2r_wide/replay.py` after the build:
`lake env lean scripts/check_axioms_qa2r_wide.lean`.

Every visible declaration owned by a `WideTube` module may depend only on `propext`,
`Classical.choice` and `Quot.sound`; the three theorems of every slab module are named
explicitly, so a missing slab fails the audit. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut modules : NameSet := {}
  for m in env.allImportedModuleNames do
    if m.getRoot == `WideTube then modules := modules.insert m
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.allImportedModuleNames[idx.toNat]!.getRoot == `WideTube then
        for ax in (← collectAxioms name) do
          unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
  let mut slabs : Nat := 0
  for k in [0:332] do
    let digits := (toString (1000 + k)).drop 1
    let ns := (`PlasmaLean.Design).str s!"DommaschkWideTubeF{digits}"
    for t in ["abs_quadratic", "neg_le_quadratic", "field_bounds"] do
      unless env.contains (ns.str t) do throwError "Missing {ns.str t}"
    slabs := slabs + 1
  let expected := (← IO.FS.lines "generated/qa2r_wide/MANIFEST.sha256").size
  unless modules.size == expected do
    throwError "{modules.size} WideTube modules imported, the manifest lists {expected}"
  logInfo m!"QA2R wide-tube axiom audit passed: {checked} declarations in {modules.size} \
    modules; {slabs} slabs with two-sided Jacobian bounds and field bounds."

#print axioms PlasmaLean.Design.DommaschkWideTubeRows000Joined.steps
#print axioms PlasmaLean.Design.DommaschkWideTubeRows000Joined.field_bounds
#print axioms PlasmaLean.Design.DommaschkWideTubeRows000Joined.trajectory
#print axioms PlasmaLean.Design.DommaschkWideTubeRows000Lower.lower
