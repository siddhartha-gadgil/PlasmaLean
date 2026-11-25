"""Bind the four section checks to the original prescribed-action birth on the verified tori."""
import argparse
import json
from pathlib import Path
import re

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flow", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/radial-section-target")
    args = parser.parse_args()
    report = json.loads(args.flow.read_text())
    parent = report["module"]
    match = re.fullmatch(r"DommaschkRadialFlowOn(\d+(?:_\d+){7})", parent)
    if not match:
        parser.error("expected the authenticated common-torus field-line continuation proof")
    roots = list(map(Path, report["import_paths"]))
    marker = admitted(roots[0], parent, report["key"])
    if f"PlasmaLean.Design.{parent}.from_nested_tori" not in marker["theorems"]:
        parser.error("missing the endpoint comparison on the original embedded tori")
    env(args)
    name = "DommaschkRadialSectionTargetOn" + match.group(1)
    source = f"""module
public import RadialFieldLineContinuationCache.{parent}
public import PlasmaLean.Design.DommaschkRadialSectionAction

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkRadialSectionAction
set_option linter.style.longLine false

/-- A universal check on four initial section balls gives a physical birth at the target action
for each admissible phase on the original pair of nested embedded invariant tori. -/
theorem from_sections : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ : ℝ, |φ| ≤ 1/2^19 → Sections (fun y => Signs y ∧ Simple y) → Realized uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,passages⟩ := {parent}.from_nested_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small sections => ?_⟩
  obtain ⟨tiles,endpoint⟩ := passages φ small
  apply realized_of_sections small tiles sections
  intro Y born paths signs
  exact endpoint Y born paths (fun u => (signs u).low) (fun u => (signs u).back) (fun u => (signs u).front)
end PlasmaLean.Design.{name}
"""
    keys = [args.version, report["key"], digest(DESIGN / "DommaschkRadialSectionAction.trace")]
    base, record = compile_modules(args.cache / name, [(name, source, ["from_sections"])],
                                   roots, keys, args, "RadialSectionTargetCache")
    result = {k: record[k] for k in ("module", "key", "theorems", "axioms", "wall_seconds", "peak_rss_kib")}
    result.update(flow_key=report["key"], import_paths=list(map(str, [base, *roots])))
    save(args.output, result)
    print(name, record["key"])


if __name__ == "__main__":
    main()
