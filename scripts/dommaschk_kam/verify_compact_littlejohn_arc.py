"""Attach a uniform Littlejohn time to the entire authenticated central QA2R pilot arc."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def physical_source(old, suffix):
    name = f"DommaschkCompactBirthArc{suffix}"
    family = "DommaschkCommonEndpointTraces" + suffix
    calibration = "DommaschkCalibratedFamily" + suffix
    src = f"""module
public import PlasmaLean.Design.DommaschkCompactLittlejohnArc
public import RegularBirthArcsCache.{old}

/-! # Simultaneous controlled guiding-centre time for a full physical pilot population -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkFirstMirrorWell DommaschkPhaseZeroRegularBirth
open DommaschkCommonPilotObservables DommaschkSignedTraceDomain DommaschkCompactLittlejohnArc
open {family} (checkpoint)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false

/-- For each original admitted launch the entire central angular arc, every band height and
every energy in a prescribed positive closed interval have a common controlled open set. -/
theorem pilot : Common checkpoint (fun φ y => {calibration}.Observed φ y ∧ Population (316/64) y ∧
    Uniform (point y '' Icc (-316/64:ℝ) (316/64))) := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,var,each,previous⟩ := {old}.pilot
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,var,each,fun φ small => ?_⟩
  obtain ⟨x,y,original,path,obs,pop⟩ := previous φ small
  refine ⟨x,y,original,path,obs,pop,?_⟩
  have reg := on_path path (by change 0 < 391; norm_num) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) rfl rfl
  have restricted : ∀ t ∈ Icc (-(316/64:ℝ)) (316/64), Region (y t) := by
    intro t ht
    apply reg
    change -(391:ℝ)/64 ≤ t ∧ t ≤ 391/64
    constructor <;> linarith [ht.1,ht.2]
  have family := of_path (a := 316/64) path (by norm_num)
    (by change (316/64:ℝ) < (391:ℝ)/64; norm_num) restricted pop
  simpa only [neg_div] using family

end PlasmaLean.Design.{name}
"""
    return name, src, ["pilot"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regular-arcs", type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=ROOT/".lake/compact-littlejohn-arcs")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.regular_arcs.read_text())
    parent = report["birth"]
    pattern = r"DommaschkRegularBirthArcs(391(?:_[1-9][0-9]*){7})"
    match = re.fullmatch(pattern, parent["module"])
    if not match or f"PlasmaLean.Design.{parent['module']}.pilot" not in parent["theorems"]:
        parser.error("expected an authenticated N147 regular-arc receipt for the 391-row pilot")
    imports = list(map(Path, parent["import_paths"]))
    admitted(imports[0], parent["module"], parent["key"])

    def lake(*cmd):
        return subprocess.check_output(["lake", "env", *cmd], cwd=ROOT, text=True).strip()

    args.lean = str(Path(lake("lean", "--print-prefix"))/"bin/lean")
    args.lean_path = lake("printenv", "LEAN_PATH")
    keys = [lake("lean", "--version"), digest(DESIGN/"DommaschkCompactLittlejohnArc.trace"), parent["key"]]
    item = physical_source(parent["module"], match[1])
    root, proof = compile_modules(args.cache/item[0], [item], imports, keys, args,
                                  "CompactLittlejohnArcCache")
    out = {k: proof[k] for k in ["module", "key", "theorems", "axioms", "wall_seconds", "peak_rss_kib"]}
    out.update(original_arcs=parent["key"], launch="q0r470", central_radius="316/64",
               import_paths=list(map(str, [root, *imports])))
    save(args.output, out)
    print(item[0], proof["key"])


if __name__ == "__main__":
    main()
