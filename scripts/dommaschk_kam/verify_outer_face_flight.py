"""Ground the variable-height Cartesian time and action bounds on the completed outer face."""
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
    parser.add_argument("--faces", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/outer-face-flight")
    args = parser.parse_args()
    faces = json.loads(args.faces.read_text())
    match = re.fullmatch(r"DommaschkPhysicalActionExitOn(\d+(?:_\d+){7})", faces["module"])
    if not match or faces["counts"][1] <= 327:
        parser.error("requires the authenticated independent birth-centered face theorem")
    roots = list(map(Path, faces["import_paths"]))
    old = faces["module"]
    proof = admitted(roots[0], old, faces["key"])
    if f"PlasmaLean.Design.{old}.from_nested_tori" not in proof["theorems"]:
        parser.error("missing original embedded torus witnesses")
    source = (roots[0] / "RadialSectorFacesCache" / (old + ".lean")).read_text()
    start = "  exact of_endpoint_witnesses\n"
    end = "\ntheorem from_nested_tori :"
    if source.count(start) != 1 or source.count(end) != 1:
        parser.error("missing the completed physical endpoint path reconstruction")
    prefix, rest = source.split(start)
    _, tori = rest.split(end)
    n = faces["counts"][1]
    # Both clocks restrict the same actual solution z to the original outer-face packets.
    branches = f"""  have f := signed.forward
  have b := signed.backward
  rw [show (checkpoint .q0r478).forwardRows = fwdRows ++ (checkpoint .q0r478).forwardRows.drop 327
    by with_unfolding_all rfl] at f
  rw [show (checkpoint .q0r478).backwardRows = backRows ++ (checkpoint .q0r478).backwardRows.drop 327
    by with_unfolding_all rfl] at b
  have room : (327/64:ℝ) < {n}/64 := by norm_num
  obtain ⟨pf⟩ := fwd_branch f.prefix room
  obtain ⟨pb⟩ := back_branch b.prefix room
  exact DommaschkOuterFaceFlight.of_outer_witness small bornO pz pf pb outerWell outerFloor

"""
    name = "DommaschkOuterFaceFlightOn" + match[1]
    source = (prefix + branches + end + tori).replace(old, name)
    source = source.replace("public import PlasmaLean.Design.DommaschkPhysicalActionExit",
                            "public import PlasmaLean.Design.DommaschkOuterFaceFlight")
    source = source.replace("open DommaschkPhysicalActionExit", "open DommaschkOuterFaceFlight")
    source = source.replace("BoundaryValues uC zC uA zA φ", "DommaschkOuterFaceFlight.Result uC zC uA zA φ")
    env(args)
    keys = [args.version, faces["key"], digest(DESIGN / "DommaschkOuterFaceFlight.trace")]
    root, result = compile_modules(args.cache / name, [(name, source, ["from_entries", "from_nested_tori"])],
                                   roots, keys, args, "OuterFaceFlightCache")
    report = {key: result[key] for key in ("module", "key", "theorems", "axioms", "wall_seconds")}
    report.update(faces=faces["key"], time_upper=452, near_upper_width="1/100000",
                  import_paths=list(map(str, [root, *roots])))
    save(args.output, report)
    print(name, report["key"], flush=True)


if __name__ == "__main__":
    main()
