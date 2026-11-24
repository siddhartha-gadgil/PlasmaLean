"""Attach both radial action comparisons to the two original births on common QA2R tori."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_common_endpoint_traces import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("well", "regular", "compared", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/top-height-secants")
    args = parser.parse_args()
    env(args)
    well, regular, compared = [json.loads(p.read_text()) for p in (args.well, args.regular, args.compared)]
    counts = regular["lengths_each_direction"]
    suffix = "_".join(str(counts[e]) for e in ENDPOINTS)
    if (not well["complete"] or well["module"] != "DommaschkQ0R478PolynomialFirstWell"
            or not regular["outer_from_birth"] or counts["q0r470"] != 391 or counts["q0r478"] <= 327
            or well["packet_sha256"] != regular["packet_sha256"] or compared["packets"][1] != well["packet_sha256"]
            or compared["length"] != 325 or regular["calibrated_key"] != compared["calibrated_key"]
            or regular["birth"]["module"] != "DommaschkRegularBirthArcs" + suffix
            or compared["module"] != "DommaschkComparedBirths325On" + suffix):
        parser.error("expected matching upper first-well, original signed birth and calibrated paired field proofs")
    keys = [args.version, digest(DESIGN / "DommaschkPairedFirstWellAction.trace")]
    inputs = []
    for record in (well, regular["birth"], compared):
        roots = list(map(Path, record["import_paths"]))
        admitted(roots[0], record["module"], record["key"])
        inputs.extend(roots)
        keys.append(record["key"])
    overlay = merge_import_roots(args.cache, inputs, keys)
    template = Path(__file__).parent / "templates/top_height_action_secant.lean.tpl"
    src = template.read_text().replace("SUFFIX", suffix).replace("OUTER_LENGTH", str(counts["q0r478"]))
    name = "DommaschkTopHeightSecant" + suffix
    decl = (name, src, ["top_of_wells", "both_on_paths", "from_common_tori"])
    root, record = compile_modules(args.cache / name, [decl], [overlay], keys, args, "TopHeightSecantCache")
    gap = Fraction(well["mass"]) - Fraction(1146552112157123, 844424930131968)
    out = {k: record[k] for k in ("module", "key", "theorems", "axioms", "peak_rss_kib", "wall_seconds")}
    out.update(import_paths=list(map(str, [root, overlay])), well=well["key"], regular=regular["birth"]["key"],
               compared=compared["key"], gap_lower=str(gap), secant_lower=str(125 * gap))
    save(args.output, out)
    print(name, record["key"], flush=True)


if __name__ == "__main__":
    main()
