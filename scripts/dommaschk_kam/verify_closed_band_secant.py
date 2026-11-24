"""Ground the full closed-band action gain on the already calibrated pair of physical births."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_common_endpoint_traces import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("top", "family", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/closed-band-action-secants")
    args = parser.parse_args()
    env(args)
    top, family = (json.loads(p.read_text()) for p in (args.top, args.family))
    counts = family["lengths_each_direction"]
    suffix = "_".join(str(counts[e]) for e in ENDPOINTS)
    if (top["module"] != "DommaschkTopHeightSecant" + suffix or top["regular"] != family["birth"]["key"]
            or counts["q0r470"] != 391 or counts["q0r478"] <= 327):
        parser.error("expected the proved upper secant and its common family through both mirror pairs")
    paths = list(map(Path, top["import_paths"]))
    admitted(paths[0], top["module"], top["key"])
    template = Path(__file__).parent / "templates"
    source = (template / "closed_band_action_secant.lean.tpl").read_text() + "\n"
    # Preserve the original-birth equalities and the exact choice of the two signed lines.
    earlier = (template / "top_height_action_secant.lean.tpl").read_text()
    common = earlier[earlier.index("theorem from_common_tori"):]
    old = "∧ Gains y z ∧ UpperSecant y z"
    if common.count(old) != 1:
        parser.error("the original shared-birth theorem has changed")
    common = common.replace(old, old + " ∧ Separated y z").replace(
        "end PlasmaLean.Design.DommaschkTopHeightSecant", "end PlasmaLean.Design.DommaschkClosedBandSecant")
    source = (source + common).replace("SUFFIX", suffix).replace("OUTER_LENGTH", str(counts["q0r478"]))
    keys = [args.version, top["key"], digest(DESIGN / "DommaschkPilotArcLengthPacket.trace"),
            digest(DESIGN / "DommaschkClosedBandAction.trace")]
    name = "DommaschkClosedBandSecant" + suffix
    decl = (name, source, ["both_on_paths", "from_common_tori"])
    root, rec = compile_modules(args.cache / name, [decl], paths, keys, args, "ClosedBandSecantCache")
    out = {k: rec[k] for k in ("module", "key", "theorems", "axioms", "peak_rss_kib", "wall_seconds")}
    out.update(top=top["key"], arclength_floor="9309/1000", action_gap="2/625", secant="2/5",
               import_paths=list(map(str, [root, *paths])))
    save(args.output, out)
    print(name, rec["key"], flush=True)


if __name__ == "__main__":
    main()
