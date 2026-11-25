"""Bind the prescribed-action or grazing alternative to the two original QA2R births."""
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
    parser.add_argument("--top", type=Path, required=True, help="audited upper-height secant on both births")
    parser.add_argument("--through-ode", action="store_true",
                        help="identify the endpoints by ODE uniqueness and prove joint continuity")
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/radial-action-alternatives")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent = json.loads(args.top.read_text())
    match = re.fullmatch(r"DommaschkTopHeightSecant(\d+(?:_\d+){7})", parent["module"])
    if match is None:
        parser.error("expected the upper-height eight-launch comparison")
    name = "DommaschkRadialActionAlternativeOn" + match.group(1)
    roots = list(map(Path, parent["import_paths"]))
    marker = admitted(roots[0], parent["module"], parent["key"])
    if f"PlasmaLean.Design.{parent['module']}.from_common_tori" not in marker["theorems"]:
        parser.error("upper-height comparison must identify the original two birth trajectories")
    env(args)
    template = Path(__file__).parent / "templates/radial_action_alternative.lean.tpl"
    source = template.read_text().replace("PARENT", parent["module"]).replace("NAME", name)
    parents = [args.version, parent["key"], digest(DESIGN / "DommaschkRadialActionAlternative.trace")]
    package = "RadialActionAlternativeCache"
    theorems = ["of_secant", "from_common_tori"]
    if args.through_ode:
        suffix = match.group(1)
        pilot, outer, *_ = map(int, suffix.split("_"))
        if pilot != 391 or outer <= 327:
            parser.error("the physical endpoint proofs require the 391-row pilot and a cap beyond row 327")
        name = "DommaschkRadialFlowOn" + suffix
        template = template.with_name("radial_field_line_continuation.lean.tpl")
        source = template.read_text().replace("SUFFIX", suffix).replace("OUTER_LENGTH", str(outer))
        parents.extend(digest(DESIGN / (module + ".trace")) for module in
                       ("DommaschkRadialFamilyContinuity", "DommaschkRadialRibbonEntry"))
        package = "RadialFieldLineContinuationCache"
        theorems = ["from_entries", "from_nested_tori"]
    declaration = (name, source, theorems)
    base, record = compile_modules(args.cache / name, [declaration], roots, parents, args,
                                   package)
    report = {k: record[k] for k in ("module", "key", "theorems", "axioms",
                                     "wall_seconds", "peak_rss_kib")}
    report.update(upper_secant=parent["key"], import_paths=list(map(str, [base, *roots])))
    save(args.output, report)
    print(name, record["key"])


if __name__ == "__main__":
    main()
