"""Check the actual upper field sign on both clock caps of all four radial entry intervals."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from bounce_frame_witness import DEFAULT_WITNESS
from bounce_mirror_pilot import HEIGHTS
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import SIGNS, snapshot, tag


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--ribbon", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--cache", type=Path, default=ROOT / ".lake/radial-ribbon-caps")
    a = p.parse_args()
    env(a)
    packet = json.loads(a.ribbon.read_text())
    expected = [digest(DEFAULT_WITNESS), digest(DEFAULT_WITNESS.with_name("bounce_frame_q0_u478.json.gz"))]
    arcs = packet["traces"]
    if (packet["tiles"] != 4 or packet["seed_radius"] != "1/65536" or packet["endpoints"] != expected
            or Fraction(packet["height"]) != HEIGHTS[1]
            or [(tr["tile"], tr["direction"]) for tr in arcs] != [(k,s) for k in range(4) for s in [-1,1]]):
        p.error("expected the two archived radial endpoints and all four signed widened traces")
    i = 330
    bound = Fraction(i+1,64)
    keys = [a.version, *expected, digest(a.ribbon), digest(DESIGN / "DommaschkRadialRibbonEntry.trace")]
    deps = []
    ordered = []
    for k in range(4):
        traces = [{"steps": [r["position"] for r in arc["rows"]]} for arc in arcs[2*k:2*k+2]]
        if any(i >= len(t["steps"]) or t["steps"][i]["index"] != i for t in traces):
            p.error(f"missing the positive-cap slab on tile {k}")
        label = f"RadialRibbon{k}"
        pieces = snapshot((i, True, 1), label=label, traces=traces, keys=keys, cache=a.cache, args=a)
        deps.extend(pieces)
        ordered.append((tag(label,i,True,1),pieces[-1][1]["key"]))
    name = "DommaschkRadialRibbonUpperCaps"
    source = "module\npublic import PlasmaLean.Design.DommaschkRadialRibbonEntry\n" + "".join(
        f"public import {SIGNS}.{n}\n" for n,_ in ordered)
    source += f"""
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkMirrorEndpointSign
set_option linter.style.longLine false
def row (backward : Bool) (k : Fin 4) : Step :=
  if backward then ![{','.join(n+'.backRow' for n,_ in ordered)}] k
  else ![{','.join(n+'.fwdRow' for n,_ in ordered)}] k
theorem above (k : Fin 4) (backward : Bool) {{prev : State}} {{x : Plane}}
    (tube : x ∈ (physicalSlab prev (row backward k) ({i}/64)).tube ({bound})) :
    (DommaschkFirstMirrorLaunchSign.height true : ℝ) <
      strength (if backward then -({bound}) else {bound}) x := by
  cases backward <;> fin_cases k
"""
    for sign in ("fwd", "back"):
        for n,_ in ordered:
            source += f"  · exact {n}.{sign}_tube_sign tube\n"
    source += f"end PlasmaLean.Design.{name}\n"
    overlay = union(a.cache,deps)
    root,receipt = compile_modules(a.cache / name, [(name,source,["above"])], [overlay],
                                   [keys,ordered], a, "RadialRibbonCapCache")
    out = {k:receipt[k] for k in ("module","key","theorems","axioms","wall_seconds","peak_rss_kib")}
    out.update(import_paths=list(map(str,[root,overlay])), ribbon=digest(a.ribbon), time=str(bound),
               tiles=dict(ordered), endpoints=expected)
    save(a.output,out)
    print(name,receipt["key"],flush=True)


if __name__ == "__main__":
    main()
