"""Prove a positive parallel-speed floor along all original births on a signed physical prefix."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_ribbon_height_band import ROWS, group
from verify_radial_ribbon_slopes import load_ribbon
from verify_signed_mirror_passage import merge_import_roots


def joined(through, groups):
    count, path = through["outer_rows"], through["module"]
    stop = groups[-1]["stop"]
    name = f"DommaschkRadialPassing{count:03}Core{stop:03}"
    imports = [through["package"] + "." + path, "PlasmaLean.Design.DommaschkRadialPassingCore"]
    for item in groups:
        imports.extend(ROWS + "." + tile["module"] for tile in item["tiles"])
    source = "module\n" + "".join(f"public import {module}\n" for module in imports) + f"""
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkRadialRibbonEntry
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkRadialPassingCore DommaschkRadialActionAlternative DommaschkNativeWellAction
open DommaschkRadialFamilyContinuity DommaschkRibbonFirstMirrors
set_option maxRecDepth 16000
set_option linter.style.longLine false

theorem in_ball (k : Fin 4) (x : Plane) (entry : x ∈ stateSet (seed k)) :
    ∃ y : ℝ → Plane, y 0 = x ∧ Enclosed y (-({count-1}/64)) ({count-1}/64) ∧ Passing y ({stop}/64) := by
  obtain ⟨y, start, path, rows⟩ := {path}.from_seed k x entry
  refine ⟨y, start, path, passing_of_below ?_⟩
  fin_cases k
"""
    for k in range(4):
        pieces = [
            f"({item['tiles'][k]['module']}.tracked (rows.mono (by norm_num)))"
            for item in groups
        ]
        term = pieces[0]
        for piece in pieces[1:]:
            term = f"({term}.append {piece})"
        source += f"  · simpa only [zero_div] using {term}\n"
    source += f"""
theorem from_nested_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ (φ : ℝ) (u : Radius), |φ| ≤ 1/2^19 →
      ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
        Enclosed y (-({count-1}/64)) ({count-1}/64) ∧ Passing y ({stop}/64) := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,tiles⟩ := DommaschkRadialRibbonEntry.from_nested_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ u small => ?_⟩
  obtain ⟨k,_,entry⟩ := tiles u u.property φ small
  exact DommaschkRadialPassingCore.from_seed (by norm_num) small entry (in_ball k)
end PlasmaLean.Design.{name}
"""
    return name, source, ["in_ball", "from_nested_tori"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("ribbon", "incoming", "packets", "through", "output"):
        parser.add_argument("--" + flag, type=Path, required=True)
    parser.add_argument("--workers", choices=(1, 2, 3), type=int, default=1)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/radial-passing-core")
    args = parser.parse_args()
    env(args)
    through, packets, incoming = (json.loads(p.read_text()) for p in
                                  (args.through, args.packets, args.incoming))
    args.ribbon_key = digest(args.ribbon)
    count = through["outer_rows"]
    if (through["packet_sha256"] != args.ribbon_key or incoming["ribbon"] != args.ribbon_key
            or through["package"] != "RadialRibbonThroughFamilyCache" or not 2 <= count <= 332):
        parser.error("the signed ODE proof and field estimates must belong to this ribbon")
    roots = list(map(Path, through["import_paths"]))
    parent = admitted(roots[0], through["module"], through["key"])
    if f"PlasmaLean.Design.{through['module']}.from_seed" not in parent["theorems"]:
        parser.error("requires a joined signed solution on every original section ball")
    packets = [packets[str(k)] for k in range(4)]
    for k, packet in enumerate(packets):
        if packet["tile"] != k or packet["ribbon"] != args.ribbon_key:
            parser.error("unexpected physical packet")
        admitted(Path(packet["import_paths"][0]), packet["module"], packet["key"])
    selected = sorted((g for g in incoming["groups"] if g["stop"] <= min(count-1, 237)),
                      key=lambda g: g["start"])
    if not selected or [g["start"] for g in selected] != [0, *[g["stop"] for g in selected[:-1]]]:
        parser.error("the signed trajectory must cover at least the first complete field group")
    traces = load_ribbon(args.ribbon)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(group, args, traces, g, packets, clearance=Fraction(132, 125),
                               name_prefix="DommaschkRibbonFastCore", short_track=True)
                   for g in selected]
        groups = [f.result() for f in futures]
    keys = [through["key"], digest(DESIGN / "DommaschkRadialPassingCore.trace")]
    for g in groups:
        for tile in g["tiles"]:
            roots.extend(map(Path, tile["import_paths"]))
            keys.append(tile["key"])
    overlay = merge_import_roots(args.cache, roots, keys)
    item = joined(through, groups)
    root, record = compile_modules(args.cache / item[0], [item], [overlay], [args.version, keys],
                                   args, "RadialPassingCoreCache")
    report = {k: record[k] for k in ("module", "key", "theorems", "axioms", "wall_seconds")}
    report.update(ribbon=args.ribbon_key, through=through["key"], outer_rows=count,
                  core_rows=groups[-1]["stop"], field_upper="132/125", speed_lower="1/12",
                  import_paths=[str(root), str(overlay)], groups=groups)
    save(args.output, report)
    print(item[0], record["key"], flush=True)


if __name__ == "__main__":
    main()
