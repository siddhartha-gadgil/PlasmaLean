"""Connect the four signed section solutions to a submirror interval containing every original birth."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def checked(report, theorem):
    roots = list(map(Path, report["import_paths"]))
    name = report["module"]
    marker = admitted(roots[0], name, report["key"])
    if f"PlasmaLean.Design.{name}.{theorem}" not in marker["theorems"]:
        raise ValueError(f"missing {name}.{theorem}")
    return roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", required=True, type=Path)
    parser.add_argument("--below", required=True, type=Path, nargs=4)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/radial-accessible-birth")
    args = parser.parse_args()
    path = json.loads(args.through.read_text())
    count = path["outer_rows"]
    roots = checked(path, "from_seed")
    if not 16 <= count <= 332 or path["package"] != "RadialRibbonThroughFamilyCache":
        parser.error("requires a four-tile ODE proof through at least sixteen slabs each way")
    estimates = sorted((json.loads(f.read_text()) for f in args.below), key=lambda e: e["tile"])
    for tile, est in enumerate(estimates):
        if (est["tile"] != tile or est["start"] != 0 or est["stop"] != 8 or est["tracks"] != 8
                or est["mode"] != "below" or est["ribbon"] != path["packet_sha256"]):
            parser.error("requires four initial eight-row signed exclusions from the same ribbon")
        roots.extend(checked(est, "tracked"))
    env(args)
    name = f"DommaschkRadialAccessibleBirth{count:03}"
    through = path["module"]
    source = f"module\npublic import {path['package']}.{through}\n"
    for est in estimates:
        source += f"public import RadialRibbonBelowRowsCache.{est['module']}\n"
    source += f"""public import PlasmaLean.Design.DommaschkRadialAccessibleBirth

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkRadialRibbonEntry
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkRadialAccessibleBirth DommaschkRadialActionAlternative DommaschkNativeWellAction
open DommaschkRibbonFirstMirrors
set_option maxRecDepth 14000
set_option linter.style.longLine false

theorem in_ball (k : Fin 4) (x : Plane) (entry : x ∈ stateSet (seed k)) :
    ∃ y : ℝ → Plane, y 0 = x ∧ Accessible y := by
  obtain ⟨y,starts,e,rows⟩ := {through}.from_seed k x entry
  have low : Below y 0 (8/64) (DommaschkFirstMirrorLaunchSign.height true) := by
    fin_cases k
"""
    for est in estimates:
        source += f"    · simpa only [zero_div] using {est['module']}.tracked (rows.mono (by norm_num))\n"
    source += f"""  refine ⟨y, starts, e.mono (Icc_subset_Icc (by norm_num) (by norm_num)), ?_⟩
  intro t ht
  have h := low.signed t (by convert ht using 1; norm_num)
  change DommaschkMirrorTubeCrossing.strength t (y t) < level
  convert h using 1; norm_num [level, DommaschkFirstMirrorLaunchSign.height]

theorem from_nested_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ (φ : ℝ) (u : Radius), |φ| ≤ 1/2^19 →
      ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧ Accessible y := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,tiles⟩ := DommaschkRadialRibbonEntry.from_nested_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ u small => ?_⟩
  obtain ⟨k,_,e⟩ := tiles u u.property φ small
  exact DommaschkRadialAccessibleBirth.from_seed small e (in_ball k)
end PlasmaLean.Design.{name}
"""
    keys = [args.version, path["key"], [e["key"] for e in estimates],
            digest(DESIGN / "DommaschkRadialAccessibleBirth.trace")]
    overlay = merge_import_roots(args.cache, roots, keys)
    claims = ["in_ball", "from_nested_tori"]
    base, record = compile_modules(args.cache / name, [(name, source, claims)], [overlay], keys, args,
                                   "RadialAccessibleBirthCache")
    out = {k: record[k] for k in ("module", "key", "theorems", "axioms", "wall_seconds", "peak_rss_kib")}
    out.update(through_key=path["key"], below_keys=[e["key"] for e in estimates],
               import_paths=list(map(str, [base, overlay])))
    save(args.output, out)
    print(name, record["key"])


if __name__ == "__main__":
    main()
