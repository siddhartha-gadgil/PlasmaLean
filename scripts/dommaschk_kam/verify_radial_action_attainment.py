"""Attach the complete signed tube observations to the physical sector action criterion."""
import argparse
import json
from pathlib import Path
import re
import time

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_physical_trace_slabs import ROOT, save
from verify_radial_accessible_birth import checked
from verify_signed_mirror_passage import merge_import_roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sector", required=True, type=Path)
    parser.add_argument("--signs", required=True, type=Path)
    parser.add_argument("--through", type=Path, help="authenticated four-tile 332-row signed ODE proof")
    parser.add_argument("--wait", action="store_true", help="wait for the through-proof receipt to be published")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/radial-action-attainment")
    args = parser.parse_args()
    if args.wait and args.through is None:
        parser.error("--wait requires --through")
    sector = json.loads(args.sector.read_text())
    signs = json.loads(args.signs.read_text())
    match = re.fullmatch(r"DommaschkSectorTargetOn(\d+(?:_\d+){7})", sector["module"])
    if not match or signs["module"] != "DommaschkRadialRibbonNoGrazingFamily":
        parser.error("expected the physical sector comparison and the complete four-tile mirror proofs")
    roots = [*checked(sector, "from_sections"), *checked(signs, "signs_and_simple")]
    env(args)
    keys = [args.version, sector["key"], signs["key"]]
    sign = signs["module"]
    imports = [f"RadialSectionTargetCache.{sector['module']}", f"RadialRibbonNoGrazingFamilyCache.{sign}"]
    name = "DommaschkRadialAttainmentOn" + match.group(1)
    claims = ["sections", "from_tracks"]
    physical = ""
    if args.through:
        while args.wait and not args.through.is_file():
            time.sleep(15)
        path = json.loads(args.through.read_text())
        if (path["module"] != "DommaschkRadialRibbonThrough" or path["outer_rows"] != 332
                or path["packet_sha256"] != signs["ribbon"] or path["package"] != "RadialRibbonThroughFamilyCache"):
            parser.error("a complete through-proof for the same signed 332-row packet is required")
        roots += checked(path, "from_seed")
        keys.append(path["key"])
        imports += [f"{path['package']}.{path['module']}"]
        name = "DommaschkProvedRadialAttainmentOn" + match.group(1)
        physical = f"""
theorem through : Joined := by
  intro k x hx
  obtain ⟨y, start, path, tracks⟩ := {path['module']}.from_seed k x hx
  exact ⟨y, start, path, by fin_cases k <;> exact tracks⟩

theorem on_nested_tori : OnNestedTori := from_tracks through
"""
        claims += ["through", "on_nested_tori"]
    source = "module\n" + "".join(f"public import {m}\n" for m in imports)
    source += f"""
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkRadialRibbonEntry DommaschkRadialFamilyContinuity
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkRadialSectionAction DommaschkSectorAction
set_option linter.style.longLine false

/-- The original signed physical solve with membership in every requested canonical tube. -/
def Joined : Prop := ∀ (k : Fin 4) (x : Plane), x ∈ stateSet (seed k) →
  ∃ y : ℝ → Plane, y 0 = x ∧ Enclosed y (-cap) cap ∧
    DommaschkLowerActionPath.Tracks ({sign}.forwardRows k) ({sign}.backwardRows k) 332 y

theorem sections (joined : Joined) : Sections (fun y => Signs y ∧ Simple y) := by
  intro k x hx
  obtain ⟨y, start, path, tracks⟩ := joined k x hx
  exact ⟨y, start, path, {sign}.signs_and_simple k path tracks⟩

def OnNestedTori : Prop := ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧ Sector uC zC uA zA

theorem from_tracks (joined : Joined) : OnNestedTori := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,sector⟩ := {sector['module']}.from_sections
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,sector (sections joined)⟩
{physical}
end PlasmaLean.Design.{name}
"""
    overlay = merge_import_roots(args.cache, roots, keys)
    base, record = compile_modules(args.cache / name, [(name, source, claims)], [overlay], keys, args,
                                   "RadialActionAttainmentCache")
    report = {k: record[k] for k in ("module", "key", "axioms", "theorems", "wall_seconds", "peak_rss_kib")}
    report.update(sector_key=sector["key"], signs_key=signs["key"], through_key=keys[3] if args.through else None,
                  import_paths=list(map(str, [base, overlay])))
    save(args.output, report)
    print(name, record["key"])


if __name__ == "__main__":
    main()
