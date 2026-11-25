"""Attach the connected original-birth action level to the checked faces, section passage and tube signs."""
import argparse
import json
from pathlib import Path
import re
import time

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_accessible_birth import checked
from verify_signed_mirror_passage import merge_import_roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--faces", required=True, type=Path)
    parser.add_argument("--accessible", required=True, type=Path)
    parser.add_argument("--attainment", required=True, type=Path)
    parser.add_argument("--wait", action="store_true", help="wait for the attainment receipt")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/connected-action-level")
    args = parser.parse_args()
    faces = json.loads(args.faces.read_text())
    access = json.loads(args.accessible.read_text())
    while args.wait and not args.attainment.is_file():
        time.sleep(15)
    attainment = json.loads(args.attainment.read_text())
    match = re.fullmatch(r"DommaschkSectorFacesOn(\d+(?:_\d+){7})", faces["module"])
    if match is None or not re.fullmatch(r"DommaschkRadialAccessibleBirth\d{3}", access["module"]):
        parser.error("expected physical face comparison and accessible-birth receipts")
    suffix = match.group(1)
    full = attainment.get("through_key") is not None
    expected = ("DommaschkProvedRadialAttainmentOn" if full else "DommaschkRadialAttainmentOn") + suffix
    if attainment["module"] != expected:
        parser.error("require the same comparison checkpoint for both endpoint and trajectory results")
    roots = [*checked(faces, "from_nested_tori"), *checked(access, "in_ball"), *checked(attainment, "sections")]
    name = ("DommaschkPhysicalConnectedLevelOn" if full else "DommaschkConnectedLevelOn") + suffix
    joins = attainment["module"]
    claims = ["from_tracks"]
    closed = ""
    if full:
        checked(attainment, "through")
        claims.append("on_nested_tori")
        closed = f"theorem on_nested_tori : OnNestedTori := from_tracks {joins}.through\n"
    source = f"""module
public import PlasmaLean.Design.DommaschkConnectedActionLevel
public import RadialSectorFacesCache.{faces['module']}
public import RadialAccessibleBirthCache.{access['module']}
public import RadialActionAttainmentCache.{joins}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkSectorAction DommaschkConnectedActionLevel
set_option maxRecDepth 16000
set_option linter.style.longLine false

def OnNestedTori : Prop := ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧ Crossing uC zC uA zA

theorem from_tracks (joined : {joins}.Joined) : OnNestedTori := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,proof⟩ := {faces['module']}.from_nested_tori
  have every (φ : Phase) := proof (φ:ℝ) (abs_le.mpr φ.property)
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,crossing_of_sector ?_ (fun φ => (every φ).2.2) ?_⟩
  · apply sector_of_sections ec ea (fun φ => (every φ).1) ({joins}.sections joined)
    intro φ Y born paths signs
    exact (every φ).2.1 Y born paths (fun u => (signs u).low) (fun u => (signs u).back)
      (fun u => (signs u).front)
  · intro p
    obtain ⟨k,_,e⟩ := (every p.1).1 p.2
    exact DommaschkRadialAccessibleBirth.from_seed (abs_le.mpr p.1.property) e
      ({access['module']}.in_ball k)
{closed}
end PlasmaLean.Design.{name}
"""
    env(args)
    parents = [args.version, faces["key"], access["key"], attainment["key"],
               digest(DESIGN / "DommaschkConnectedActionLevel.trace")]
    overlay = merge_import_roots(args.cache, roots, parents)
    base, marker = compile_modules(args.cache / name, [(name, source, claims)], [overlay], parents, args,
                                   "ConnectedActionLevelCache")
    result = {k: marker[k] for k in ("module", "key", "theorems", "axioms", "wall_seconds", "peak_rss_kib")}
    result.update(faces_key=faces["key"], accessible_key=access["key"], attainment_key=attainment["key"],
                  through_key=attainment["through_key"], import_paths=list(map(str, [base, overlay])))
    save(args.output, result)
    print(name, marker["key"])


if __name__ == "__main__":
    main()
