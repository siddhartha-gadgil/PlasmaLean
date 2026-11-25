"""Join the physical first-well crossings and sampling bounds on one pair of original tori."""
import argparse
import json
from pathlib import Path
import re

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("through", "rectangle", "faces", "output"):
        parser.add_argument("--" + flag, required=True, type=Path)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/completed-radial-sector")
    args = parser.parse_args()
    through, rectangle, faces = (json.loads(path.read_text()) for path in
                                (args.through, args.rectangle, args.faces))
    if (through["module"] != "DommaschkRadialRibbonThrough" or through["outer_rows"] != 332
            or through["package"] != "RadialRibbonThroughFamilyCache"
            or rectangle["module"] != "DommaschkProvedRadialHeightActionRectangle"
            or rectangle.get("through_key") != through["key"]
            or rectangle["parents"][1:] != [faces["key"], through["key"]]
            or not re.fullmatch(r"DommaschkSectorActionBandOn\d+(?:_\d+){7}", faces["module"])):
        parser.error("requires the full original physical join and its verified height and action bounds")
    roots = []
    for report, claims in ((through, ["from_seed"]), (rectangle, ["from_entries", "through"]),
                           (faces, ["from_nested_tori"])):
        paths = list(map(Path, report["import_paths"]))
        marker = admitted(paths[0], report["module"], report["key"])
        if any("PlasmaLean.Design." + report["module"] + "." + c not in marker["theorems"] for c in claims):
            parser.error("missing parent theorem in " + report["module"])
        roots.extend(paths)
    name = "DommaschkCertifiedRadialSector"
    rect, face = rectangle["module"], faces["module"]
    source = f"""module
public import PlasmaLean.Design.DommaschkRadialActionWindows
public import RadialHeightActionRectangleCache.{rect}
public import RadialSectorFacesCache.{face}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Theory.KAM WEll1Z2 DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer
open DommaschkSectorHeightAction DommaschkSectorHeightCrossings DommaschkRadialActionWindows
open DommaschkRadialSectionAction DommaschkSectorActionBand DommaschkSectorAction DommaschkNativeWellAction
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.style.longLine false

/-- One nested embedded pair and one jointly continuous true first-well family simultaneously
supply radial sampling intervals and connected physical levels for all admissible prescriptions. -/
theorem on_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∃ family : Family uC zC uA zA, Samples family ∧
        ∀ H J : Phase → ℝ, Continuous H → Continuous J → (∀ φ, |H φ - level| ≤ delta) →
          (∀ φ, J φ ∈ Icc lowTarget highTarget) → Crossing uC zC uA zA H J := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,inputs⟩ := {face}.from_nested_tori
  have items (φ : Phase) := inputs φ (abs_le.mpr φ.2)
  have signs (φ : Phase) : BandFaces uC zC uA zA φ := (items φ).2.2
  obtain ⟨⟨family⟩,_⟩ := {rect}.from_entries ec ea (fun φ => (items φ).1) signs {rect}.through
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,family,of_faces family signs,crossing family signs⟩

end PlasmaLean.Design.{name}
"""
    env(args)
    parents = [through["key"], rectangle["key"], faces["key"]]
    keys = [args.version, parents, digest(DESIGN / "DommaschkRadialActionWindows.trace")]
    links = merge_import_roots(args.cache, roots, keys)
    root, result = compile_modules(args.cache / name, [(name, source, ["on_nested_tori"])],
                                   [links], keys, args, "CertifiedRadialSectorCache")
    report = {k: result[k] for k in ("module", "key", "theorems", "axioms", "wall_seconds", "peak_rss_kib")}
    report.update(ribbon=through["packet_sha256"], parents=parents, import_paths=[str(root), str(links)])
    save(args.output, report)
    print(name, report["key"], flush=True)


if __name__ == "__main__":
    main()
