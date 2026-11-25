"""Attach uniform first-well action windows to the original physical height-action rectangle."""
import argparse
import json
from pathlib import Path
import re
import time

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def theorem(rectangle, faces, proved):
    name="Dommaschk"+("Proved" if proved else "")+"RadialFirstWellActionWindows"
    family="(∃ family : Family uC zC uA zA, Samples family)"
    through="DommaschkRadialRibbonMirrorBand.Through"
    result=family if proved else f"({through} → {family})"
    finish=f" secured {rectangle}.through" if proved else " secured"
    src=f'''module
public import PlasmaLean.Design.DommaschkRadialActionWindows
public import RadialHeightActionRectangleCache.{rectangle}
public import RadialSectorFacesCache.{faces}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Theory.KAM WEll1Z2 DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer
open DommaschkSectorHeightCrossings DommaschkRadialActionWindows DommaschkSectorAction
open DommaschkRadialSectionAction DommaschkSectorActionBand DommaschkMirrorLaunch
set_option linter.all false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- All phases, admissible heights and prescribed targets share the same radial sampling width
for each tolerance, on the true first wells of a single original three-coordinate family. -/
theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧ {result} := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,inputs⟩ := {faces}.from_nested_tori
  have items (φ : Phase) := inputs φ (abs_le.mpr φ.2)
  have faces (φ : Phase) := (items φ).2.2
  have secured (path : {through}) : {family} := by
    obtain ⟨⟨family⟩,_⟩ := {rectangle}.from_entries ec ea (fun φ => (items φ).1) faces path
    exact ⟨family,of_faces family faces⟩
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,{finish}⟩

end PlasmaLean.Design.{name}
'''
    return name,src,["from_nested_tori"]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--rectangle",type=Path,required=True)
    p.add_argument("--faces",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--wait",action="store_true")
    p.add_argument("--cache",type=Path,default=ROOT/".lake/radial-first-well-action-windows")
    args=p.parse_args()
    while args.wait and not args.rectangle.exists():
        time.sleep(15)
    rect,faces=(json.loads(f.read_text()) for f in (args.rectangle,args.faces))
    proved=rect["module"]=="DommaschkProvedRadialHeightActionRectangle"
    if (rect["module"] not in ("DommaschkRadialHeightActionRectangle","DommaschkProvedRadialHeightActionRectangle")
            or not re.fullmatch(r"DommaschkSectorActionBandOn\d+(?:_\d+){7}",faces["module"])
            or rect["parents"][1]!=faces["key"] or proved!=("through_key" in rect)):
        p.error("expected a matched original N192 rectangle and its authenticated physical endpoint faces")
    parents=[rect["key"],faces["key"]]
    for r in (rect,faces):
        admitted(Path(r["import_paths"][0]),r["module"],r["key"])
    roots=[Path(s) for r in (rect,faces) for s in r["import_paths"]]
    links=merge_import_roots(args.cache,roots,parents)
    env(args)
    term=theorem(rect["module"],faces["module"],proved)
    claims=["PlasmaLean.UniformRadialWindow."+t for t in ("uniform","lipschitz","HasInterval.volume")]
    claims+=["PlasmaLean.Design.DommaschkRadialActionWindows.of_faces",f"PlasmaLean.Design.{term[0]}.from_nested_tori"]
    root,rec=compile_modules(args.cache/term[0],[term],[links],
        [args.version,parents,digest(DESIGN/"DommaschkRadialActionWindows.trace")],args,
        "RadialFirstWellActionWindowsCache",qualified_claims=claims)
    result={k:v for k,v in rec.items() if k!="artifacts"}
    result.update(parents=parents,through_key=rect.get("through_key"),import_paths=[str(root),str(links)])
    save(args.output,result)
    print(term[0],rec["key"],flush=True)


if __name__=="__main__":
    main()
