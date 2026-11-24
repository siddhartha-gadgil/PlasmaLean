"""Use the common embedded torus pair to control original pilot birth phases simultaneously."""
import argparse
import json
from pathlib import Path
import re
import subprocess
from string import Template

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def source(previous, suffix):
    name = "DommaschkCommonLaunchPhases" + suffix
    fam = "DommaschkCommonEndpointTraces" + suffix
    src = f"""module
public import PlasmaLean.Design.DommaschkCompactLaunchPhases
public import RegularBirthArcsCache.{previous}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkFirstMirrorWell DommaschkPhaseZeroRegularBirth
open DommaschkCompactLittlejohnArc DommaschkCompactLaunchPhases DommaschkCommonLittlejohnTime
open DommaschkCartesianAngleFlow DommaschkCommonPilotObservables DommaschkSignedTraceDomain
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 DommaschkKamC KamNewton
open DommaschkMirrorLaunch
open {fam} (checkpoint)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false

theorem original_phases :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      Uniform (location uC zC uA zA (47/100) '' Icc (-(1/2^19):ℝ) (1/2^19)) ∧
      ∀ φ, |φ| ≤ (1/2^19:ℝ) → ∃ x y,
        y φ = coordinates.symm (birth uC zC uA zA (47/100) φ) ∧
        DommaschkSignedObservable.Path (checkpoint .q0r470).length
          (checkpoint .q0r470).forwardExit (checkpoint .q0r470).backwardExit
          (checkpoint .q0r470).forwardRows (checkpoint .q0r470).backwardRows x y ∧ Population (316/64) y := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,_,each⟩ := {previous}.pilot
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,?_,?_⟩
  · apply uniform_launches (by norm_num) ec ea
    intro φ small
    obtain ⟨x,y,src,path,_,pop⟩ := each φ (abs_le.mpr small)
    have reg := on_path path (by change 0 < 391; norm_num) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) rfl rfl
    have place : DommaschkFirstMirrorWell.point y φ = location uC zC uA zA (47/100) φ := by
      unfold DommaschkFirstMirrorWell.point location
      rw [src]
      rfl
    rw [← place]
    have inside : φ ∈ Icc (-(316/64:ℝ)) (316/64) := by
      constructor <;> linarith [small.1,small.2]
    refine ⟨in_regular (reg φ ?_) φ,(pop.1 φ inside).2.2.1⟩
    change -(391:ℝ)/64 ≤ φ ∧ φ ≤ 391/64
    constructor <;> linarith [small.1,small.2]
  · intro φ hφ
    obtain ⟨x,y,src,path,_,pop⟩ := each φ hφ
    exact ⟨x,y,src,path,pop⟩

end PlasmaLean.Design.{name}
"""
    return (name, src, ["original_phases"])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--regular-arcs", type=Path, required=True)
    p.add_argument("--all-arcs", action="store_true", help="give every admitted trajectory one shared horizon")
    p.add_argument("--cache", type=Path, default=ROOT/".lake/uniform-launch-phases")
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    r = json.loads(a.regular_arcs.read_text())["birth"]
    match = re.fullmatch(r"DommaschkRegularBirthArcs(391(?:_[1-9][0-9]*){7})", r["module"])
    if not match:
        p.error("an authentic regular-arc receipt for the 391-row q0r470 pilot is required")
    paths = list(map(Path, r["import_paths"]))
    admitted(paths[0], r["module"], r["key"])

    def lake(*cmd):
        return subprocess.check_output(["lake","env",*cmd],cwd=ROOT,text=True).strip()

    a.lean = str(Path(lake("lean","--print-prefix"))/"bin/lean")
    a.lean_path = lake("printenv","LEAN_PATH")
    keys = [lake("lean","--version"),digest(DESIGN/"DommaschkCompactLaunchPhases.trace"),r["key"]]
    item = source(r["module"], match[1])
    root, proof = compile_modules(a.cache/item[0], [item], paths, keys, a, "CommonLaunchPhaseCache")
    out = {k: proof[k] for k in ["module","key","theorems","axioms","wall_seconds","peak_rss_kib"]}
    out.update(original_arcs=r["key"],import_paths=list(map(str,[root,*paths])))
    if a.all_arcs:
        name = "DommaschkEveryLaunchArc" + match[1]
        template = Path(__file__).parent/"templates/compact_every_launch_arc.lean.tpl"
        body = Template(template.read_text()).substitute(
            NAME=name, PHASE=item[0], FAMILY="DommaschkCommonEndpointTraces"+match[1])
        deps = [*keys, proof["key"], digest(DESIGN/"DommaschkEnclosedLaunchArcs.trace")]
        task = (name, body, ["every_arc"])
        top, physical = compile_modules(a.cache/name, [task], [root,*paths], deps, a, "EveryLaunchArcCache")
        out["all_arcs"] = {k: physical[k] for k in ["module","key","theorems","axioms","wall_seconds","peak_rss_kib"]}
        out["all_arcs"]["import_paths"] = list(map(str, [top,root,*paths]))
    save(a.output,out)
    result = out.get("all_arcs",out)
    print(result["module"], result["key"])


if __name__ == "__main__":
    main()
