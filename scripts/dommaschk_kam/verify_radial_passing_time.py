"""Attach Cartesian mirror travel clocks to trajectories through the original birth sector."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/radial-passing-time")
    args = parser.parse_args()
    env(args)
    core = json.loads(args.core.read_text())
    n, stop = core["outer_rows"], core["core_rows"]
    expected = f"DommaschkRadialPassing{n:03}Core{stop:03}"
    if core["module"] != expected or not 1 <= stop < n <= 332:
        parser.error("requires the signed passing-core theorem on the original radial launch family")
    paths = list(map(Path, core["import_paths"]))
    marker = admitted(paths[0], expected, core["key"])
    if f"PlasmaLean.Design.{expected}.from_nested_tori" not in marker["theorems"]:
        parser.error("the passing-core package must identify the original physical births")
    half_time = (Fraction(stop, 64) - Fraction(1, 2**19)) / 2
    name = f"DommaschkRadialPassingTime{n:03}Core{stop:03}"
    source = f"""module
public import RadialPassingCoreCache.{expected}
public import PlasmaLean.Design.DommaschkRadialPassingTime

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkRadialRibbonEntry
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkRadialPassingTime DommaschkRadialActionAlternative DommaschkFirstMirrorLaunchSign
open DommaschkRadialFamilyContinuity DommaschkRadialPassingCore
set_option linter.style.longLine false

theorem from_nested_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ (φ : ℝ) (u : Radius), |φ| ≤ 1/2^19 →
      ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
        Enclosed y (-({n-1}/64)) ({n-1}/64) ∧ Passing y ({stop}/64) ∧
          ∀ h ∈ Icc (height false : ℝ) (height true : ℝ), ClockOn y ({stop}/64) h φ ∧
            ∀ τ : ℝ, |τ| ≤ ({half_time}) → ∃! t : Icc (-({stop}/64) : ℝ) ({stop}/64), clock y h φ t = τ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,inputs⟩ := {expected}.from_nested_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ u small => ?_⟩
  obtain ⟨y,start,path,passing⟩ := inputs φ u small
  have born : φ ∈ Icc (-({stop}/64)) ({stop}/64) := abs_le.mp (small.trans (by norm_num))
  refine ⟨y,start,path,passing,fun h hh => ?_⟩
  have c := clock_on path (by norm_num : ({stop}/64 : ℝ) ≤ ({n-1}/64)) passing hh born
  exact ⟨c, fun τ ht => times_about_birth c born (by linarith only [small]) ht⟩
end PlasmaLean.Design.{name}
"""
    parents = [args.version, core["key"], digest(DESIGN / "DommaschkRadialPassingTime.trace")]
    links = merge_import_roots(args.cache, paths, parents)
    root, result = compile_modules(args.cache / name, [(name, source, ["from_nested_tori"])],
                                   [links], parents, args, "RadialPassingTimeCache")
    report = {key: result[key] for key in ("module", "key", "theorems", "axioms", "wall_seconds")}
    report.update(core=core["key"], outer_rows=n, core_rows=stop, half_time=str(half_time), rate_bounds=["1/2", "15"],
                  import_paths=[str(root), str(links)])
    save(args.output, report)
    print(name, report["key"], flush=True)


if __name__ == "__main__":
    main()
