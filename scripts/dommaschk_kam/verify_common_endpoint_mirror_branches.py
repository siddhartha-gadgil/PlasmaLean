"""Attach certified full-height mirror branches to original birth lines on one fixed embedded pair."""
import argparse
import json
from pathlib import Path
import subprocess

from plan_endpoint_continuations import exterior
from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS, PACKAGE as FAMILY
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_secondary_mirror_band import BAND
from verify_signed_mirror_passage import merge_import_roots


def source(counts, observations):
    suffix = "_".join(str(counts[e]) for e in ENDPOINTS)
    family = "DommaschkCommonEndpointTraces" + suffix
    cal = "DommaschkCalibratedFamily" + suffix
    name = "DommaschkCommonMirrorBands" + "".join(e.upper() for e in observations) + "On" + suffix
    lines = ["module", "public import PlasmaLean.Design.DommaschkCommonBranchObservations",
             f"public import CalibratedFamilyCache.{cal}", f"public import {FAMILY}.{family}"]
    for _, (_, band, timing, _) in observations.items():
        lines.append(f"public import {BAND}.{timing}")
    lines.extend(["", "@[expose] public section", "noncomputable section",
                  f"namespace PlasmaLean.Design.{name}",
                  "open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch",
                  "open DommaschkLowerActionPath DommaschkEndpointMirrorBranch",
                  "open DommaschkCommonBranchObservations Theory.KAM",
                  f"open {family} (checkpoint)", "set_option maxRecDepth 32768",
                  "set_option maxHeartbeats 3200000", "set_option linter.style.longLine false"])
    claims = []
    for label, (stop, band, timing, limits) in observations.items():
        n = counts[label]
        (a, c), (d, b) = limits
        lines.append(f"""
def {label}Mirrors (y : ℝ → Plane) : Prop :=
  ∃ (f : {band}.fwdBranch y) (b : {band}.backBranch (fun t => y (-t))),
    (f.time {timing}.lowHeight ∈ Ioo ({a}/64) ({c}/64) ∧
      f.time {timing}.highHeight ∈ Ioo ({d}/64) ({b}/64)) ∧
    (b.time {timing}.lowHeight ∈ Ioo ({a}/64) ({c}/64) ∧
      b.time {timing}.highHeight ∈ Ioo ({d}/64) ({b}/64))

theorem {label}_on_path {{y : ℝ → Plane}}
    (path : Signed (MirrorEndpoint.start .{label}) (checkpoint .{label}).forwardRows
      (checkpoint .{label}).backwardRows ((checkpoint .{label}).length / 64) y) : {label}Mirrors y := by
  have hf : (checkpoint .{label}).forwardRows = {band}.fwdRows ++
      (checkpoint .{label}).forwardRows.drop {stop} := by with_unfolding_all rfl
  have hb : (checkpoint .{label}).backwardRows = {band}.backRows ++
      (checkpoint .{label}).backwardRows.drop {stop} := by with_unfolding_all rfl
  have forward := path.forward
  have backward := path.backward
  rw [hf] at forward
  rw [hb] at backward
  have room : ({b}/64:ℝ) < (checkpoint .{label}).length / 64 := by
    change ({b}/64:ℝ) < {n}/64
    norm_num
  obtain ⟨f⟩ := {band}.fwd_branch forward.prefix room
  obtain ⟨h⟩ := {band}.back_branch backward.prefix room
  have lf := {timing}.fwd_root_separation forward.prefix f
  have lb := {timing}.back_root_separation backward.prefix h
  exact ⟨f,h,⟨lf.1,lf.2.1⟩,⟨lb.1,lb.2.1⟩⟩

def {label}AtBirth (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA (MirrorEndpoint.radius .{label}) φ) ∧
    Signed (MirrorEndpoint.start .{label}) (checkpoint .{label}).forwardRows
      (checkpoint .{label}).backwardRows ((checkpoint .{label}).length / 64) y ∧ {label}Mirrors y

theorem {label}_of_passage {{uC zC uA zA : FA}} {{φ : ℝ}} (small : |φ| ≤ 1/2^19)
    (p : (checkpoint .{label}).Passage .{label} uC zC uA zA φ) : {label}AtBirth uC zC uA zA φ := by
  exact fixed_birth_observation rfl p (small.trans (by change (1/2^19:ℝ) ≤ {n}/64; norm_num))
    (by change 0 < {n}; norm_num) ({family}.row_counts .{label}).1 ({family}.row_counts .{label}).2
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (fun _ => {label}_on_path)
""")
        claims.extend([label+"_on_path", label+"_of_passage"])
    conj = " ∧ ".join(e+"AtBirth uC zC uA zA φ" for e in observations)
    lines.extend([f"theorem from_common_tori : ExistsOnPair checkpoint {cal}.Observed",
                  f"    (fun uC zC uA zA => ∀ φ, |φ| ≤ 1/2^19 → {conj}) := by",
                  f"  apply of_pair {cal}.same_embedded_tori",
                  "  intro uC zC uA zA pair φ small"])
    terms = []
    for e in observations:
        lines.extend([f"  have {e} := {e}_of_passage small (pair.passage .{e} φ",
                      "    (by simpa [MirrorEndpoint.width,MirrorEndpoint.opposite,azimuth] using small))"])
        terms.append(e)
    conclusion = terms[0] if len(terms) == 1 else "⟨" + ",".join(terms) + "⟩"
    lines.extend(["  exact " + conclusion, "", f"end PlasmaLean.Design.{name}", ""])
    return name, "\n".join(lines), [*claims, "from_common_tori"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", type=Path, required=True)
    parser.add_argument("--calibrated", type=Path, required=True)
    parser.add_argument("--branches", nargs="+", type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=ROOT/".lake/common-endpoint-mirror-branches")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    family, calibrated = [json.loads(p.read_text()) for p in (args.family, args.calibrated)]
    counts = family["lengths_each_direction"]
    suffix = "_".join(str(counts[e]) for e in ENDPOINTS)
    if (set(counts) != set(ENDPOINTS) or any(type(n) is not int or not 1<=n<=391 for n in counts.values())
            or family["module"] != "DommaschkCommonEndpointTraces"+suffix
            or calibrated["module"] != "DommaschkCalibratedFamily"+suffix
            or calibrated["lengths_each_direction"] != counts):
        parser.error("expected matching eight-label original checkpoint and calibrated family")
    keys, paths = [], []
    def accept(report, claims):
        roots = list(map(Path, report["import_paths"]))
        marker = admitted(roots[0],report["module"],report["key"])
        if any(f"PlasmaLean.Design.{report['module']}.{c}" not in marker["theorems"] for c in claims):
            parser.error("missing kernel declaration in "+report["module"])
        keys.append(marker["key"])
        paths.extend(roots)
    accept(family, ["same_nested_tori"])
    accept(calibrated, ["same_embedded_tori"])
    branches = {}
    parents = {}
    for path in args.branches:
        record = json.loads(path.read_text())
        label = record["endpoint"].lower()
        if label not in ("q0r478", "q0r523", "q0r531") or label in branches:
            parser.error("expected different phase-zero secondary branches")
        intervals, stop = exterior(label)
        birth = record["physical_birth"]
        timing = record["timing"]
        n = counts[label]
        checksum = digest(RECORD.with_name(f"bounce_frame_q0_u{label[3:]}.json.gz"))
        if (intervals[1] != intervals[-1] or n <= stop or birth["signed_length"] != n or
                family["endpoints"][label] != {"key": birth["parents"][1], "packet_sha256": checksum}
                or record["packet_sha256"] != checksum or record["key"]!=birth["parents"][0]
                or record["module"]!=f"Dommaschk{label.upper()}MirrorBranch{stop:03}"
                or timing["module"]!="Dommaschk"+label.upper()+"MirrorTimeSeparation"
                or birth["module"]!=f"Dommaschk{label.upper()}MirrorBandBirth{n:03}"):
            parser.error("the full mirror birth and the selected endpoint checkpoint must coincide")
        accept(record, ["fwd_branch", "back_branch"])
        accept(timing, ["fwd_root_separation","back_root_separation","fwd_time_derivative","back_time_derivative"])
        accept(birth, ["from_birth"])
        branches[label] = (stop,record["module"],timing["module"],intervals[1])
        parents[label] = {"branch":record["key"],"timing":timing["key"],"physical_birth":birth["key"],
                          "brackets_in_64ths":intervals[1]}
    def lake(*cmd):
        return subprocess.check_output(["lake","env",*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake("lean","--print-prefix"))/"bin/lean")
    args.lean_path = lake("printenv","LEAN_PATH")
    keys.extend([lake("lean","--version"),digest(DESIGN/"DommaschkCommonBranchObservations.trace")])
    overlay = merge_import_roots(args.cache, paths, keys)
    item = source(counts,branches)
    root, marker = compile_modules(args.cache/item[0],[item],[overlay],keys,args,"CommonMirrorBranchCache")
    result = {k:v for k,v in marker.items() if k!="artifacts"}
    result.update(family_key=family["key"],calibrated_key=calibrated["key"],branches=parents,
                  lengths_each_direction=counts,signed_rows=2*sum(counts.values()),
                  import_paths=[str(root),str(overlay)])
    save(args.output,result)
    print(item[0],marker["key"],flush=True)


if __name__ == "__main__":
    main()
