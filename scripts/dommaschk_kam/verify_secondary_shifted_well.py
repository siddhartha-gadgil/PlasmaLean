"""Join first-mirror branches and shifted physical action cells on one secondary birth trajectory."""
import argparse
import fcntl
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, HERE, ROOT, digest, save
from verify_secondary_action_cover import header, package
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


NAME = "DommaschkQ0R478ShiftedFirstWell"
PACKAGE = "SecondaryShiftedWellCache"


def birth(n, signed, cover=None, shoulders=False):
    provider = NAME + ("Shoulders" if shoulders else "")
    provider_package = "SecondaryWellShoulderCache" if shoulders else PACKAGE
    name = f"{provider}Birth{n:03}" + ("Full" if cover else "")
    full_module = "DommaschkLowerCoverQ0R478L005R649"
    links = [f"{provider_package}.{provider}", f"{SIGNED_PACKAGE}.{signed}"]
    if cover:
        links.append(f"{package(5,649)}.{full_module}")
    src = header(name, links)
    prop = "Complete" if cover else "Result"
    src += f"""
open {signed} {provider} Theory.KAM Contract Forms Fields.VacuumBoozer WEll1Z2 DommaschkKamC KamNewton
abbrev Property (y : ℝ → Plane) := Signed endpoint.start forwardRows backwardRows ({n}/64) y ∧ {prop} y

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (e : SectionEntry endpoint uC zC uA zA φ) :
    AtBirth endpoint uC zC uA zA φ Property := by
  have fmatch : forwardRows = DommaschkQ0R478MirrorBranch327.fwdRows ++ forwardRows.drop 327 := by with_unfolding_all rfl
  have bmatch : backwardRows = DommaschkQ0R478MirrorBranch327.backRows ++ backwardRows.drop 327 := by with_unfolding_all rfl
  have actual := from_passage (by norm_num) fmatch bmatch ({signed}.from_entry e)
"""
    if cover:
        src += f"""
  obtain ⟨s,a,y,hs,ang,src,d,j,path,res⟩ := actual
  have f := path.forward
  have b := path.backward
  rw [fmatch] at f
  rw [bmatch] at b
  have covered := {full_module}.cover (tracks_of_take (take_rows f.prefix 322) (take_rows b.prefix 322))
  rw [{full_module}.Covered,show {full_module}.start = (-322/64:ℝ) by norm_num [{full_module}.start]] at covered
  exact ⟨s,a,y,hs,ang,src,d,j,path,complete_of_core res covered⟩
"""
    else:
        src += "  exact actual\n"
    src += f"""
theorem from_nested_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ - azimuth endpoint.opposite| ≤ endpoint.width → AtBirth endpoint uC zC uA zA φ Property := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,entry⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ h => from_entry (entry endpoint φ h)⟩

end PlasmaLean.Design.{name}
"""
    return name, src, ["from_entry", "from_nested_tori"]


def checked_paths(r):
    paths = list(map(Path, r["import_paths"]))
    admitted(paths[0], r["module"], r["key"])
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upper-well", type=Path, required=True)
    parser.add_argument("--shifted-birth", type=Path, required=True)
    parser.add_argument("--clearance", type=Path, help="add the two 285-slab outer action contributions")
    parser.add_argument("--signed", type=Path)
    parser.add_argument("--full-cover", type=Path)
    parser.add_argument("--cache", type=Path, default=ROOT/".lake/secondary-shifted-well")
    parser.add_argument("--output", type=Path, required=True)
    a = parser.parse_args()
    # The independent final receipts can become ready together. Replay one long physical
    # birth at a time so their large Lean imports use one workstation allocation.
    if a.signed:
        a.cache.mkdir(parents=True, exist_ok=True)
        birth_lock = (a.cache/"signed-birth.lock").open("a")
        fcntl.flock(birth_lock, fcntl.LOCK_EX)
    upper, short = [json.loads(p.read_text()) for p in [a.upper_well, a.shifted_birth]]
    packet = digest(load(478)[1])
    if (upper["module"] != "DommaschkQ0R478LowerFirstWell" or upper["packet_sha256"] != packet
            or short["module"] != "DommaschkShiftedActionBirth267R032Of048"):
        parser.error("expected matching q0r478 upper-well and shifted 32-pair action proofs")
    if a.full_cover and not a.signed:
        parser.error("the final target needs both the signed trajectory and the full original cover")

    def lake(*cmd):
        return subprocess.check_output(["lake", "env", *cmd], cwd=ROOT, text=True).strip()

    a.lean = str(Path(lake("lean", "--print-prefix"))/"bin/lean")
    a.lean_path = lake("printenv", "LEAN_PATH")
    keys = [lake("lean", "--version"), digest(DESIGN/"DommaschkSecondaryHeightCollar.trace"),
            upper["key"], short["key"], packet]
    overlay = merge_import_roots(a.cache/"parents", checked_paths(upper)+checked_paths(short), keys)
    item = (NAME, (HERE/"templates/secondary_shifted_well.lean.tpl").read_text(),
            ["complete_of_core", "on_path", "from_passage"])
    root, record = compile_modules(a.cache/NAME, [item], [overlay], keys, a, PACKAGE)
    report = {k: record[k] for k in ["key", "module", "theorems", "axioms", "wall_seconds", "peak_rss_kib"]}
    links = [root, overlay]
    report.update(import_paths=list(map(str, links)), short_mass=short["lower_mass"],
                  height_drop=short["height_drop"], packet_sha256=packet,
                  shifted_short_key=short["key"], upper_well_key=upper["key"])
    if a.clearance:
        gap = json.loads(a.clearance.read_text())
        if ((gap["module"], gap["drop"], gap["packet_sha256"]) !=
                ("DommaschkQ0R478Drop1Over270000SubmirrorPrefix317", "1/270000", packet)):
            parser.error("the two outer action intervals use the 317-pair quantitative clearance")
        theory = ROOT/".lake/build/lib/lean/PlasmaLean/Theory/Kinetic/MirrorActionShoulders.trace"
        keys = [*keys, record["key"], gap["key"], digest(theory)]
        shoulder_overlay = merge_import_roots(a.cache/"shoulders", [*links, *checked_paths(gap)], keys)
        item = (NAME+"Shoulders", (HERE/"templates/secondary_shifted_shoulders.lean.tpl").read_text(),
                ["mass_on_core", "on_path", "from_passage"])
        root, record = compile_modules(a.cache/item[0], [item], [shoulder_overlay], keys, a,
                                       "SecondaryWellShoulderCache")
        links = [root, shoulder_overlay]
        report.update({k: record[k] for k in ["key", "module", "theorems", "axioms", "wall_seconds",
                                               "peak_rss_kib"]})
        report.update(import_paths=list(map(str, links)), strict_floor="43/100", clearance_key=gap["key"])
    if a.signed:
        signed = json.loads(a.signed.read_text())
        n = signed["length_each_direction"]
        pm = f"DommaschkSignedPrefixQ0R478{n:03}"
        if n <= 327 or signed["module"] != pm or signed["packet_sha256"] != packet:
            parser.error("the true signed q0r478 path must extend strictly beyond 327/64")
        paths = list(map(Path, [signed["proof_root"], signed["import_path"]]))
        admitted(paths[0], pm, signed["key"])
        more = [*keys, record["key"], signed["key"]]
        if a.full_cover:
            cover = json.loads(a.full_cover.read_text())
            if ((cover["module"], cover["package"], cover["block_range"], cover["packet_sha256"]) !=
                    ("DommaschkLowerCoverQ0R478L005R649", package(5,649), [5,649], packet)):
                parser.error("the complete original q0r478 lower core covers blocks [5,649)")
            paths.extend(checked_paths(cover))
            more.append(cover["key"])
        merged = merge_import_roots(a.cache/"birth", [*links, *paths], more)
        item = birth(n, pm, a.full_cover, bool(a.clearance and not a.full_cover))
        rb, final = compile_modules(a.cache/item[0], [item], [merged], more, a, "ShiftedWellBirthCache")
        report["birth"] = {k: final[k] for k in ["module", "key", "axioms", "theorems", "wall_seconds"]}
        report["birth"].update(signed_length=n, signed_key=signed["key"], full_target=bool(a.full_cover),
                               import_paths=list(map(str, [rb, merged])))
    save(a.output, report)
    result = report.get("birth", report)
    print(result["module"], result["key"])


if __name__ == "__main__":
    main()
