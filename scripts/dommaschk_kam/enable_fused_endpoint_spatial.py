"""Opt in one endpoint only after both original signed physical steps pass its own pilot."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from verify_endpoint_signed_prefix import DEPENDENCY, PACKAGE, input_root
from verify_fused_endpoint_jacobians import MARKER, checked_roots
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, key_of, save


def check(evidence, label, packet, version):
    index = evidence["index"]
    if (evidence["endpoint"], evidence["packet_sha256"]) != (label,packet):
        raise ValueError("the pilot belongs to a different endpoint or trajectory packet")
    matrices = {r.get("matrix_direction"): r for r in evidence["jacobians"]}
    opposite = label.startswith("q1")
    if (set(matrices) != ({1,-1} if opposite else {None}) or
            len(matrices) != len(evidence["jacobians"])):
        raise ValueError("the endpoint needs its own signed frames")
    steps = evidence["steps"]
    if len(steps) != 2 or {s["direction"] for s in steps} != {1,-1}:
        raise ValueError("the pilot requires both physical clocks")
    for s in steps:
        sign = s["direction"]
        clock = "Forward" if sign == 1 else "Back"
        frame = "Independent"+clock if opposite else "PairedForward"
        jac = matrices[sign if opposite else None]
        jacname = f"DommaschkJacobian{label.upper()}{frame}{index:03}"
        jacroot = input_root(jac,label,1,index,jacname,packet,version)
        checked_roots(jac,jacroot,version)
        name = f"DommaschkPhysical{label.upper()}{clock}{index:03}"
        if (s["endpoint"],s["packet_sha256"],s["index"],s["module"],s["jacobian_key"]) != (
                label,packet,index,name,jac["key"]):
            raise ValueError("the physical pilot uses a different endpoint, clock or matrix")
        root = Path(s["import_paths"][0])
        record = admitted(root,name,s["key"])
        claims = ["checked","field_bounds","physical_step"]
        if record["theorems"] != ["PlasmaLean.Design."+name+"."+t for t in claims]:
            raise ValueError("the local physical step is missing")
        source = (root/PACKAGE/(name+".lean")).read_text()
        common = [packet,version,digest(DESIGN/(DEPENDENCY+".trace")),jac["key"],s["residual_key"]]
        if key_of([common,[(name,source,claims)]]) != s["key"]:
            raise ValueError("the signed physical result has a different packet or parents")


def enabled(campaign, label, packet, version):
    path = campaign/MARKER
    if not path.is_file():
        return False
    check(json.loads(path.read_text()),label,packet,version)
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign", type=Path, required=True)
    parser.add_argument("--span", nargs=2, type=int, required=True)
    parser.add_argument("--row", type=int, required=True)
    args = parser.parse_args()
    directory = args.campaign.resolve()
    status = json.loads((directory/"status.json").read_text())
    label, index = status["endpoint"], args.row
    packet = RECORD.with_name(f"bounce_frame_{label[:2]}_u{label[3:]}.json.gz")
    checksum = digest(packet)
    if status["packet_sha256"] != checksum or not (args.span[0] <= index < args.span[1]):
        parser.error("the original packet or pilot span differs from the active campaign")
    references = directory/"references"/f"{index:03}.json"
    if not references.is_file():
        parser.error("the selected original signed central defects are not yet available")
    version = subprocess.check_output(["lake","env","lean","--version"], cwd=ROOT, text=True).strip()
    if enabled(directory,label,checksum,version):
        print(f"{label} already enabled with both physical proofs",flush=True)
        return
    pilot = directory/"fused-pilot"
    pilot.mkdir(exist_ok=True)
    jac, steps = (pilot/(name+f"{index:03}.json") for name in ("matrices","physical"))
    def run(script, *rest):
        subprocess.run([sys.executable,Path(__file__).with_name(script),"--endpoint",label,*map(str,rest)],
                       cwd=ROOT, check=True)
    run("verify_grouped_endpoint_jacobians.py","--span",*args.span,"--rows",index,"--fused","--output",jac)
    run("verify_endpoint_signed_prefix.py","--row",index,"--references",references,
        "--jacobians",jac,"--output",steps)
    evidence = {"endpoint": label, "packet_sha256": checksum, "index": index,
                "jacobians": json.loads(jac.read_text()), "steps": json.loads(steps.read_text())}
    check(evidence,label,checksum,version)
    save(directory/MARKER,evidence)
    print(f"{label} enabled using both original signed physical steps at {index}",flush=True)


if __name__ == "__main__":
    main()
