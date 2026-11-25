"""Collect a reproducible eight-launch checkpoint from the signed prefix campaign.

Each child verifier reauthenticates its inputs and checks its composed Lean proof.
The manifest retains the selected prefix lengths so a growing campaign can replay
an earlier checkpoint with --lengths.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from verify_common_endpoint_traces import ENDPOINTS
from verify_physical_trace_slabs import ROOT, save


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign", type=Path, default=ROOT / ".lake/secondary-trace-campaign")
    parser.add_argument("--pilot", required=True, type=Path)
    parser.add_argument("--flight", required=True, type=Path)
    parser.add_argument("--clearances", required=True, nargs=3, type=Path)
    parser.add_argument("--launch-profile", required=True, type=Path)
    parser.add_argument("--row-map", required=True, type=Path)
    parser.add_argument("--lengths", nargs=7, type=int, metavar="N",
                        help="seven secondary lengths in the order " + ", ".join(ENDPOINTS[1:]))
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    scripts = Path(__file__).resolve().parent

    def verify(name, module, *flags):
        receipt = args.output_dir / (name + ".json")
        print(f"{name} → {receipt}", flush=True)
        subprocess.run([sys.executable, scripts / (module + ".py"), *flags, "--output", receipt], check=True)
        return receipt

    selected = []
    for i, label in enumerate(ENDPOINTS[1:]):
        directory = args.campaign / label / "prefixes"
        if args.lengths is None:
            candidates = [p for p in directory.glob("*.json") if p.stem.isdecimal()]
            if not candidates:
                parser.error(f"no signed prefix for {label} in {directory}")
            selected.append(max(candidates, key=lambda p: int(p.stem)))
        else:
            prefix = directory / f"{args.lengths[i]:03}.json"
            if not prefix.is_file():
                parser.error(f"missing selected prefix {prefix}")
            selected.append(prefix)
    lengths = [int(p.stem) for p in selected]
    family = verify("family", "verify_common_endpoint_traces", "--pilot", args.pilot,
                    "--secondary", *selected)
    birth = verify("birth", "verify_birth_variation", "--family", family)
    calibrated = verify("calibrated", "verify_common_pilot_observables", "--birth", birth,
                        "--flight", args.flight)
    outputs = {"family": family, "birth": birth, "calibrated": calibrated}
    outputs["clearances"] = verify("clearances", "verify_common_original_margins",
                                   "--calibrated", calibrated, "--clearances", *args.clearances)
    outputs["opposite"] = verify("opposite", "verify_opposite_incoming_fields", "--calibrated", calibrated)
    outputs["compared"] = verify("compared", "verify_compared_trace_prefix", "--calibrated", calibrated,
                                 "--launch-profile", args.launch_profile, "--row-map", args.row_map,
                                 "--length", "325")
    family_info = json.loads(family.read_text())
    save(args.output_dir / "manifest.json", {
        "lengths_each_direction": family_info["lengths_each_direction"],
        "selected_secondary_lengths": lengths,
        "signed_rows": family_info["signed_rows"],
        "receipts": {key: value.name for key, value in outputs.items()},
        "family_key": family_info["key"],
    })


if __name__ == "__main__":
    main()
