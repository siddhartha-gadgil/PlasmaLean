"""Compare kernel time on identical signed trial rectangles, rates, inputs and claims."""
import argparse
from collections import defaultdict
import json
from pathlib import Path

from grouped_trial_jacobian_rows import checked_grouped_roots
from verify_endpoint_signed_prefix import input_root
from verify_fused_endpoint_jacobians import checked_roots
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import RECORD, digest, save


def summarize(path, fused):
    original = json.loads(path.read_text())
    if not original:
        raise ValueError(f"empty signed matrix report {path}")
    inputs = {}
    times = defaultdict(float)
    seen = set()
    for item in original:
        label, index = item["endpoint"], item["index"]
        clock = (index, item.get("matrix_direction"))
        if clock in inputs:
            raise ValueError(f"repeated matrix {clock}")
        packet = RECORD.with_name(f"bounce_frame_{label[:2]}_u{label[3:]}.json.gz")
        checksum = digest(packet)
        module, version = item["module"], item["lean_version"]
        root = input_root(item, label, 1, index, module, checksum, version)
        inputs[clock] = (label, checksum, version, module, tuple(item["projected_radii"]),
                         item["common_rate"], item["theorems"], item["axioms"])
        parents = item["fused_parents" if fused else "grouped_parents"]
        check = checked_roots if fused else checked_grouped_roots
        check(item, root, version)
        for parent in [*parents, {"root": str(root), "module": module, "key": item["key"]}]:
            key, name = parent["key"], parent["module"]
            if key in seen:
                continue
            seen.add(key)
            record = admitted(Path(parent["root"]), name, key)
            if name.startswith("DommaschkHornerJetData"):
                stage = "shared_static"
            elif name.endswith("Fields"):
                stage = "field_jet"
            elif name.endswith("Restricted"):
                stage = "restricted_jets"
            elif name.endswith("Input"):
                stage = "clock_inputs"
            elif name.startswith("DommaschkJacobian"):
                stage = "wrappers" if fused else "matrix_groups"
            else:
                stage = "fused_clock_restrictions_matrices"
            times[stage] += record["wall_seconds"]
    seconds = round(sum(v for k,v in times.items() if k != "shared_static"), 3)
    return inputs, {"stages_seconds": {k: round(v,3) for k,v in times.items()},
                    "nonstatic_kernel_seconds": seconds, "accepted_packages": len(seen)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--fused", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    original, old = summarize(args.original, False)
    replacement, new = summarize(args.fused, True)
    if original != replacement:
        raise ValueError("input rectangle, signed budget, clock, packet, or audited claims differ")
    ratio = old["nonstatic_kernel_seconds"] / new["nonstatic_kernel_seconds"]
    label, checksum = next(iter(original.values()))[:2]
    result = {"endpoint": label, "packet_sha256": checksum,
              "rows": sorted({i for i,_ in original}), "signed_matrices": len(original),
              "distinct_claims": sum(len(x[-2]) for x in original.values()),
              "original": old, "fused": new, "nonstatic_speedup": ratio}
    save(args.output, result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
