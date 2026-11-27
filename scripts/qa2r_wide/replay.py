"""Replay the wide-tube certificates of the QA2R label-0.474 forward trace from the repository.

    python3 scripts/qa2r_wide/replay.py [--jobs 20]

1. unpack `generated/qa2r_wide/WideTube.tar.zst` if the sources are not there, and check every
   source against `MANIFEST.sha256`;
2. `lake build WideTube.DommaschkWideTubeRows000Joined` (library `QA2RWide`; about 170 CPU-hours
   from scratch, about 2.5 GB per Lean process);
3. `lake env lean scripts/check_axioms_qa2r_wide.lean`;
4. write `generated/qa2r_wide/replay-report.json`.

Reads nothing under `/tmp` and no campaign cache. Needs the `zstd` command.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "generated/qa2r_wide"
TOP = "WideTube.DommaschkWideTubeRows000Joined"


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 4) - 4))
    args = parser.parse_args()
    started = time.time()
    if not any((OUT / "WideTube").glob("*.lean")):
        subprocess.run("zstd -d --long=27 -q -c WideTube.tar.zst | tar xf -", shell=True, cwd=OUT, check=True)
    listed = dict(reversed(l.split("  ", 1)) for l in (OUT / "MANIFEST.sha256").read_text().splitlines())
    present = {str(p.relative_to(OUT)) for p in (OUT / "WideTube").glob("*.lean")}
    if present != set(listed):
        sys.exit(f"manifest mismatch: {len(present - set(listed))} extra, {len(set(listed) - present)} missing")
    for rel, digest in listed.items():
        if hashlib.sha256((OUT / rel).read_bytes()).hexdigest() != digest:
            sys.exit(f"hash mismatch: {rel}")
    env = {**os.environ, "LEAN_NUM_THREADS": str(args.jobs)}
    t0 = time.time()
    with (OUT / "replay.log").open("w") as log:
        if subprocess.run(["lake", "build", TOP], cwd=ROOT, env=env, stdout=log,
                          stderr=subprocess.STDOUT).returncode:
            sys.exit("lake build failed; see generated/qa2r_wide/replay.log")
    build_seconds = round(time.time() - t0)
    audit = subprocess.run(["lake", "env", "lean", "scripts/check_axioms_qa2r_wide.lean"], cwd=ROOT,
                           capture_output=True, text=True)
    text = " ".join((audit.stdout + audit.stderr).split())
    standard = text.count("depends on axioms: [propext, Classical.choice, Quot.sound]")
    if audit.returncode or "wide-tube axiom audit passed" not in text or standard != 3:
        sys.exit("axiom audit failed:\n" + audit.stdout[-2000:] + audit.stderr[-2000:])
    git = lambda *a: subprocess.check_output(["git", *a], cwd=ROOT, text=True).strip()
    summary = text[text.index("QA2R wide-tube axiom audit passed"):].split(" 'PlasmaLean")[0]
    report = dict(
        audit=summary, modules=len(listed), build_seconds=build_seconds, jobs=args.jobs,
        commit=git("rev-parse", "HEAD"),
        dirty=bool(git("status", "--porcelain", "--", ".", ":!generated/qa2r_wide/replay-report.json")),
        lean=subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip(),
        manifest_sha256=hashlib.sha256((OUT / "MANIFEST.sha256").read_bytes()).hexdigest(),
        date=time.strftime("%Y-%m-%d"), wall_seconds=round(time.time() - started))
    (OUT / "replay-report.json").write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
