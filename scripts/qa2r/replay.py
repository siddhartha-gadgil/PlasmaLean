"""Replay the script-generated QA2R certificates from the repository.

    python3 scripts/qa2r/replay.py            # verify hashes, build, axiom audit
    python3 scripts/qa2r/replay.py --target PeriodicCollarFamilyCache.DommaschkPeriodicOriginalCollar

Steps:
0. unpack `generated/qa2r/archives/` if the sources are not there (`scripts/qa2r/pack.py`);
1. check every source under `generated/qa2r/` against `MANIFEST.sha256` (no missing, changed or
   extra file);
2. build the library `QA2RGenerated` with `lake build`, in tiers of recorded peak memory so that
   the parallel jobs fit in `--memory-gb` (a module's tier is the largest recorded peak among the
   module and everything it imports);
3. run `scripts/check_axioms_qa2r.lean` once for each module of `roots.txt` and check that the
   runs cover every source (full replay only);
4. write `generated/qa2r/replay-report.json` (commit, toolchain, counts, times).

No file under `/tmp` and no campaign cache under `.lake/` is read.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "generated/qa2r"
IMPORT = re.compile(r"^(?:public )?(?:meta )?import (?:all )?([A-Za-z0-9_]+)\.([A-Za-z0-9_.]+)\s*$")
TIERS = [4, 8, 16, 40]  # GB of recorded peak memory


def imports(path):
    found, comment = [], False
    with open(path) as f:
        for line in f:
            t = line.strip()
            if comment:
                comment = "-/" not in t
                continue
            if t.startswith("/-"):
                comment = "-/" not in t
                continue
            m = IMPORT.match(t)
            if m:
                found.append(f"{m[1]}.{m[2]}")
            elif t and t != "module" and not t.startswith("--"):
                if t.startswith(("import ", "public import ", "meta import ", "public meta import ")):
                    raise ValueError(f"unparsed import in {path}: {t}")
                break
    return found


def check_manifest():
    listed = {}
    for line in (OUT / "MANIFEST.sha256").read_text().splitlines():
        digest, rel = line.split("  ", 1)
        listed[rel] = digest
    present = {str(p.relative_to(OUT)) for p in OUT.glob("*/*.lean")}
    if present != set(listed):
        sys.exit(f"manifest mismatch: {len(present - set(listed))} extra, "
                 f"{len(set(listed) - present)} missing sources")
    for rel, digest in listed.items():
        if hashlib.sha256((OUT / rel).read_bytes()).hexdigest() != digest:
            sys.exit(f"hash mismatch: {rel}")
    return listed


def available_gb():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable"):
            return int(line.split()[1]) / 1e6
    return 0.0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--target", action="append", default=[], help="build only these modules (no audit)")
    parser.add_argument("--memory-gb", type=float, default=90, help="memory for parallel Lean jobs")
    parser.add_argument("--max-jobs", type=int, default=max(1, (os.cpu_count() or 4) - 4))
    parser.add_argument("--skip-hashes", action="store_true")
    args = parser.parse_args()
    started = time.time()
    if not any(OUT.glob("*/*.lean")):
        subprocess.run([sys.executable, str(Path(__file__).with_name("pack.py")), "unpack"], check=True)
    listed = check_manifest() if not args.skip_hashes else {
        l.split("  ", 1)[1]: 0 for l in (OUT / "MANIFEST.sha256").read_text().splitlines()}
    modules = {rel[:-5].replace("/", "."): rel for rel in listed}
    receipts = json.loads((OUT / "receipts.json").read_text())
    deps = {m: [d for d in imports(OUT / rel) if d in modules] for m, rel in modules.items()}
    wanted = set()
    stack = list(args.target) if args.target else list(modules)
    while stack:
        m = stack.pop()
        if m not in modules:
            sys.exit(f"unknown generated module {m}")
        if m not in wanted:
            wanted.add(m)
            stack.extend(deps[m])
    peak = {}

    def tier_peak(m):  # iterative post-order
        order, stack = [], [m]
        while stack:
            x = stack.pop()
            if x in peak:
                continue
            pending = [d for d in deps[x] if d not in peak]
            if pending:
                stack.append(x)
                stack.extend(pending)
            else:
                own = (receipts.get(modules[x], {}).get("peak_rss_kib") or 4_000_000) / 1e6
                peak[x] = max([own, *[peak[d] for d in deps[x]]])
        return peak[m]

    for m in wanted:
        tier_peak(m)
    phases, done = [], set()
    for limit in TIERS:
        level = {m for m in wanted if peak[m] <= limit}
        imported = {d for m in level for d in deps[m]}
        sinks = sorted(level - imported - done)
        done |= level
        jobs = max(1, min(args.max_jobs, int(args.memory_gb // limit)))
        if sinks:
            phases.append({"limit_gb": limit, "jobs": jobs, "modules": len(level), "sinks": sinks})
    if done != wanted:
        sys.exit(f"{len(wanted - done)} modules exceed the largest memory tier")
    log = OUT / "replay.log"
    log.write_text("")
    for phase in phases:
        sinks = phase.pop("sinks")
        phase["targets"] = len(sinks)
        t0 = time.time()
        print(f"tier <= {phase['limit_gb']} GB: {phase['modules']} modules, {len(sinks)} targets, "
              f"{phase['jobs']} jobs", flush=True)
        for i in range(0, len(sinks), 1500):
            while available_gb() < phase["limit_gb"] * phase["jobs"] * 0.6:
                print(f"waiting for memory ({available_gb():.0f} GB available)", flush=True)
                time.sleep(60)
            env = {**os.environ, "LEAN_NUM_THREADS": str(phase["jobs"])}
            with log.open("a") as out:
                code = subprocess.run(["lake", "build", *sinks[i:i + 1500]], cwd=ROOT, env=env,
                                      stdout=out, stderr=subprocess.STDOUT).returncode
            if code:
                sys.exit(f"lake build failed in tier {phase['limit_gb']} GB; see {log}")
        phase["wall_seconds"] = round(time.time() - t0)
    report = {"phases": phases, "modules": len(wanted)}
    if not args.target:
        t0 = time.time()
        template = (ROOT / "scripts/check_axioms_qa2r.lean").read_text().splitlines(keepends=True)
        marked = [i for i, line in enumerate(template) if line.rstrip().endswith("-- ROOT")]
        if len(marked) != 1:
            sys.exit("scripts/check_axioms_qa2r.lean: expected one import marked ROOT")
        work = ROOT / ".lake/qa2r-audit"
        work.mkdir(exist_ok=True)
        roots = (OUT / "roots.txt").read_text().split()

        def audit_one(root):
            lines = list(template)
            lines[marked[0]] = f"import {root} -- ROOT\n"
            script = work / (root + ".lean")
            script.write_text("".join(lines))
            run = subprocess.run(["lake", "env", "lean", str(script)], cwd=ROOT, capture_output=True, text=True)
            return root, run.returncode, run.stdout + run.stderr

        counts, failures = {}, []
        with ThreadPoolExecutor(max(1, min(args.max_jobs, 12))) as pool, (OUT / "audit.log").open("w") as out:
            for root, code, text in pool.map(audit_one, roots):
                summary = [l for l in text.splitlines() if l.startswith("QA2R axiom audit passed")]
                other = [l for l in text.splitlines() if not l.startswith(("module ", "QA2R axiom audit passed"))]
                out.write(f"{root}: {summary[0] if summary else 'FAILED'}\n" + "".join(l + "\n" for l in other))
                if code or len(summary) != 1 or other:
                    failures.append(root)
                    continue
                for line in text.splitlines():
                    if line.startswith("module "):
                        _, name, n = line.split()
                        # A module imported indirectly shows only its exported declarations,
                        # whose recorded axiom sets include those of the private ones they use.
                        counts[name] = max(counts.get(name, 0), int(n))
        if failures:
            sys.exit(f"axiom audit failed for {len(failures)} items, e.g. {failures[0]}; see generated/qa2r/audit.log")
        if set(counts) != set(modules):
            sys.exit(f"audit coverage: {len(set(modules) - set(counts))} sources not imported by any root")
        theorems = sum(1 for r in receipts.values() for t in r["theorems"] if t.startswith("PlasmaLean."))
        audit_summary = (f"QA2R axiom audit passed: {sum(counts.values())} declarations in {len(counts)} "
                         f"generated modules, standard axioms only; {len(roots)} audit runs; "
                         f"{theorems} receipt theorems present")
        git = lambda *a: subprocess.check_output(["git", *a], cwd=ROOT, text=True).strip()
        report.update(
            audit=audit_summary, audit_seconds=round(time.time() - t0),
            commit=git("rev-parse", "HEAD"), dirty=bool(git("status", "--porcelain")),
            lean=subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip(),
            manifest_sha256=hashlib.sha256((OUT / "MANIFEST.sha256").read_bytes()).hexdigest(),
            host_cpus=os.cpu_count(), date=time.strftime("%Y-%m-%d"),
            wall_seconds=round(time.time() - started))
        (OUT / "replay-report.json").write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps(report, indent=1), flush=True)


if __name__ == "__main__":
    main()
