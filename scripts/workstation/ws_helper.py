#!/usr/bin/env python3
"""Helpers for scripts/workstation/run.sh (standard library only).

Subcommands:
  measure OUT.json LOG -- CMD...   run CMD, tee output to LOG, record wall time, CPU time and
                                   the peak RSS of the largest process (lean, python, ...)
  axioms LOG                       check `#print axioms` output: only propext, Classical.choice
                                   and Quot.sound are allowed
  summary TASKDIR                  combine the step records of one task into summary.json and
                                   print the laptop-budget verdict
  show                             print a summary.json read from stdin (used by pending.sh)
"""

import glob
import json
import os
import re
import resource
import subprocess
import sys
import time

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LOG_TAIL = 500  # lines kept in committed logs


def measure(out_path, log_path, cmd):
    t0 = time.time()
    with open(log_path, "w") as log:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        lines = []
        for line in proc.stdout:
            sys.stdout.write(line)
            lines.append(line)
            if len(lines) > 4 * LOG_TAIL:
                lines = lines[-LOG_TAIL:]
        proc.wait()
        log.writelines(lines[-LOG_TAIL:])
    wall = time.time() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    # ru_maxrss is the peak of the largest descendant: bytes on macOS, KiB on Linux.
    rss = ru.ru_maxrss if sys.platform == "darwin" else ru.ru_maxrss * 1024
    rec = {
        "cmd": " ".join(cmd),
        "status": "ok" if proc.returncode == 0 else "failed",
        "returncode": proc.returncode,
        "wall_min": round(wall / 60, 2),
        "cpu_min": round((ru.ru_utime + ru.ru_stime) / 60, 2),
        "peak_rss_gb": round(rss / 2**30, 2),
    }
    with open(out_path, "w") as f:
        json.dump(rec, f, indent=1)
    return proc.returncode


def axioms(log_path):
    text = open(log_path).read()
    if re.search(r"\berror:", text):
        print("axiom check: Lean reported an error")
        return 1
    bad = set()
    found = 0
    for m in re.finditer(r"depends on axioms: \[([^\]]*)\]", text, re.S):
        found += 1
        for ax in m.group(1).replace("\n", " ").split(","):
            ax = ax.strip()
            if ax and ax not in ALLOWED:
                bad.add(ax)
    found += len(re.findall(r"does not depend on any axioms", text))
    if bad:
        print("axiom check FAILED, non-standard axioms:", ", ".join(sorted(bad)))
        return 1
    print(f"axiom check ok ({found} entry points)")
    return 0


def summary(task_dir):
    env = os.environ
    max_rss = float(env.get("LAPTOP_MAX_RSS_GB", "6"))
    default_cpu = float(env.get("LAPTOP_DEFAULT_CPU_MIN", "60"))
    max_cpu = float(env.get("LAPTOP_MAX_CPU_MIN", "240"))
    slowdown = float(env.get("LAPTOP_SLOWDOWN", "1.0"))
    meta = json.load(open(os.path.join(task_dir, "meta.json")))
    steps = {}
    for p in sorted(glob.glob(os.path.join(task_dir, "*.step.json"))):
        steps[os.path.basename(p)[: -len(".step.json")]] = json.load(open(p))
    builds = {k[len("build-"):]: v for k, v in steps.items() if k.startswith("build-")}
    lean_cpu = sum(v["cpu_min"] for v in builds.values()) * slowdown
    lean_rss = max([v["peak_rss_gb"] for v in builds.values()], default=0.0)
    failed = [k for k, v in steps.items() if v["status"] != "ok"]
    if failed:
        verdict = "failed: " + ", ".join(failed)
    elif not builds:
        verdict = "no Lean modules"
    elif lean_rss > max_rss:
        verdict = (f"TOO BIG FOR LAPTOP: peak {lean_rss} GB > {max_rss} GB; "
                   "split the certificate into smaller modules")
    elif lean_cpu <= default_cpu:
        verdict = f"laptop ok, default build (~{lean_cpu:.0f} CPU-min)"
    elif lean_cpu <= max_cpu:
        verdict = (f"laptop ok, separate top module not imported by LeanTheory.lean "
                   f"(~{lean_cpu:.0f} CPU-min)")
    else:
        verdict = (f"TOO SLOW FOR LAPTOP: ~{lean_cpu:.0f} CPU-min > {max_cpu}; "
                   "find a smaller certificate")
    out = dict(meta, steps=steps, laptop={
        "lean_cpu_min_scaled": round(lean_cpu, 1), "lean_peak_rss_gb": lean_rss,
        "budget": {"max_rss_gb": max_rss, "default_cpu_min": default_cpu,
                   "max_cpu_min": max_cpu, "slowdown": slowdown},
        "verdict": verdict})
    with open(os.path.join(task_dir, "summary.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(f"{meta['task']}: {verdict}")
    return 0 if not failed and not verdict.startswith("TOO") else 1


def show():
    d = json.load(sys.stdin)
    lap = d["laptop"]
    print(f"   {d['task']} [{d['stamp']}, base {d['base_commit']}, {d['host']}]")
    print(f"     verdict: {lap['verdict']}")
    print(f"     lean: {lap['lean_cpu_min_scaled']} CPU-min (scaled), "
          f"peak {lap['lean_peak_rss_gb']} GB")
    for k, v in d["steps"].items():
        print(f"     {k:40s} {v['status']:6s} {v['wall_min']:8.1f} min "
              f"{v['peak_rss_gb']:6.2f} GB")
    return 0


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    sub = sys.argv[1]
    if sub == "measure":
        if len(sys.argv) < 6 or sys.argv[4] != "--":
            sys.exit("usage: measure OUT.json LOG -- CMD...")
        sys.exit(measure(sys.argv[2], sys.argv[3], sys.argv[5:]))
    if sub == "axioms":
        sys.exit(axioms(sys.argv[2]))
    if sub == "summary":
        sys.exit(summary(sys.argv[2]))
    if sub == "show":
        sys.exit(show())
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
