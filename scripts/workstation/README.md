# scripts/workstation/

The workstation pipeline (full documentation: [Workstation.md](../../Workstation.md)).

| File | Purpose |
| --- | --- |
| [`run.sh`](run.sh) | Runs tasks: numerics → Lean emission → per-module measured build → axiom check → results branch `workstation/<task>-<stamp>` pushed. `--verify-only` re-checks a task on the laptop with the laptop budget; `--help` lists the options |
| [`ws_helper.py`](ws_helper.py) | Measurement (wall/CPU time, peak RSS), axiom-log check, `summary.json` and laptop verdict |
| [`pending.sh`](pending.sh) | Lists unmerged `workstation/*` branches not yet in `workstation/REVIEWED.md`, with verdicts |
| [`oleans.py`](oleans.py) | Packs/unpacks compiled modules (oleans) between machines, with version and source checks |
| [`tasks/TEMPLATE.sh`](tasks/TEMPLATE.sh) | Template for a new task (modules, entry points, outputs, `task_numerics`, `task_emit`) |
| [`tasks/smoke.sh`](tasks/smoke.sh) | Pipeline smoke test: Python packages, one small module, axioms, push |

Laptop budget defaults: ≤ 6 GB peak per process, ≤ 60 Lean CPU-minutes for a default-build task,
≤ 240 for an on-demand top module (`LAPTOP_MAX_RSS_GB`, `LAPTOP_DEFAULT_CPU_MIN`,
`LAPTOP_MAX_CPU_MIN`, `LAPTOP_SLOWDOWN`).
