# scripts/workstation/

The workstation pipeline (full documentation: [Workstation.md](../../Workstation.md); laptop side:
skill `plasmalean-workstation-update`).

| File | Purpose |
| --- | --- |
| [`run.sh`](run.sh) | Runs tasks: numerics → Lean emission → per-module measured build → axiom check → results branch `workstation/<task>-<stamp>` pushed. `--verify-only` re-checks a task on the laptop with the laptop budget; `--list`, `--skip-numerics`, `--no-push`; see the header |
| [`ws_helper.py`](ws_helper.py) | Measurement (wall/CPU time, peak RSS), axiom-log check, `summary.json` and laptop verdict |
| [`pending.sh`](pending.sh) | Lists unmerged `workstation/*` branches not yet in `workstation/REVIEWED.md`, with verdicts |
| [`oleans.py`](oleans.py) | Packs/unpacks compiled modules (oleans) between machines, with version and source checks |
| [`tasks/TEMPLATE.sh`](tasks/TEMPLATE.sh) | Template for a new task (modules, entry points, outputs, `task_numerics`, `task_emit`) |
| [`tasks/smoke.sh`](tasks/smoke.sh) | Pipeline smoke test: Python packages, one small module (`PlasmaLean.SubsetSum`), axioms, push |
| [`tasks/lambda-cell.sh`](tasks/lambda-cell.sh) | One pitch-angle cell of passing alpha guiding centres (`Design/RationalStellaratorGCMu<TAG>*`) |
| [`tasks/energy-window.sh`](tasks/energy-window.sh) | Energy × pitch family of KAM tori (`Design/RationalStellaratorGCEw*`) |
| [`tasks/family2-ballooning.sh`](tasks/family2-ballooning.sh) | Family-2 ballooning certificate search (data only; no kernel checker yet) |
| [`tasks/proofterm-migrate.sh`](tasks/proofterm-migrate.sh) | Phase 16 migration of on-demand KAM families to explicit proof terms |

Laptop budget defaults: ≤ 6 GB peak per process, ≤ 60 Lean CPU-minutes for a default-build task,
≤ 240 for an on-demand top module (`LAPTOP_MAX_RSS_GB`, `LAPTOP_DEFAULT_CPU_MIN`,
`LAPTOP_MAX_CPU_MIN`, `LAPTOP_SLOWDOWN`). After a phase that adds or changes heavy numerics or
certificates, update the tasks here.
