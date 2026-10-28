# workstation/

Records of the workstation pipeline (see [Workstation.md](../Workstation.md)).

- [`REVIEWED.md`](REVIEWED.md): one line per workstation run reviewed on the laptop (skill
  `workstation-update`); `scripts/workstation/pending.sh` skips the branches listed here.
- `results/<task>/<stamp>/` (created by `scripts/workstation/run.sh` on the results branch, not on
  `main`): step records, truncated logs and `summary.json` with the laptop verdict.
- `artifacts/<task>/` (optional, created by tasks that set `TASK_ARTIFACTS`): small files
  (≤ 50 MB each) reused by later runs.
