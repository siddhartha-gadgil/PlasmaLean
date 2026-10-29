# workstation/

Records of the workstation pipeline (see [Workstation.md](../Workstation.md)).

- [`REVIEWED.md`](REVIEWED.md): one line per workstation run reviewed on the laptop (skill
  `plasmalean-workstation-update`), with outcome and cost on both machines;
  `scripts/workstation/pending.sh` skips the branches listed here.
- `results/<task>/<stamp>/`: step records, truncated logs and `summary.json` with the laptop
  verdict, written by `scripts/workstation/run.sh` on the results branch and kept on `main` for
  merged runs (currently `lambda-cell/` and `proofterm-migrate/`).
- `artifacts/<task>/` (optional, created by tasks that set `TASK_ARTIFACTS`): small files reused by
  later runs.
