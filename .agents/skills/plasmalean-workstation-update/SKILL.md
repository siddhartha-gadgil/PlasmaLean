---
name: plasmalean-workstation-update
description: Fetch PlasmaLean workstation runs (git branches workstation/*), re-check them on this laptop with the laptop build budget, merge and integrate the ones that pass, and report. Use when the user says "update from workstation", "pull the workstation results", "what did the workstation do", "check workstation runs" or similar.
---

# Update from the workstation

Heavy numerics and first builds of large certificates run on a workstation via
`scripts/workstation/run.sh` (see `Workstation.md`). Tasks are scripts in
`scripts/workstation/tasks/`: `smoke.sh` (a pipeline check), `TEMPLATE.sh` (copy it to define a
new task: numerics, emission of generated Lean files, the list of modules to build) and the
project tasks (`energy-window.sh`, `lambda-cell.sh`, `family2-ballooning.sh`,
`proofterm-migrate.sh`). Each run pushes a branch
`workstation/<tasks>-<UTC stamp>` containing `workstation/results/<task>/<stamp>/` (step records,
truncated logs, `summary.json` with a laptop verdict) and, on success, generated files. This skill
brings those runs back here. The user's request authorizes the whole procedure below, including
the merge into `main` and the push. Do not merge anything that fails a check.

## 1. Survey

```bash
scripts/workstation/pending.sh          # fetches; lists unmerged, unreviewed runs with verdicts
```

If it prints "no pending workstation runs", report that and also show the last few lines of
`workstation/REVIEWED.md`. Do not run anything else. Otherwise, for each pending branch, oldest
first, classify it from its verdicts:

- **failed** (any step not ok): read the logs straight from the branch, for example
  `git show origin/<branch>:workstation/results/<task>/<stamp>/numerics.log | tail -60`. Diagnose:
  environment/setup, a numerics failure, a Lean error or an axiom violation. Do not merge.
  Record it (§4).
- **TOO BIG / TOO SLOW FOR LAPTOP**: do not merge. Record the peak memory and CPU, and suggest
  how to shrink the certificate (split modules, a proof-term certificate, a smaller witness).
- **laptop ok, default build**: re-check it here in full (§2).
- **laptop ok, separate top module** (on-demand modules, not imported by `PlasmaLean.lean`):
  spot-check instead of a full rebuild (§2a). This is the user's decision of 25 October 2026: the
  workstation's Lean kernel check is accepted for on-demand modules, and the full laptop build is
  deferred until the module is needed.
- A **smoke**-only run has nothing to merge. Record it as a pipeline check and report the
  workstation's host, CPUs and timings.

## 2. Re-check on the laptop

Preconditions:
- `git status --porcelain --untracked-files=no` is empty;
- you are on `main` and up to date (`git pull --ff-only`);
- `memory_pressure | tail -1` shows enough free memory;
- no other agent is running a heavy Lean build. If one is, wait for it or tell the user.

Untracked files left by running agents are fine: never `git add -A`.

```bash
git merge --no-ff --no-commit origin/<branch>
scripts/workstation/run.sh --verify-only <task> [<task> ...]
```

`--verify-only` builds each task module separately, measuring each build against the laptop
budget, and re-checks the axioms. It does not touch git. Compare the laptop numbers with the
workstation's. If it fails, or its verdict is not "laptop ok", run `git merge --abort` and record
the run as rejected, with the laptop numbers.

## 2a. Spot-check an on-demand run

Same preconditions as §2. Inside the uncommitted merge:
1. Check the workstation's numbers against the laptop limits in `summary.json`: every module's
   peak ≤ `LAPTOP_MAX_RSS_GB` (6), and the verdict is "laptop ok". Check that the axioms step is ok.
2. Grep the merged files: no `sorry`, `admit`, `axiom`, `native_decide` or `decide` of any kind
   (`decide +kernel`, `decide_cbv`, plain `decide`).
3. Build a sample here, one module at a time, with `lake build <module>`: the first, the last and
   two random check modules of each family, plus each family's bridge (`LowMem*`). This builds
   their dependencies too, which is part of the point. Compare peak memory and time with the
   workstation's numbers.
4. If all of this passes, continue with §3. Record "merged (separate top module, spot-checked)",
   and note that the full laptop build is deferred. Otherwise run `git merge --abort` and record
   the run as rejected.

## 3. Integrate a passing run

Still inside the uncommitted merge:

1. **Default build:** add `public import <module>` for the task's top modules to `PlasmaLean.lean`,
   in the matching section. Add `#print axioms <entry point>` lines to `scripts/check_axioms.lean`.
   **Separate top module:** do neither. Make sure the build command
   (`lake build PlasmaLean.Design.<Top>`) is documented in the module docstring and in the plan.
2. Check the reported declarations: grep each entry point in the merged files. Also check that the
   generated files contain no `sorry`, `axiom`, `native_decide` or `decide` of any kind.
3. `lake build PlasmaLean` (one process; with zero warnings), then
   `lake env lean scripts/check_axioms.lean`.
4. Update `notes/implementation-plan.md` with a dated log entry under the relevant phase (what was
   certified, the window or parameters, the cost on both machines) and update the affected `Q-*`/`N-*`
   rows of its research graph (status, evidence, next action). If the result is substantive,
   also update the progress report, slides and docs via the usual pipeline
   (`node scripts/generate_handbook.mjs`, `node scripts/check_site.mjs`).
5. Record the run in `workstation/REVIEWED.md` (§4).
6. Commit the merge, staging paths explicitly: the merged files, `PlasmaLean.lean`,
   `scripts/check_axioms.lean`, the notes and `workstation/REVIEWED.md`. Use a message such as
   `Merge workstation run <branch>: <task> (<verdict>)`, followed by the attribution trailer.
   Then `git push`.

If any step in §3 fails and you cannot fix it with a small, obviously correct change, run
`git merge --abort` (or `git reset --merge`). Record the run as rejected, with the reason.

## 4. Record and report

Append one line per run to `workstation/REVIEWED.md` (create the file with a short header if it
is missing), in the format

```
- `<branch>` — <task>: <merged (default build) | merged (separate top module) | rejected: reason | failed: diagnosis | smoke ok> — workstation <cpu-min>/<GB>, laptop <cpu-min>/<GB> — <YYYY-MM-DD>
```

For runs that were not merged, commit only `workstation/REVIEWED.md` (staged explicitly) and push.
`pending.sh` then stops listing them.

Final report to the user, concise:
- for each run: the task, its outcome, and the key numbers (certified window or parameters,
  workstation and laptop cost, peak memory);
- what changed on `main` (the commit hash), or why nothing changed;
- suggested next workstation tasks, or fixes for failed runs, as exact `run.sh` commands for the
  user to type on the workstation.

After every review, rewrite the **"Next Commands"** section at the end of `Workstation.md`: a
dated status line (run now / wait, and why) and the exact commands for the next useful runs.
Commit it with the review.

Do not delete remote `workstation/*` branches unless the user asks.
