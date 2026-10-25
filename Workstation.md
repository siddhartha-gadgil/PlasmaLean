# Running heavy work on a workstation

Some PlasmaLean steps need more memory or CPU than the development laptop has: untrusted numerical
searches (KAM tori, Chebyshev families, ballooning oracles) and the first Lean build of large
certificates. These run on a workstation through one script,
[`scripts/workstation/run.sh`](scripts/workstation/run.sh), which pushes its results to a git
branch. The laptop then pulls the branch and re-checks it.

**Rule: the final Lean must build on the laptop.** The workstation looks for certificates and
makes them *small*. It is not a place for proofs that only a large machine can check. Every run
measures each Lean module and reports a laptop verdict:

| Verdict | Condition (defaults) | What happens |
| --- | --- | --- |
| laptop ok, default build | peak ≤ 6 GB per process and Lean CPU ≤ 60 min | imported by `PlasmaLean.lean` |
| laptop ok, separate top module | peak ≤ 6 GB and Lean CPU ≤ 240 min | on-demand `lake build PlasmaLean.Design.<Top>` |
| TOO BIG / TOO SLOW FOR LAPTOP | otherwise | not merged; split the certificate or find a smaller one |

The limits come from `LAPTOP_MAX_RSS_GB`, `LAPTOP_DEFAULT_CPU_MIN`, `LAPTOP_MAX_CPU_MIN` and
`LAPTOP_SLOWDOWN`. The last one multiplies the workstation CPU time: set it, for example, to 1.5
if the workstation cores are faster than the laptop's.

## Requirements on the workstation

- Linux or macOS, with `bash`, `git` and `python3` ≥ 3.10 (with `venv`/`pip`).
  On Debian/Ubuntu: `sudo apt install git python3-venv build-essential`.
- Push access to the GitHub repository, via an ssh key (`ssh -T git@github.com`) or a credential helper.
- Lean set up once by hand in the clone: `elan` (Lean v4.34.1 from `lean-toolchain`),
  `lake exe cache get` and `lake build`. This is already done on the workstation. The script only
  checks that `lake` is available. Later builds are incremental: each task builds only what changed.
- The script installs the Python packages itself, into a venv `.venv-ws`, from
  [`scripts/requirements.txt`](scripts/requirements.txt).

## First time

```bash
ssh workstation
tmux new -s plasma            # so that a dropped connection does not stop the run
cd PlasmaLean && git pull
scripts/workstation/run.sh --setup-only    # Python venv and packages
scripts/workstation/run.sh smoke           # a few minutes: tests the whole pipeline and pushes
```

Detach with `Ctrl-b d` and reattach later with `tmux attach -t plasma`.

## A run

```bash
cd PlasmaLean && git checkout main && git pull
scripts/workstation/run.sh --list                 # available tasks
scripts/workstation/run.sh energy-window          # one or more tasks
```

For each task, the script:

1. creates a branch `workstation/<tasks>-<UTC stamp>` from the current `main`. It refuses to run
   if tracked files are modified;
2. runs the task's **numerics** (untrusted Python), with intermediate data kept in `$WS_WORK`
   (default `~/plasmalean-work`, never committed);
3. **emits** the Lean certificate files;
4. **builds** each Lean module of the task separately and records its wall time, CPU time and peak
   memory;
5. **checks axioms** of the task's main theorems: only `propext`, `Classical.choice` and `Quot.sound`
   are allowed;
6. writes `workstation/results/<task>/<stamp>/` with the step records, truncated logs and
   `summary.json`, which contains the laptop verdict;
7. commits the results and, if every step succeeded, the generated files. It then pushes the
   branch. A failed task still commits its logs, so that the failure can be diagnosed on the laptop.

The script exits nonzero if any task failed or does not fit the laptop.

Options:
- `--skip-numerics`: re-emit and rebuild only.
- `--no-push`: commit without pushing.
- `--branch NAME`: use a different branch name.
- `--jobs N`: set the parallelism (default: all CPUs).

`--help` lists them all.

## Back on the laptop

In a Claude Code session here, say **"update from workstation"**: the skill
`plasmalean-workstation-update` lists pending runs (`scripts/workstation/pending.sh`), re-checks the
passing ones with `--verify-only`, merges and integrates them, records every run in
`workstation/REVIEWED.md`, pushes and reports. The manual steps are:

```bash
scripts/workstation/pending.sh                              # unmerged runs and their verdicts
git log --oneline origin/workstation/<branch> -3
cat workstation/results/<task>/<stamp>/summary.json        # after checking out the branch
git checkout -b review origin/workstation/<branch>
scripts/workstation/run.sh --verify-only <task>             # builds here, with the laptop budget
```

`--verify-only` skips the installs, numerics and emission, and touches no git state. It builds the
task's modules on the laptop one at a time with the same measurements, re-checks the axioms and
prints the verdict. Its records go to `$TMPDIR/plasmalean-verify`. If the verdict is "laptop ok",
merge the branch into `main`:
- for a default-build result, add the imports to `PlasmaLean.lean` and the entry points to
  `scripts/check_axioms.lean`;
- for a separate top module, document its build command.

Then update the plan and progress reports as usual.

## Adding a task

Copy [`scripts/workstation/tasks/TEMPLATE.sh`](scripts/workstation/tasks/TEMPLATE.sh) to
`tasks/<name>.sh` and fill in the fields:
- `TASK_MODULES`: dependencies first;
- `TASK_ENTRYPOINTS`;
- `TASK_OUTPUTS`: the files to commit;
- `TASK_TARGET`;
- the functions `task_numerics` and `task_emit`.

The functions run from the repository root with `WS_PY` (the venv Python), `WS_WORK` and `WS_JOBS`
set. Keep the numerics restartable, because long runs get interrupted. Test the task file on the
laptop with a small parameter setting, then commit it to `main` before running it on the workstation.

## Troubleshooting

- **Lost connection:** always run inside `tmux` or `screen`.
- **Mathlib or Lean version bumped on `main`:** run `lake exe cache get` (and `elan` picks up a
  new `lean-toolchain` automatically) before the next run, or Mathlib will rebuild from source.
- **Out of memory on the workstation:** lower `--jobs`. A task's numerics should respect `WS_JOBS`.
- **Push rejected:** the branch name is unique per run, so this is an authentication problem.
  Check `git remote -v` and your ssh key.
- **Generated Lean too big for the laptop:** the verdict says so and nothing should be merged.
  Split the certificate over several modules (each ≤ 6 GB), use proof-term certificates (see
  `.claude/skills/plasmalean-lean-proofs`), or ask the numerics for a smaller witness.
