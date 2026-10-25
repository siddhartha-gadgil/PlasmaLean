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
- Push access to the GitHub repository **without typing a password** (see below). `run.sh` checks
  this before starting and stops at once if a push would prompt.
- Lean set up once by hand in the clone: `elan` (Lean v4.34.1 from `lean-toolchain`),
  `lake exe cache get` and `lake build`. This is already done on the workstation. The script only
  checks that `lake` is available. Later builds are incremental: each task builds only what changed.
- The script installs the Python packages itself, into a venv `.venv-ws`, from
  [`scripts/requirements.txt`](scripts/requirements.txt).

### Push access

GitHub does not accept account passwords for `git push` over HTTPS, and a run pushes unattended,
so set up one of these once:

- **ssh key (recommended):**
  ```bash
  ssh-keygen -t ed25519 -C hornbill            # empty passphrase, or load it with ssh-agent
  cat ~/.ssh/id_ed25519.pub                    # add at github.com → Settings → SSH keys
  ssh -T git@github.com                        # should greet you by user name
  git remote set-url origin git@github.com:siddhartha-gadgil/PlasmaLean.git
  ```
- **GitHub CLI:** `gh auth login` (HTTPS), then `gh auth setup-git`.
- **Stored token:** create a personal access token (repo scope), then
  `git config --global credential.helper store` and push once by hand, entering the token as the
  password. (`credential.helper cache` forgets it after 15 minutes, which is why it kept asking.)

Check with `git push --dry-run origin HEAD:refs/heads/workstation/auth-check`: it must finish
without a prompt.

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

1. switches to `main` and pulls (a previous run leaves the clone on its results branch only if it
   failed), then creates a branch `workstation/<tasks>-<UTC stamp>`. It refuses to run if tracked
   files are modified;
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
   branch and switches back to `main`. A failed task still commits its logs and whatever files it
   generated, so that the failure can be reproduced on the laptop.

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

## Next Commands

Kept up to date from the laptop after every review ("update from workstation"). Run them on the
workstation, inside `tmux`; `run.sh` pulls `main` itself.

**Status (25 October 2026): wait.** The generator bug behind the failed Mu3 runs (a template
number substituted twice, giving a false bound in `Mu3Adm`) is being fixed; these commands become
useful once the fix is on `main` (the next laptop commit will say so here). Push access must work
without a password (see "Push access" above).

```bash
# Pitch cell λ ∈ [1/8, 3/16] (tag Mu3): numerics are cached on the workstation, so this re-emits
# with the fixed generator and builds (about 30 CPU-min of Lean).
LAM_LO=1/8 LAM_HI=3/16 LAM_TAG=3 scripts/workstation/run.sh --skip-numerics lambda-cell

# Pitch cell λ ∈ [3/16, 1/4] (tag Mu4): from scratch, about 40 min of Python plus 30 CPU-min of Lean.
LAM_LO=3/16 LAM_HI=1/4 LAM_TAG=4 scripts/workstation/run.sh lambda-cell
```

The certificates are now emitted in the low-memory format (peak ≈ 4.4 GB per process), so the
default 6 GB laptop limit applies; `LAPTOP_MAX_RSS_GB=9` is no longer needed.

Run the two commands separately (not joined by `&&`): they are independent. Then say "update
from workstation" on the laptop.
