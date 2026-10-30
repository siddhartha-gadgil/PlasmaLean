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
- `--skip-push-check`: do not test push access before starting.
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

For **on-demand** results (verdict "separate top module", not imported by `PlasmaLean.lean`), the
review spot-checks rather than rebuilding everything: it checks the workstation's measurements and
axiom check, greps for forbidden tactics, and builds a sample of modules here. The full laptop
build of such a family is deferred until it is needed. Default-build results are always rebuilt
here in full.

`--verify-only` skips the installs, numerics and emission, and touches no git state. It builds the
task's modules on the laptop one at a time with the same measurements, re-checks the axioms and
prints the verdict. Its records go to `$TMPDIR/plasmalean-verify`. If the verdict is "laptop ok",
merge the branch into `main`:
- for a default-build result, add the imports to `PlasmaLean.lean` and the entry points to
  `scripts/check_axioms.lean`;
- for a separate top module, document its build command.

Then update the plan and progress reports as usual.

## Sharing compiled files (oleans)

Like the Mathlib cache, but by hand: compiled PlasmaLean modules built on one machine can be copied
to the other instead of being rebuilt. This uses
[`scripts/workstation/oleans.py`](scripts/workstation/oleans.py).

On the workstation, after a run whose branch has been merged into `main` and pulled:

```bash
git checkout main && git pull
python3 scripts/workstation/oleans.py pack ~/ew-oleans.tar.gz PlasmaLean.Design.RationalStellaratorGCEwFamily
# or only some modules (smaller; their imports must already be built on the laptop):
python3 scripts/workstation/oleans.py pack --only ~/mu3.tar.gz 'PlasmaLean.Design.RationalStellaratorGCMu3*'
```

Copy the archive to the laptop (Google Drive, `scp`, …), then on the laptop:

```bash
git pull
python3 scripts/workstation/oleans.py info   ~/Downloads/ew-oleans.tar.gz   # what is inside
python3 scripts/workstation/oleans.py unpack ~/Downloads/ew-oleans.tar.gz
```

- **What `unpack` checks before extracting:**
  - the Lean version and commit are the same on both machines;
  - `lake-manifest.json` is identical (same Mathlib);
  - every packed module's source is byte-identical to this clone's.

  If anything differs it refuses and names the commit to check out. After extracting, it runs
  `lake --no-build build` on the targets to confirm that Lake accepts them without rebuilding.
- **What is packed:** a target and all of its PlasmaLean imports, transitively; Mathlib is not
  included. A module's files are all of `.lake/build/lib/lean/<path>.*` and
  `.lake/build/ir/<path>.*`. For scale: Mu3 with its imports is 247 modules and 208 MB, and with
  `--only` it is 100 modules and 67 MB.
- **Trust:** unpacked modules are **not** re-checked by the kernel on the laptop. That is what saves
  the time, and it means trusting the workstation's build, as with the on-demand spot-check policy.
  Default-build modules should still be built here.
- **Status:** works across platforms. On 26 October 2026, Mu2–Mu5 (400 modules, 314 MB) were packed
  on the Linux workstation, unpacked on the Mac laptop, and Lake accepted them without rebuilding.

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

**Status (30 October 2026): run now.** Main item: the Dommaschk quasi-axisymmetric fit (Q-16,
N-31, task `dommaschk-qa`), the main route to a candidate satisfying C1 + C2 of the stellarator
contract. Untrusted numerics only, no Lean build (verdict "no Lean modules"). It commits
`scripts/dommaschk_qa/results/<stamp>/`: `candidate.json` (exact rational coefficients),
`summary.json` (axis, nesting, ι, QA defect by helicity, ε_eff, defect/ι and the Q-16 tier),
`starts.json` and three PNG plots. The task file must be on `main` first. Restartable: if a run is
interrupted, start it again with the same parameters and finished starts are skipped.

Medium run (24 coefficients, 16 starts; about 1 CPU-hour, about 10–15 min wall with 16 jobs):

```bash
cd PlasmaLean && git pull
DQA_NMAX=2 DQA_STARTS=16 DQA_IOTA_MIN=0.2 scripts/workstation/run.sh --jobs 16 dommaschk-qa
```

Larger run, after the medium one has been reviewed (62 coefficients, 32 starts, stronger ι target,
wider surfaces; about 25 CPU-hours, so about 1.5 h wall with 16 jobs, capped at 4 h per start by
`DQA_TIME`):

```bash
DQA_NMAX=4 DQA_STARTS=32 DQA_IOTA_MIN=0.3 DQA_NFEV=150 DQA_NPER=300 DQA_SURFACES=0.02,0.05,0.08 \
  scripts/workstation/run.sh --jobs 16 dommaschk-qa
```

Memory: about 0.6 GB per process for the medium run and up to about 2 GB for the larger one
(lower `--jobs` if needed). The estimates are scaled from laptop timings: one objective
evaluation plus its batched Jacobian takes about 3.5 s for 24 coefficients and 15 s for 62.

**Optional, lower priority (still valid, not urgent).** Phase 16 stages 8–9 changed the Mu chain
modules, so the on-demand families downstream of them (Mu2–Mu5, MuQuarter, Ew1–4) are stale on
both machines (their sources are unchanged). When convenient, rebuild them on the workstation and
send the compiled files back:

```bash
cd PlasmaLean && git pull
lake build PlasmaLean.Design.RationalStellaratorGCMuQuarter PlasmaLean.Design.RationalStellaratorGCEwFamily
python3 scripts/workstation/oleans.py pack ~/ondemand.tar.gz \
  PlasmaLean.Design.RationalStellaratorGCMuQuarter PlasmaLean.Design.RationalStellaratorGCEwFamily
```

Copy `~/ondemand.tar.gz` to the laptop and say where it is.

Then say "update from workstation" on the laptop.
