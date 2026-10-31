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
- **Status:** works across platforms, with one extra step for modules downstream of the native
  `PlasmaLeanMeta` library. On 26 October 2026, Mu2–Mu5 (400 modules, 314 MB) were packed on the
  Linux workstation, unpacked on the Mac laptop, and Lake accepted them without rebuilding; that
  was before the Mu chains imported `PlasmaLean.Certificates.EvalCert`.
- **Modules downstream of `PlasmaLean.Certificates.EvalCert`.** Their traces include a hash of the
  precompiled `PlasmaLeanMeta` library: `.so` on Linux, `.dylib` on macOS. Lake therefore rejects
  them on the other platform, although their compiled outputs are the same. In that case:

  ```bash
  python3 scripts/workstation/oleans.py unpack  ~/Downloads/ondemand.tar.gz   # reports "NOT up to date"
  lake build PlasmaLean          # rebuild the default-build modules here (bounded; see the skills)
  python3 scripts/workstation/oleans.py retrace ~/Downloads/ondemand.tar.gz
  ```

  `retrace` handles only modules outside the default build (user decision, 30 October 2026). It
  checks that their sources match and that their installed outputs are byte-identical to the
  archive's. It then rewrites each trace's inputs and hash to the ones Lake expects here, layer by
  layer, until Lake accepts the targets. It refuses if a default-build module is out of date.
  Trust is the same as for `unpack`.

  First use, 30 October 2026: the MuQuarter and EwFamily archive (1,010 modules, 738 MB). Lake
  rejected 102 modules downstream of `EvalCert`. The 45 default-build ones among them were rebuilt
  here, then 57 on-demand modules were retraced in 8 rounds (about 1 minute). The 12 Mu2–Mu5,
  MuQuarter and Ew entry points load with standard axioms only.

## Unattended polling

When the connection to the workstation is unreliable, leave a poller running there. It picks up
new commands from `main` by itself:

```bash
ssh workstation
tmux new -s poll
cd PlasmaLean && git checkout main && git pull
scripts/workstation/poll.sh            # every 10 minutes; --interval SECONDS, --once
```

- **What it runs.** Every 10 minutes, if the workstation is idle (no `run.sh` and no `lake`
  running), it pulls `main` and reads `NEXT_ID` in
  [`scripts/workstation/next.sh`](scripts/workstation/next.sh). For a `NEXT_ID` it has not run
  before, it runs `next.sh` once.
- **Who writes `next.sh`.** The laptop rewrites it after every review, together with "Next
  Commands" below; the two always agree. When there is nothing to do, `next.sh` only prints a
  message saying so.
- **Failures.** Each batch runs once, whether it succeeds or fails; a failed batch is not
  retried. To retry, the laptop issues a new `NEXT_ID`.
- **Logs.** In `$WS_WORK/poll/` (default `~/plasmalean-work/poll/`): `poll.log`, one
  `<NEXT_ID>.log` per batch, and a `done-<NEXT_ID>` marker per batch.
- **Status for the laptop.** At the start and end of each batch the poller pushes a one-file
  commit (`status.txt`: host, time, batch, state and the tail of the log) to the branch
  `ws-status`. It uses git plumbing, so the working tree is not touched. `pending.sh` prints it;
  by hand, `git fetch origin ws-status && git show origin/ws-status:status.txt`.
- **Updates.** If a pull changes `poll.sh`, the poller re-executes the new version. It never pulls
  over modified tracked files, and says so in its log.
- **Trust.** `next.sh` is executed as found on `main`. Only push `next.sh` changes you would run
  by hand.

Results come back as usual: each `run.sh` inside a batch pushes its own `workstation/...` branch,
and "update from workstation" on the laptop reviews them.

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

Kept up to date from the laptop after every review ("update from workstation"). The same
commands are in [`scripts/workstation/next.sh`](scripts/workstation/next.sh), with `NEXT_ID` =
`2026-10-31-warmstart`, which the poller runs by itself (see "Unattended polling"). By hand, run
them inside `tmux` (`run.sh` pulls `main` itself), or run `bash scripts/workstation/next.sh`.

**Status (31 October 2026, after both NFP 3 runs): run now.** NFP 3 with only 24 coefficients
gave the first candidate that passes every Q-16 check: defect/ι 0.007–0.020 at |ι| ≈ 0.28,
ε_eff 0.13–0.47 % (N-31 §15). The 42-coefficient NFP 3 run was worse: it crosses the 1/3 and 3/10
resonances (N-31 §16). Next are the two warm-start runs below.

**Warm-start refinement** (N-31 §14; `--init` is on `main`). The first run
restarts from the NFP 3 candidate of N-31 §15, the lead candidate. The second restarts from the
NFP 2 candidate of N-31 §10, where a 2-start laptop test already found a nearby moderate-tier field
with |ι| ≈ 0.32. Both use small random perturbations and go straight into the full objective.
Each takes about 10–15 min wall. Run them one after the other:

```bash
cd PlasmaLean && git pull
DQA_NMAX=2 DQA_STARTS=48 DQA_IOTA_MIN=0.25 DQA_SURFACES=0.015,0.03,0.045 DQA_NFEV=60 \
  DQA_EXTRA="--nfp 3 --init scripts/dommaschk_qa/results/20261031T044845Z/candidate.json --init-sigma 0.001" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa
DQA_NMAX=3 DQA_STARTS=48 DQA_IOTA_MIN=0.2 DQA_SURFACES=0.015,0.03,0.045 DQA_NFEV=60 \
  DQA_EXTRA="--init scripts/dommaschk_qa/results/20261030T120952Z/candidate.json --init-sigma 0.002" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa
```

**On-demand olean transfer: resolved (30 October 2026).** The MuQuarter and EwFamily archive is
installed on the laptop via `oleans.py retrace` (see "Sharing compiled files"). The pack step can
be used again when needed.

Then say "update from workstation" on the laptop.
