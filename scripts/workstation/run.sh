#!/usr/bin/env bash
# PlasmaLean workstation pipeline: heavy numerics + Lean certificate build on a big machine,
# results committed to a git branch and pushed, to be pulled and re-checked on the laptop.
# See Workstation.md. Compatible with bash 3.2 (macOS) so that --verify-only runs locally.
#
# usage: scripts/workstation/run.sh [options] TASK...
#   --list            list the available tasks and exit
#   --setup-only      check lake/python and install the Python packages (venv .venv-ws), exit
#   --verify-only     laptop mode: skip setup installs, numerics and emission; build the task's
#                     Lean modules with resource measurement and the laptop budget; no git
#   --skip-numerics   run emission and the Lean build only (numerics outputs already present)
#   --no-push         commit on the results branch but do not push
#   --skip-push-check do not test non-interactive push access before starting
#   --branch NAME     results branch (default workstation/<tasks>-<UTC stamp>)
#   --jobs N          parallelism exported to tasks as WS_JOBS (default: number of CPUs)
# environment:
#   WS_WORK                 scratch directory for large intermediate data (default ~/plasmalean-work)
#   LAPTOP_MAX_RSS_GB       per-process peak memory allowed on the laptop (default 6)
#   LAPTOP_DEFAULT_CPU_MIN  Lean CPU budget for the default build (default 60)
#   LAPTOP_MAX_CPU_MIN      Lean CPU budget for an on-demand top module (default 240)
#   LAPTOP_SLOWDOWN         laptop/workstation per-core time ratio applied to CPU time (default 1.0)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/../.." && pwd)"
TASK_DIR="$SCRIPT_DIR/tasks"
HELPER="$SCRIPT_DIR/ws_helper.py"
VENV="$REPO/.venv-ws"
export WS_WORK="${WS_WORK:-$HOME/plasmalean-work}"
export WS_PY="$VENV/bin/python"
export WS_REPO="$REPO"

say() { printf '\n==> %s\n' "$*"; }
die() { printf 'error: %s\n' "$*" >&2; exit 1; }

ncpu() { nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4; }

# Default (empty) task interface; a task file in tasks/ overrides what it needs.
load_task() {
  TASK_DESC=""
  TASK_MODULES=""       # Lean modules to build, dependencies first
  TASK_ENTRYPOINTS=""   # declarations checked with #print axioms
  TASK_OUTPUTS=""       # paths/globs committed to the results branch
  TASK_ARTIFACTS=""     # optional extra files copied to workstation/artifacts/<task>/
  TASK_TARGET="default" # intended laptop build: default | separate
  task_numerics() { :; }
  task_emit() { :; }
  local f="$TASK_DIR/$1.sh"
  [ -f "$f" ] || die "unknown task '$1' (see --list)"
  # shellcheck disable=SC1090
  . "$f"
}

# Internal re-entry: run one task function so that it can be measured as a process.
if [ "${1:-}" = "__step" ]; then
  cd "$REPO"
  load_task "$3"
  "task_$2"
  exit $?
fi

ORIG_ARGS=("$@")
PUSH_CHECK=1; LIST=0; SETUP_ONLY=0; VERIFY=0; SKIP_NUM=0; PUSH=1; BRANCH=""; JOBS="$(ncpu)"; TASKS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --list) LIST=1 ;;
    --setup-only) SETUP_ONLY=1 ;;
    --verify-only) VERIFY=1 ;;
    --skip-numerics) SKIP_NUM=1 ;;
    --no-push) PUSH=0 ;;
    --skip-push-check) PUSH_CHECK=0 ;;
    --branch) shift; BRANCH="${1:?--branch needs a name}" ;;
    --jobs) shift; JOBS="${1:?--jobs needs a number}" ;;
    -h|--help) sed -n '2,21p' "$0"; exit 0 ;;
    -*) die "unknown option $1" ;;
    *) TASKS="$TASKS $1" ;;
  esac
  shift
done
export WS_JOBS="$JOBS"
cd "$REPO"

# Always start from an up-to-date main (a previous run leaves results on its own branch), then
# re-run the updated copy of this script.
if [ "$VERIFY" = 0 ] && [ "$LIST" = 0 ] && [ -z "${WS_SYNCED:-}" ]; then
  [ -z "$(git status --porcelain --untracked-files=no)" ] \
    || die "tracked files are modified; run in a clean clone"
  cur="$(git rev-parse --abbrev-ref HEAD)"
  if [ "$cur" != main ]; then say "switching from $cur to main"; git checkout -q main; fi
  git pull --ff-only -q
  export WS_SYNCED=1
  exec bash "$SCRIPT_DIR/run.sh" ${ORIG_ARGS[@]+"${ORIG_ARGS[@]}"}
fi

if [ "$LIST" = 1 ]; then
  for f in "$TASK_DIR"/*.sh; do
    t="$(basename "$f" .sh)"
    [ "$t" = TEMPLATE ] && continue
    load_task "$t"
    printf '%-24s %s\n' "$t" "$TASK_DESC"
  done
  exit 0
fi

# ---------------------------------------------------------------- setup
setup() {
  # Lean (elan, lake), the Mathlib cache and the library build are prepared once by hand on the
  # workstation (see Workstation.md); here we only check them and install the Python packages.
  command -v git >/dev/null || die "git is required"
  command -v python3 >/dev/null || die "python3 (>= 3.10) is required"
  python3 -c 'import sys; sys.exit(sys.version_info < (3, 10))' || die "python3 >= 3.10 required"
  if ! command -v lake >/dev/null; then
    [ -x "$HOME/.elan/bin/lake" ] || die "lake not found (install elan; see Workstation.md)"
    export PATH="$HOME/.elan/bin:$PATH"
  fi
  if [ "$VERIFY" = 1 ]; then return; fi
  if [ ! -x "$WS_PY" ]; then
    say "creating Python venv $VENV"
    python3 -m venv "$VENV"
  fi
  "$WS_PY" -m pip install -q --upgrade pip
  "$WS_PY" -m pip install -q -r "$REPO/scripts/requirements.txt"
  mkdir -p "$WS_WORK"
}

# Fail early (not after hours of work) if pushing would need a password typed by hand.
check_push_auth() {
  say "checking non-interactive push access to origin ($(git remote get-url origin))"
  local err
  if ! err="$(GIT_TERMINAL_PROMPT=0 GIT_SSH_COMMAND="${GIT_SSH_COMMAND:-ssh} -o BatchMode=yes" \
       git push --dry-run origin HEAD:refs/heads/workstation/auth-check 2>&1)"; then
    printf '%s\n' "$err" >&2
    die "git push --dry-run to origin failed without a terminal prompt (output above). Set up an ssh
       key or a stored credential (Workstation.md, 'Push access'), or skip this check with
       --skip-push-check if you are sure pushing works unattended"
  fi
}

setup
if [ "$VERIFY" = 0 ] && [ "$PUSH" = 1 ] && [ "$PUSH_CHECK" = 1 ]; then check_push_auth; fi
if [ "$SETUP_ONLY" = 1 ]; then say "setup complete"; exit 0; fi
[ -n "$TASKS" ] || die "no task given (see --list)"
for t in $TASKS; do [ -f "$TASK_DIR/$t.sh" ] || die "unknown task '$t'"; done

STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
BASE="$(git rev-parse --short HEAD)"

# ---------------------------------------------------------------- git branch
if [ "$VERIFY" = 0 ]; then
  [ -z "$(git status --porcelain --untracked-files=no)" ] \
    || die "tracked files are modified; run in a clean clone"
  BASE="$(git rev-parse --short HEAD)"
  [ -n "$BRANCH" ] || BRANCH="workstation/$(echo $TASKS | tr ' ' '+')-$STAMP"
  git checkout -b "$BRANCH"
  RESULTS="$REPO/workstation/results"
else
  RESULTS="${TMPDIR:-/tmp}/plasmalean-verify"
fi

# ---------------------------------------------------------------- tasks
step() { # step TASKOUT NAME CMD...
  local out="$1" name="$2"; shift 2
  say "[$name] $*"
  python3 "$HELPER" measure "$out/$name.step.json" "$out/$name.log" -- "$@"
}

ANY_FAIL=0
COMMIT_PATHS=""
for t in $TASKS; do
  load_task "$t"
  out="$RESULTS/$t/$STAMP"
  mkdir -p "$out"
  cat > "$out/meta.json" <<EOF
{"task": "$t", "description": "$TASK_DESC", "stamp": "$STAMP", "base_commit": "$BASE",
 "host": "$(hostname)", "os": "$(uname -sm)", "cpus": $(ncpu), "jobs": $JOBS,
 "mode": "$([ "$VERIFY" = 1 ] && echo verify || echo workstation)", "target": "$TASK_TARGET"}
EOF
  ok=1
  if [ "$VERIFY" = 0 ] && [ "$SKIP_NUM" = 0 ]; then
    step "$out" numerics bash "$SCRIPT_DIR/run.sh" __step numerics "$t" || ok=0
  fi
  if [ "$ok" = 1 ] && [ "$VERIFY" = 0 ]; then
    step "$out" emit bash "$SCRIPT_DIR/run.sh" __step emit "$t" || ok=0
  fi
  if [ "$ok" = 1 ]; then
    for m in $TASK_MODULES; do
      step "$out" "build-$m" lake build "$m" || { ok=0; break; }
    done
  fi
  if [ "$ok" = 1 ] && [ -n "$TASK_ENTRYPOINTS" ]; then
    axf="$out/axioms.lean"
    : > "$axf"
    for m in $TASK_MODULES; do echo "import $m" >> "$axf"; done
    for e in $TASK_ENTRYPOINTS; do echo "#print axioms $e" >> "$axf"; done
    if step "$out" axioms lake env lean "$axf"; then
      python3 "$HELPER" axioms "$out/axioms.log" || {
        ok=0
        python3 - "$out/axioms.step.json" <<'EOF'
import json, sys
p = sys.argv[1]; r = json.load(open(p)); r["status"] = "failed"; json.dump(r, open(p, "w"))
EOF
      }
    else
      ok=0
    fi
  fi
  python3 "$HELPER" summary "$out" || ANY_FAIL=1
  [ "$ok" = 1 ] || ANY_FAIL=1
  if [ "$VERIFY" = 0 ]; then
    COMMIT_PATHS="$COMMIT_PATHS workstation/results/$t/$STAMP"
    # generated files are committed even when a later step failed, so that the failure can be
    # reproduced on the laptop (a failed run is never merged)
    for g in $TASK_OUTPUTS; do
      for f in $g; do [ -e "$f" ] && COMMIT_PATHS="$COMMIT_PATHS $f"; done
    done
    if [ "$ok" = 1 ]; then
      if [ -n "$TASK_ARTIFACTS" ]; then
        mkdir -p "workstation/artifacts/$t"
        for a in $TASK_ARTIFACTS; do
          # keep the repository small: artifacts over 50 MB stay on the workstation
          if [ -f "$a" ] && [ "$(wc -c < "$a")" -le 52428800 ]; then
            cp "$a" "workstation/artifacts/$t/"
          else
            echo "artifact skipped (missing or > 50 MB): $a" | tee -a "$out/artifacts-skipped.txt"
          fi
        done
        COMMIT_PATHS="$COMMIT_PATHS workstation/artifacts/$t"
      fi
    fi
  fi
done

if [ "$VERIFY" = 1 ]; then
  say "verify-only results in $RESULTS (not committed)"
  exit "$ANY_FAIL"
fi

# ---------------------------------------------------------------- commit and push
say "committing results on $BRANCH"
# shellcheck disable=SC2086
git add -- $COMMIT_PATHS
git commit -q -m "Workstation run: $(echo $TASKS) ($STAMP, base $BASE)

$(for t in $TASKS; do
    python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["task"]+": "+d["laptop"]["verdict"])' \
      "workstation/results/$t/$STAMP/summary.json" 2>/dev/null || echo "$t: no summary"
  done)"
if [ "$PUSH" = 1 ]; then
  git push -u origin "$BRANCH"
  say "pushed $BRANCH; on the laptop: git fetch && scripts/workstation/run.sh --verify-only$TASKS"
else
  say "committed locally on $BRANCH (not pushed)"
fi
git checkout -q main
say "back on main"
exit "$ANY_FAIL"
