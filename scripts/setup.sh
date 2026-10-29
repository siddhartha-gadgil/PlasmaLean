#!/usr/bin/env bash
# One-time (idempotent) setup of a PlasmaLean clone on Linux or macOS.
#
# usage: scripts/setup.sh [--check-axioms] [--python] [--no-build] [-h|--help]
#   --check-axioms   after the build, run `lake env lean scripts/check_axioms.lean` (default build;
#                    on-demand top modules are audited separately by scripts/check_axioms_heavy.lean)
#   --python         create the Python venv .venv-ws from scripts/requirements.txt (used by the
#                    untrusted oracle scripts and the workstation pipeline)
#   --no-build       stop after fetching the Mathlib cache (skip `lake build`)
#   -h, --help       show this help
#
# Steps: install elan if missing (the toolchain itself is chosen by elan from `lean-toolchain`),
# fetch the prebuilt Mathlib oleans (`lake exe cache get`), build the default library PlasmaLean
# (`lake build`; several hundred certificate modules, keep each process within about 6 GB).
# Running it again only redoes what is missing or stale.

set -euo pipefail

say() { printf '\n==> %s\n' "$*"; }
die() { printf 'error: %s\n' "$*" >&2; exit 1; }

CHECK_AXIOMS=0; PYTHON=0; BUILD=1
while [ $# -gt 0 ]; do
  case "$1" in
    --check-axioms) CHECK_AXIOMS=1 ;;
    --python) PYTHON=1 ;;
    --no-build) BUILD=0 ;;
    -h|--help) sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) die "unknown option $1 (see --help)" ;;
  esac
  shift
done

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"
[ -f lean-toolchain ] || die "lean-toolchain not found in $REPO"
[ -f PlasmaLean.lean ] || die "PlasmaLean.lean not found in $REPO (not a PlasmaLean checkout?)"

# 1. elan (Lean toolchain manager)
if command -v elan >/dev/null 2>&1 || [ -x "$HOME/.elan/bin/elan" ]; then
  say "elan already installed"
else
  say "installing elan"
  command -v curl >/dev/null 2>&1 || die "curl is required to install elan"
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --default-toolchain none
fi
if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1091
  . "$HOME/.elan/env"
fi
command -v lake >/dev/null 2>&1 || die "lake not on PATH after installing elan (open a new shell)"

# 2. toolchain: elan reads lean-toolchain and installs it on first use
say "toolchain $(cat lean-toolchain) (selected by elan from lean-toolchain)"
lean --version

# 3. Mathlib cache
say "fetching the Mathlib cache (lake exe cache get)"
lake exe cache get

# 4. build
if [ "$BUILD" = 1 ]; then
  say "building the default library PlasmaLean (lake build)"
  lake build
  if [ "$CHECK_AXIOMS" = 1 ]; then
    say "axiom audit (scripts/check_axioms.lean)"
    lake env lean scripts/check_axioms.lean
  fi
elif [ "$CHECK_AXIOMS" = 1 ]; then
  say "skipping the axiom audit: it needs the build (drop --no-build)"
fi

# 5. optional Python environment
if [ "$PYTHON" = 1 ]; then
  command -v python3 >/dev/null 2>&1 || die "python3 is required for --python"
  if [ ! -x .venv-ws/bin/python ]; then
    say "creating the Python venv .venv-ws"
    python3 -m venv .venv-ws
  else
    say "Python venv .venv-ws already exists"
  fi
  .venv-ws/bin/python -m pip install --quiet --upgrade pip
  .venv-ws/bin/python -m pip install --quiet -r scripts/requirements.txt
  say "python packages installed in .venv-ws"
fi

say "setup complete"
