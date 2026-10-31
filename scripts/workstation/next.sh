#!/usr/bin/env bash
# GENERATED on the laptop after each review ("update from workstation"); mirrors "Next Commands"
# in Workstation.md. Run by scripts/workstation/poll.sh once per NEXT_ID, or by hand:
#   bash scripts/workstation/next.sh
# Commands run one after the other; a failing command does not stop the later ones.
NEXT_ID="2026-10-31-refine-target"

cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1
rc=0
step() { echo "=== $(date '+%Y-%m-%d %H:%M:%S') $*"; "$@" || { echo "=== failed (exit $?): $*"; rc=1; }; }

# Refine the certification target (N-31 §22: NFP 2, purely rational, strong tier) to enlarge the
# nested region while keeping the strong tier: warm starts, --exclude-log, surfaces pushed out to
# r = 0.06, transform window between 2/9 and 1/4. About 20 min wall each.
T=scripts/dommaschk_qa/results/20261031T085357Z/candidate.json
step env DQA_NMAX=3 DQA_STARTS=48 DQA_IOTA_MIN=0.2 DQA_SURFACES=0.02,0.04,0.06 DQA_NFEV=60 \
  DQA_EXTRA="--exclude-log --init $T --init-sigma 0.001 --iota-window 0.2235,0.2495" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa
step env DQA_NMAX=3 DQA_STARTS=48 DQA_IOTA_MIN=0.2 DQA_SURFACES=0.015,0.03,0.045 DQA_NFEV=60 \
  DQA_EXTRA="--exclude-log --init $T --init-sigma 0.0005" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa

exit $rc
