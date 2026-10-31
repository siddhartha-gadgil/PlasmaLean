#!/usr/bin/env bash
# GENERATED on the laptop after each review ("update from workstation"); mirrors "Next Commands"
# in Workstation.md. Run by scripts/workstation/poll.sh once per NEXT_ID, or by hand:
#   bash scripts/workstation/next.sh
# Commands run one after the other; a failing command does not stop the later ones.
NEXT_ID="2026-10-31-warmstart"

cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1
rc=0
step() { echo "=== $(date '+%Y-%m-%d %H:%M:%S') $*"; "$@" || { echo "=== failed (exit $?): $*"; rc=1; }; }

# Warm-start refinement (N-31 §14): from the NFP 3 lead candidate (§15), then from the NFP 2
# candidate (§10). About 10-15 min wall each.
step env DQA_NMAX=2 DQA_STARTS=48 DQA_IOTA_MIN=0.25 DQA_SURFACES=0.015,0.03,0.045 DQA_NFEV=60 \
  DQA_EXTRA="--nfp 3 --init scripts/dommaschk_qa/results/20261031T044845Z/candidate.json --init-sigma 0.001" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa
step env DQA_NMAX=3 DQA_STARTS=48 DQA_IOTA_MIN=0.2 DQA_SURFACES=0.015,0.03,0.045 DQA_NFEV=60 \
  DQA_EXTRA="--init scripts/dommaschk_qa/results/20261030T120952Z/candidate.json --init-sigma 0.002" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa

exit $rc
