#!/usr/bin/env bash
# GENERATED on the laptop after each review ("update from workstation"); mirrors "Next Commands"
# in Workstation.md. Run by scripts/workstation/poll.sh once per NEXT_ID, or by hand:
#   bash scripts/workstation/next.sh
# Commands run one after the other; a failing command does not stop the later ones.
NEXT_ID="2026-10-31-rerank"

cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1
rc=0
step() { echo "=== $(date '+%Y-%m-%d %H:%M:%S') $*"; "$@" || { echo "=== failed (exit $?): $*"; rc=1; }; }

# Re-rank the two warm-start runs of batch 2026-10-31-warmstart at diagnostic resolution
# (N-31 §18). Same commands, so the finished starts are reused from the work directories; only
# the re-ranking and the diagnostics run (a few minutes each). starts.json now keeps all
# coefficients.
step env DQA_NMAX=2 DQA_STARTS=48 DQA_IOTA_MIN=0.25 DQA_SURFACES=0.015,0.03,0.045 DQA_NFEV=60 \
  DQA_EXTRA="--nfp 3 --init scripts/dommaschk_qa/results/20261031T044845Z/candidate.json --init-sigma 0.001" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa
step env DQA_NMAX=3 DQA_STARTS=48 DQA_IOTA_MIN=0.2 DQA_SURFACES=0.015,0.03,0.045 DQA_NFEV=60 \
  DQA_EXTRA="--init scripts/dommaschk_qa/results/20261030T120952Z/candidate.json --init-sigma 0.002" \
  scripts/workstation/run.sh --jobs 24 dommaschk-qa

exit $rc
