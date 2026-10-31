#!/usr/bin/env bash
# GENERATED on the laptop after each review ("update from workstation"); mirrors "Next Commands"
# in Workstation.md. Run by scripts/workstation/poll.sh once per NEXT_ID, or by hand:
#   bash scripts/workstation/next.sh
# Commands run one after the other; a failing command does not stop the later ones.
NEXT_ID="2026-11-01-kam-C-96"

cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1
rc=0
step() { echo "=== $(date '+%Y-%m-%d %H:%M:%S') $*"; "$@" || { echo "=== failed (exit $?): $*"; rc=1; }; }

# Certification step 2 numerics (N-31 §26): torus C, the preferred certification torus, at 96 x 80
# modes with 60-digit refinement for margin (about 31,000 unknowns; peak about 16 GB).
step env DKAM_TORI=C DKAM_N=96 DKAM_M=80 DKAM_DPS=60 \
  scripts/workstation/run.sh dommaschk-kam

exit $rc
