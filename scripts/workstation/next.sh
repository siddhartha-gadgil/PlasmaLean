#!/usr/bin/env bash
# GENERATED on the laptop after each review ("update from workstation"); mirrors "Next Commands"
# in Workstation.md. Run by scripts/workstation/poll.sh once per NEXT_ID, or by hand:
#   bash scripts/workstation/next.sh
# Commands run one after the other; a failing command does not stop the later ones.
NEXT_ID="2026-10-31-kam-A-C"

cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1
rc=0
step() { echo "=== $(date '+%Y-%m-%d %H:%M:%S') $*"; "$@" || { echo "=== failed (exit $?): $*"; rc=1; }; }

# Certification step 2 numerics (N-31 §25): KAM flow tori A and C of the certification target at
# 80 x 64 modes, 50-digit refinement (about 20,800 unknowns; peak about 8 GB).
step env DKAM_TORI=A,C DKAM_N=80 DKAM_M=64 DKAM_DPS=50 \
  scripts/workstation/run.sh dommaschk-kam

exit $rc
