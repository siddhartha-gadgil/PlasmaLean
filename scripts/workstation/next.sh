#!/usr/bin/env bash
# GENERATED on the laptop after each review ("update from workstation"); mirrors "Next Commands"
# in Workstation.md. Run by scripts/workstation/poll.sh once per NEXT_ID, or by hand:
#   bash scripts/workstation/next.sh
# Commands run one after the other; a failing command does not stop the later ones.
NEXT_ID="2026-11-01-kam-export"

cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1
rc=0
step() { echo "=== $(date '+%Y-%m-%d %H:%M:%S') $*"; "$@" || { echo "=== failed (exit $?): $*"; rc=1; }; }

# Export the refined coefficients of the certification torus C (N-33 item 6) into the committed
# results (torus_C_N*_M*.json). Both runs are cached in the work directory, so only the export runs
# (about a minute each).
step env DKAM_TORI=C DKAM_N=80 DKAM_M=64 DKAM_DPS=50 scripts/workstation/run.sh dommaschk-kam
step env DKAM_TORI=C DKAM_N=96 DKAM_M=80 DKAM_DPS=60 scripts/workstation/run.sh dommaschk-kam

exit $rc
