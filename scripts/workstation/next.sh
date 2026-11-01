#!/usr/bin/env bash
# GENERATED on the laptop after each review ("update from workstation"); mirrors "Next Commands"
# in Workstation.md. Run by scripts/workstation/poll.sh once per NEXT_ID, or by hand:
#   bash scripts/workstation/next.sh
# Commands run one after the other; a failing command does not stop the later ones.
NEXT_ID="2026-11-02-kam-A-96"

cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1
rc=0
step() { echo "=== $(date '+%Y-%m-%d %H:%M:%S') $*"; "$@" || { echo "=== failed (exit $?): $*"; rc=1; }; }

# Second certified torus for a nested region (Q-16): torus A (iota = -(19+sqrt5)/89, outside torus
# C) at 96 x 80 modes, 60-digit refinement, with the coefficient export (torus_A_N96_M80.json).
# About 5-10 min wall, peak about 16 GB. Then torus B (outer, near 3/13) at 96 x 80 for comparison.
step env DKAM_TORI=A DKAM_N=96 DKAM_M=80 DKAM_DPS=60 scripts/workstation/run.sh dommaschk-kam
step env DKAM_TORI=B DKAM_N=96 DKAM_M=80 DKAM_DPS=60 scripts/workstation/run.sh dommaschk-kam

exit $rc
