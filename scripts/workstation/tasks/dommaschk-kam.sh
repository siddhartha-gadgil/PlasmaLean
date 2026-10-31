# KAM flow-torus oracle for the Dommaschk certification target (notes/theory/dommaschk-qa.md §20,
# §24; candidate scripts/dommaschk_qa/results/20261031T092522Z/candidate.json, NFP 2, purely
# rational): stellarator-symmetric Fourier tori (R, z)(theta, phi) solving the flow-form invariance
# equation with a fixed Diophantine iota, double-precision Galerkin-Newton, multiprecision
# refinement, invariance error (sup and weighted l1 strip norms), ELP-S twist, shear and the
# FHL-type smallness ratio. UNTRUSTED numerics only: no Lean modules (verdict "no Lean modules").
# The Lean certificate (KamTorusA pattern) is a later step; see scripts/dommaschk_kam/README.md.
#
# The file is sourced by scripts/workstation/run.sh (bash 3.2 compatible). Only $WS_PY and
# $WS_WORK are used (the dense LU uses the BLAS threads of the venv's numpy).
#
# Parameters (environment):
#   DKAM_TORI   rotation numbers, comma separated (default A): A = -2[0;8,2,1,1,...] = -0.238608
#               (r_launch ~ 0.037), B = -2[0;8,1,1,...] = -0.232071 (r ~ 0.056, outer),
#               C = -2[0;8,3,1,1,...] = -0.241651 (r ~ 0.027), or cf:a1,a2,... for
#               iota = -2[0;a1,a2,...,1,1,...] (a1 = 8 keeps |iota| in (2/9, 1/4))
#   DKAM_N      theta modes |k| <= N (default 80)
#   DKAM_M      psi = 2 phi modes |m| <= M (default 64); unknowns 2(N(2M+1) + M) + 1,
#               dense Jacobian 8 n^2 bytes (80 x 64: n = 20769, 3.5 GB, peak ~8 GB; LU a few minutes)
#   DKAM_DPS    multiprecision digits of the refinement and error evaluation (default 50;
#               0 = double precision only)
#   DKAM_OVER   oversampling of the error grid relative to the Galerkin grid (default 2)
#   DKAM_EXTRA  further options for scripts/dommaschk_kam/run.py (default empty)
DKAM_TORI="${DKAM_TORI:-A}"
DKAM_N="${DKAM_N:-80}"
DKAM_M="${DKAM_M:-64}"
DKAM_DPS="${DKAM_DPS:-50}"
DKAM_OVER="${DKAM_OVER:-2}"
DKAM_EXTRA="${DKAM_EXTRA:-}"

TASK_DESC="Dommaschk KAM flow-torus oracle (tori ${DKAM_TORI}, N ${DKAM_N}, M ${DKAM_M}, dps ${DKAM_DPS}): invariance error, twist, FHL ratio; untrusted"

# No Lean (verdict "no Lean modules"); the KAM certificate step will add modules here.
TASK_MODULES=""
TASK_ENTRYPOINTS=""

# summary.json and log.txt (small).
TASK_OUTPUTS="scripts/dommaschk_kam/results"
TASK_ARTIFACTS=""
TASK_TARGET="default"

# Restartable: intermediate states (axis, launch radii, initial tori, double tori per continuation
# stage, multiprecision tori, error spectra) are cached in a work directory keyed by the candidate
# and stage parameters, so an interrupted run resumes at the last finished stage. Each run writes a
# new results/<UTC stamp>/.
task_numerics() {
  local work="$WS_WORK/dommaschk-kam/target-092522Z"
  local stamp; stamp="$(date -u +%Y%m%dT%H%M%SZ)"
  local res="scripts/dommaschk_kam/results/$stamp"
  mkdir -p "$work" "$res"
  # shellcheck disable=SC2086
  "$WS_PY" -I scripts/dommaschk_kam/run.py --work "$work" --results "$res" \
    --tori "$DKAM_TORI" --N "$DKAM_N" --M "$DKAM_M" --dps "$DKAM_DPS" --over "$DKAM_OVER" \
    $DKAM_EXTRA || return 1
}
