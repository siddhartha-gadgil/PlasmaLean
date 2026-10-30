# Dommaschk quasi-axisymmetric fit (Q-16, N-27 route ii, N-31): an explicit VACUUM field
# B = grad(phi + sum_k a_k V_k) (Dommaschk potentials, exactly harmonic, so current-free: contract
# clause C1 reduces to iota >= iota_min) fitted for quasi-axisymmetry (clause C2 in its QS form) with
# a NON-PLANAR magnetic axis (N-30: a planar axis forces an O(r) QA defect, Garren-Boozer).
# Untrusted numerics only: there is NO Lean emission or build yet. The deliverable is a candidate
# (exact rational coefficients) plus diagnostics, for the later certificate stage (KAM tori by the
# existing pipeline, Boozer angles by one cohomological equation). See notes/theory/dommaschk-qa.md.
#
# The file is sourced by scripts/workstation/run.sh (bash 3.2 compatible). Only $WS_PY, $WS_WORK
# and $WS_JOBS are used.
#
# Parameters (environment):
#   DQA_NMAX      Dommaschk order: toroidal modes m = 2i, i <= DQA_NMAX (default 2)
#   DQA_LMAX      maximal z-degree l of the potentials (default DQA_NMAX + 2)
#                 coefficients: 24 for (2, 4), 42 for (3, 5), 62 for (4, 6)
#   DQA_STARTS    random starts, run DQA_STARTS at a time up to WS_JOBS in parallel (default 16)
#   DQA_IOTA_MIN  required |iota| on the optimised surfaces (default 0.2)
#   DQA_SURFACES  launch distances from the axis on phi = 0, comma separated (default 0.02,0.04,0.06)
#   DQA_NFEV      least-squares evaluations per start and stage (default 60; stage A gets 4x)
#   DQA_NPER      field periods traced per objective evaluation (default 200)
#   DQA_TIME      time limit per start in seconds (default 14400)
#   DQA_EXTRA     further options for scripts/dommaschk_qa/optimize.py (default empty)
DQA_NMAX="${DQA_NMAX:-2}"
DQA_LMAX="${DQA_LMAX:-$((DQA_NMAX + 2))}"
DQA_STARTS="${DQA_STARTS:-16}"
DQA_IOTA_MIN="${DQA_IOTA_MIN:-0.2}"
DQA_SURFACES="${DQA_SURFACES:-0.02,0.04,0.06}"
DQA_NFEV="${DQA_NFEV:-60}"
DQA_NPER="${DQA_NPER:-200}"
DQA_TIME="${DQA_TIME:-14400}"
DQA_EXTRA="${DQA_EXTRA:-}"

TASK_DESC="Dommaschk QA fit (nmax ${DQA_NMAX}, lmax ${DQA_LMAX}, ${DQA_STARTS} starts, iota >= ${DQA_IOTA_MIN}): vacuum C1+C2 candidate, untrusted"

# No Lean yet (verdict "no Lean modules"); the certificate stage will add modules here.
TASK_MODULES=""
TASK_ENTRYPOINTS=""

# Candidate (exact rational coefficients), summary.json, starts.json and PNG plots (< 1 MB each).
TASK_OUTPUTS="scripts/dommaschk_qa/results"
TASK_ARTIFACTS=""
TASK_TARGET="default"

# Restartable: the work directory is keyed by the parameters; finished starts are skipped and
# interrupted starts resume from their checkpoints. Each run writes a new results/<UTC stamp>/.
task_numerics() {
  local tag="n${DQA_NMAX}l${DQA_LMAX}s${DQA_STARTS}i${DQA_IOTA_MIN}r$(echo "$DQA_SURFACES" | tr ',' '_')f${DQA_NFEV}p${DQA_NPER}"
  local work="$WS_WORK/dommaschk-qa/$tag"
  local stamp; stamp="$(date -u +%Y%m%dT%H%M%SZ)"
  mkdir -p "$work"
  "$WS_PY" -I scripts/dommaschk_qa/validate.py > "$work/validate.log" 2>&1 || { cat "$work/validate.log"; return 1; }
  # shellcheck disable=SC2086
  "$WS_PY" -I scripts/dommaschk_qa/optimize.py --work "$work" \
    --results "scripts/dommaschk_qa/results/$stamp" --jobs "$WS_JOBS" \
    --nmax "$DQA_NMAX" --lmax "$DQA_LMAX" --starts "$DQA_STARTS" --iota-min "$DQA_IOTA_MIN" \
    --surfaces "$DQA_SURFACES" --max-nfev "$DQA_NFEV" --nper "$DQA_NPER" --time-limit "$DQA_TIME" \
    $DQA_EXTRA || return 1
  cp "$work/validate.log" "scripts/dommaschk_qa/results/$stamp/"
}
