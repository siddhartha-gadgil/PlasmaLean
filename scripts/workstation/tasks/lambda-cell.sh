# One pitch-angle cell of passing alpha guiding centres with mu > 0: a Chebyshev-in-lambda family of
# exact KAM tori over lambda = mu B0/E in [LAM_LO, LAM_HI] at rho0 = 1/256 (3.5 MeV alphas at
# B0R0 ~ 69 T m), certified by the pipeline of the cell [0, 1/16] (scripts/gc_kam/lam_*.py, run with
# small patches by scripts/gc_kam/lamcell/*.py). It produces the Lean modules
# Design/RationalStellaratorGCMu${LAM_TAG}* (namespace PlasmaLean.Design.RationalStellaratorGC.Mu${LAM_TAG})
# up to the guiding-centre theorem Mu${LAM_TAG}.rationalStellarator_gc_mu_confined_forever.
# Combining cells (for example Design/RationalStellaratorGCMuWide for [0, 1/8]) is a separate,
# hand-written step. See notes/theory/gc-kam-status.md, section "second pitch cell".
#
# The file is sourced by scripts/workstation/run.sh (bash 3.2 compatible). Only $WS_PY, $WS_WORK
# and $WS_JOBS are used; Lean and Mathlib must already be set up.
#
# Parameters (environment):
#   LAM_LO, LAM_HI  cell endpoints, rationals (default 1/16 and 1/8). 2/(LAM_HI - LAM_LO) and
#                   LAM_LO * 2/(LAM_HI - LAM_LO) must be integers and 0 <= LAM_LO < LAM_HI <= 1/4.
#                   Cells wider than 1/16 or ending above 1/8 need a higher Chebyshev degree, which
#                   breaks the 6 GB kernel budget (see the notes); the numerics then fail or the
#                   verdict says TOO BIG.
#   LAM_TAG         module tag (default 2). Use a new tag for every new cell.
#   LAM_GH, LAM_GL  number of high/low-resolution kernel-check modules (default 64, 8). With
#                   LAM_HCAP=1 every high-resolution module holds at most one double-width check
#                   (each about 4.3 GB of kernel memory), which keeps every process under 6 GB.
LAM_LO="${LAM_LO:-1/16}"
LAM_HI="${LAM_HI:-1/8}"
LAM_TAG="${LAM_TAG:-2}"
LAM_GH="${LAM_GH:-64}"
LAM_GL="${LAM_GL:-8}"
export LAM_LO LAM_HI LAM_TAG LAM_GH LAM_GL
export LAM_HCAP="${LAM_HCAP:-1}"

TASK_DESC="pitch cell lambda in [${LAM_LO}, ${LAM_HI}] (tag Mu${LAM_TAG}): confinement of passing alpha GCs with mu > 0"

_lc_modules() {
  local P="PlasmaLean.Design.RationalStellaratorGCMu${LAM_TAG}" k
  printf '%sDataL ' "$P"
  for k in 1 2 3 4 5 6; do printf '%sDataH%d ' "$P" "$k"; done
  printf '%sKvL %sKvH %sTreesL %sTreesH %sEnvL %sEnvH %sRelL %sRelH ' "$P" "$P" "$P" "$P" "$P" "$P" "$P" "$P"
  for k in $(seq 1 "$LAM_GL"); do printf '%sCheckL%d ' "$P" "$k"; done
  for k in $(seq 1 "$LAM_GH"); do printf '%sCheckH%d ' "$P" "$k"; done
  printf '%sChainL %sChainH %sOutL %sOutH %sMaj %sAdm %sExact %sForever %sConfined' \
    "$P" "$P" "$P" "$P" "$P" "$P" "$P" "$P" "$P"
}

# Lean modules, dependencies first (each built in its own process). Measured on the laptop for
# [1/16, 1/8] (97 modules with the hand-written MuWide): 31 CPU-min, 29 min wall. Peak RSS 7.8 GB
# (CheckH3); 10 check modules are above 6 GB. The certified cell [0, 1/16] measures the same way
# (its CheckH1 is 8.8 GB). See notes/theory/gc-kam-status.md.
TASK_MODULES="$(_lc_modules)"

TASK_ENTRYPOINTS="PlasmaLean.Design.RationalStellaratorGC.Mu${LAM_TAG}.rationalStellarator_gc_mu_confined_forever \
PlasmaLean.Design.RationalStellaratorGC.Mu${LAM_TAG}.mu_family_torus \
PlasmaLean.Design.RationalStellaratorGC.Mu${LAM_TAG}.mu_family_master"

TASK_OUTPUTS="PlasmaLean/Design/RationalStellaratorGCMu${LAM_TAG}*.lean"

TASK_ARTIFACTS=""

# About 31 CPU-minutes of Lean for a cell of width 1/16. That is within the default-build CPU budget,
# but some kernel checks peak above 6 GB, as they do in the default-build cell [0, 1/16].
TASK_TARGET="separate"  # merged as on-demand top modules (peaks > 6 GB)

# Untrusted numerics (restartable: finished steps are skipped). Peak memory: ~1 GB per torus process,
# several GB for the high-resolution ball pipeline (cert.py H).
task_numerics() {
  local G=scripts/gc_kam/lamcell
  export LAM_WORK="$WS_WORK/lambda-cell-${LAM_TAG}"
  mkdir -p "$LAM_WORK/tori"
  [ -f "$LAM_WORK/init.npz" ] || "$WS_PY" -I $G/tori.py init || return 1
  # 16 Chebyshev nodes in lambda; torus files that exist are skipped by tori.py
  seq 0 15 | xargs -P "$WS_JOBS" -I{} sh -c \
    '"$0" -I scripts/gc_kam/lamcell/tori.py 28 20 16 {} > "$1/tori/log_{}.txt" 2>&1' \
    "$WS_PY" "$LAM_WORK" || return 1
  [ -f "$LAM_WORK/cheb.npz" ] || "$WS_PY" -I $G/tori.py cheb 28 20 16 > "$LAM_WORK/cheb.log" || return 1
  [ -f "$LAM_WORK/lam_cert_H.pkl" ] || "$WS_PY" -I $G/cert.py H > "$LAM_WORK/cert_H.log" || return 1
  [ -f "$LAM_WORK/lam_cert_L.pkl" ] || "$WS_PY" -I $G/cert.py L > "$LAM_WORK/cert_L.log" || return 1
  "$WS_PY" -I $G/maj.py > "$LAM_WORK/maj.log" || return 1
}

# Lean emission into $LAM_WORK/emit, then installation under PlasmaLean/Design (renamed modules).
task_emit() {
  local G=scripts/gc_kam/lamcell
  export LAM_WORK="$WS_WORK/lambda-cell-${LAM_TAG}"
  rm -rf "$LAM_WORK/emit"
  "$WS_PY" -I $G/maj.py > "$LAM_WORK/maj.log" || return 1
  "$WS_PY" -I $G/emit.py > "$LAM_WORK/emit.log" || return 1
  "$WS_PY" -I $G/emit_kam.py > "$LAM_WORK/emit_kam.log" || return 1
  "$WS_PY" -I $G/install.py --force > "$LAM_WORK/install.log" || return 1
}
