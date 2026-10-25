# Workstation task: family-2 ideal-ballooning surface certificates (UNTRUSTED numerics + data).
# Sourced by scripts/workstation/run.sh (bash 3.2 compatible); uses only WS_PY, WS_WORK, WS_JOBS.
#
# STATUS (25 Oct 2026): the kernel checker that would link the emitted data to the reduction
# `LandremanFamily2BallooningSecular.family2_stable_of_secular_cert` is NOT implemented yet.
# A run therefore produces (1) the untrusted certificate search on F2B_NK surfaces of the band
# [F2B_KLO, F2B_KHI] (scripts/family2_ballooning_cert/search.py, JSON in $WS_WORK) and (2) Lean
# DATA modules LandremanFamily2BallooningData*.lean (coefficients only, no claim), and builds
# them together with the reduction module.  No ballooning-stability theorem is produced.
#
# Environment (all optional):
#   F2B_KLO, F2B_KHI   band ends (default 0.70, 0.90)
#   F2B_NK             number of surfaces (default 9)
#   F2B_RES            "full" (default: NT=128, NZ=16, widths 1,8 / 1e-3,1e-2, 12 active-set
#                      rounds, <= 2e8 nonzeros per SOCP, ~40-60 GB per surface) or "small"
#                      (laptop smoke test: NT=32, NZ=4, 1 round)
#   F2B_MAXNNZ         override the per-solve nonzero cap (memory ~ 150-250 bytes per nonzero)
#   F2B_EMIT_DIR       where task_emit writes the Lean data modules (default PlasmaLean/Design)
# Python packages: clarabel (listed in scripts/requirements.txt; cvxpy is NOT needed).

F2B_KLO="${F2B_KLO:-0.70}"
F2B_KHI="${F2B_KHI:-0.90}"
F2B_NK="${F2B_NK:-9}"
F2B_RES="${F2B_RES:-full}"
F2B_EMIT_DIR="${F2B_EMIT_DIR:-PlasmaLean/Design}"

TASK_DESC="family-2 ballooning: certificate search on $F2B_NK surfaces of k in [$F2B_KLO, $F2B_KHI] and Lean data modules (checker not yet implemented)"

# The data modules are emitted under predictable names: per surface one chunk
# LandremanFamily2BallooningDatak<1000 k>C0 (both resolutions have nf*NT*NZ <= 18432 < 20000
# coefficients, emit.py's chunk size) and one header LandremanFamily2BallooningDatak<1000 k>.
# TASK_MODULES is computed when this file is sourced (run.sh runs task_emit in a subshell).
_f2b_tags() {
  "$WS_PY" -c "
import numpy as np
n=int('$F2B_NK'); ks=np.linspace(float('$F2B_KLO'),float('$F2B_KHI'),n) if n>1 else [float('$F2B_KLO')]
print(' '.join('k%04d'%int(round(k*1000)) for k in ks))"
}
_f2b_modules() {
  for t in $(_f2b_tags); do
    echo "PlasmaLean.Design.LandremanFamily2BallooningData${t}C0"
    echo "PlasmaLean.Design.LandremanFamily2BallooningData${t}"
  done
}

TASK_MODULES="$(_f2b_modules | tr '\n' ' ')PlasmaLean.Design.LandremanFamily2BallooningSecular"
TASK_ENTRYPOINTS="PlasmaLean.Design.LandremanFamily2BallooningSecular.family2_stable_of_secular_cert"
TASK_OUTPUTS="PlasmaLean/Design/LandremanFamily2BallooningData*.lean"
TASK_ARTIFACTS=""
TASK_TARGET="separate"

_f2b_opts() {
  if [ "$F2B_RES" = "small" ]; then
    echo "--NT 32 --NZ 4 --rounds 1 --fine 0.5 --max_nnz ${F2B_MAXNNZ:-5e6}"
  else
    echo "--NT 128 --NZ 16 --epsm 0.15 --sig 1,8 --sigabs 1e-3,1e-2 --rounds 12 --add 20000 --fine 2 --max_nnz ${F2B_MAXNNZ:-2e8}"
  fi
}

# Untrusted numerics (restartable: surfaces whose JSON exists are skipped).
task_numerics() {
  mkdir -p "$WS_WORK/family2-ballooning"
  "$WS_PY" -I scripts/family2_ballooning_cert/search.py band "$F2B_KLO" "$F2B_KHI" "$F2B_NK" \
    --outdir "$WS_WORK/family2-ballooning" --jobs "$WS_JOBS" $(_f2b_opts)
}

# Lean data modules from the certificate JSON files of this band.
task_emit() {
  mkdir -p "$F2B_EMIT_DIR"
  files=$("$WS_PY" -c "
import numpy as np
n=int('$F2B_NK'); ks=np.linspace(float('$F2B_KLO'),float('$F2B_KHI'),n) if n>1 else [float('$F2B_KLO')]
print(' '.join('$WS_WORK/family2-ballooning/cert_k%.4f.json'%k for k in ks))")
  "$WS_PY" -I scripts/family2_ballooning_cert/emit.py $files --outdir "$F2B_EMIT_DIR"
}
