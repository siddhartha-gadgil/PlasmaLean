# High-resolution residual chain of the Dommaschk KAM certificate (N-33 plan item 7,
# notes/theory/dommaschk-kam-certificate.md and notes/theory/kamflow-g-status.md, "Item 7"): the
# initial invariance error of the 96 x 80 data torus C (Design/DommaschkKamCData, ...CTorus) for
# the field dkFieldTC on the strip r = 9/200, `dk_e0R` and `dk_e0Z` (e0q = 1.23e-27, oracle
# 5.9e-29, KAM needs <= 1.3e-23), as the on-demand top module Design/DommaschkKamCRes.
#
# A KronBall chain in the data box (layout 96 x 80, scale 2^-128, strip weights 68553^s 2^{16(K-s)}):
# R, s = R^2, z^2..z^5, LU/LZ (2^-Q Lt_{iota_q}), Horner in s of the R-form polynomials dDR, dnRh,
# dnZR (coefficient nodes without product + product nodes s H + Pc), norm nodes D LU - R G and
# D LZ - s F. Grids are salted packed rows with divide-and-conquer Kronecker images
# (Design/DommaschkKamCResKron). Generator: scripts/dommaschk_kam/emit_res.py (exact validation
# in Python; about 25 s). No numerics stage: the torus data are already in Design/DommaschkKamCData.
#
# The file is sourced by scripts/workstation/run.sh (bash 3.2 compatible). Only $WS_PY is used.
#
# Parameters (environment):
#   DRES_NCHECK   number of kernel-check modules (default 12; each holds 2-4 product nodes of about
#                 34 Mbit images, peak about 4.5-5 GB per process)
#   DRES_PARTIAL  1: build only the first data/environment/check modules and one equality check
#                 (a reduced pipeline test, about 3 CPU-min; the verdict then covers only those)
DRES_NCHECK="${DRES_NCHECK:-12}"
DRES_PARTIAL="${DRES_PARTIAL:-0}"

TASK_DESC="Dommaschk torus C residual chain (96 x 80, r = 9/200): dk_e0R, dk_e0Z (e0 = 1.23e-27)"

_dres_modules() {
  local P="PlasmaLean.Design.DommaschkKamCRes" k
  printf '%sKron ' "$P"
  for k in 1 2 3 4 5 6 7 8 9; do printf '%sData%d ' "$P" "$k"; done
  printf '%sEnv %sTrees ' "$P" "$P"
  if [ "$DRES_PARTIAL" = 1 ]; then
    printf '%sEqU %sCheck1' "$P" "$P"
    return
  fi
  printf '%sRel %sEqU %sEqZ ' "$P" "$P" "$P"
  for k in $(seq 1 "$DRES_NCHECK"); do printf '%sCheck%d ' "$P" "$k"; done
  printf '%sChain PlasmaLean.Design.DommaschkKamCRes' "$P"
}

# Lean modules, dependencies first (each built in its own process).
TASK_MODULES="$(_dres_modules)"

# Main theorems; #print axioms must show only propext, Classical.choice, Quot.sound.
if [ "$DRES_PARTIAL" = 1 ]; then
  TASK_ENTRYPOINTS="PlasmaLean.Design.DommaschkKamC.kronH PlasmaLean.Design.DommaschkKamC.eqH_U \
PlasmaLean.Design.DommaschkKamC.kH_s"
else
  TASK_ENTRYPOINTS="PlasmaLean.Design.DommaschkKamC.dk_e0R PlasmaLean.Design.DommaschkKamC.dk_e0Z \
PlasmaLean.Design.DommaschkKamC.ballH_all PlasmaLean.Design.DommaschkKamC.kron_gridR \
PlasmaLean.Design.DommaschkKamC.Bd_ctr_of_node PlasmaLean.Design.DommaschkKamC.e0q_not_tiny"
fi

# The generated Lean (the hand-written DommaschkKamCResKron is committed on main).
TASK_OUTPUTS="PlasmaLean/Design/DommaschkKamCResData*.lean PlasmaLean/Design/DommaschkKamCResEnv.lean \
PlasmaLean/Design/DommaschkKamCResTrees.lean PlasmaLean/Design/DommaschkKamCResRel.lean \
PlasmaLean/Design/DommaschkKamCResEq*.lean PlasmaLean/Design/DommaschkKamCResCheck*.lean \
PlasmaLean/Design/DommaschkKamCResChain.lean PlasmaLean/Design/DommaschkKamCRes.lean"
TASK_ARTIFACTS=""

# On-demand top module (not imported by PlasmaLean.lean).
TASK_TARGET="separate"

# No numerics: the data torus is Design/DommaschkKamCData (exported by the dommaschk-kam task).
task_numerics() {
  :
}

# Emit and validate (exact rationals, gmpy2 images) the chain modules.
task_emit() {
  "$WS_PY" -I scripts/dommaschk_kam/emit_res.py --emit --ncheck "$DRES_NCHECK" || return 1
}
