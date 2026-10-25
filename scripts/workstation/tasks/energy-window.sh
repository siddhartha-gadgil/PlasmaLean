# Energy window of passing alpha guiding centres: a genuine (energy x pitch angle) family of exact
# KAM tori over |rho - 1/256| <= 2^-32 (E = 3.5 MeV +- 0.4 eV at the design B0R0), lambda in [0, 1/16].
# Four node pipelines (lambda-families at rho_j = 1/256 + t_j 2^-32, t_j = -1, -5/16, 5/16, 1),
# kernel-checked combination norms, and interpolation in rho with an analytic (Cauchy) remainder.
# See notes/theory/gc-kam-status.md, section 9.
#
# The file is sourced by scripts/workstation/run.sh (bash 3.2 compatible).
#
# EW_DELTA: half-width of the energy window in eV. The certificate is built for EW_DELTA = 0.4
# (gyro-length half-width 2^-32, the largest dyadic width whose family stays inside the admissibility
# balls, radius 1.18e-8, of the certified low-resolution chain Design/RationalStellaratorGCMu*L).
# Wider windows (+-3 eV, +-1%) need two further steps that are NOT automated here: (i) re-run the
# low-resolution chain with enlarged balls (scripts/gc_kam/ew_cert.py L with EW_EIN_ADD) and emit
# new L modules, (ii) regenerate the window constants (scripts/gc_kam/ew_const.py; the static
# modules RationalStellaratorGCEw{Interp,Adm,Maj,Const}.lean hard-code hEw = 2^-32 and cE).
# The numerics refuse other values instead of producing a certificate that cannot build.
EW_DELTA="${EW_DELTA:-0.4}"

TASK_DESC="energy window E = 3.5 MeV +- ${EW_DELTA} eV x pitch cell [0, 1/16]: confinement of passing alpha GCs"

_ew_node_modules() {
  local j k
  for j in 1 2 3 4; do
    for k in 1 2 3 4 5 6; do printf 'PlasmaLean.Design.RationalStellaratorGCEw%dDataH%d ' "$j" "$k"; done
    printf 'PlasmaLean.Design.RationalStellaratorGCEw%dKvH ' "$j"
    printf 'PlasmaLean.Design.RationalStellaratorGCEw%dTreesH ' "$j"
    printf 'PlasmaLean.Design.RationalStellaratorGCEw%dEnvH ' "$j"
    printf 'PlasmaLean.Design.RationalStellaratorGCEw%dRelH ' "$j"
    for k in $(ls PlasmaLean/Design/RationalStellaratorGCEw${j}CheckH*.lean 2>/dev/null \
        | sed 's/.*CheckH\([0-9]*\)\.lean/\1/' | sort -n); do
      printf 'PlasmaLean.Design.RationalStellaratorGCEw%dCheckH%d ' "$j" "$k"
    done
    printf 'PlasmaLean.Design.RationalStellaratorGCEw%dChainH ' "$j"
    printf 'PlasmaLean.Design.RationalStellaratorGCEw%dOutH ' "$j"
  done
}

_ew_comb_checks() {
  local k
  for k in $(ls PlasmaLean/Design/RationalStellaratorGCEwCombCheck*.lean 2>/dev/null \
      | sed 's/.*CombCheck\([0-9]*\)\.lean/\1/' | sort -n); do
    printf 'PlasmaLean.Design.RationalStellaratorGCEwCombCheck%d ' "$k"
  done
}

# Lean modules, dependencies first (each built in its own process). Measured on the laptop: about
# 70 CPU-min in total; the node kernel checks (RationalStellaratorGCEw<j>CheckH*) peak at 5-8.8 GB
# (36 of 272 above 6 GB, as do the existing RationalStellaratorGCMuCheckH* at 6.9 GB), the rest <= 3 GB.
TASK_MODULES="PlasmaLean.Theory.KAM.ParamInterp \
PlasmaLean.Design.RationalStellaratorGCEwInterp \
PlasmaLean.Design.RationalStellaratorGCEwAdm \
PlasmaLean.Design.RationalStellaratorGCEwMaj \
PlasmaLean.Design.RationalStellaratorGCEwConst \
$(_ew_node_modules) \
PlasmaLean.Design.RationalStellaratorGCEwNodes \
PlasmaLean.Design.RationalStellaratorGCEwCombEnv \
$(_ew_comb_checks) \
PlasmaLean.Design.RationalStellaratorGCEwComb \
PlasmaLean.Design.RationalStellaratorGCEwDisc \
PlasmaLean.Design.RationalStellaratorGCEwRes \
PlasmaLean.Design.RationalStellaratorGCEwExact \
PlasmaLean.Design.RationalStellaratorGCEwForever \
PlasmaLean.Design.RationalStellaratorGCEwConfined \
PlasmaLean.Design.RationalStellaratorGCEwFamily"

TASK_ENTRYPOINTS="PlasmaLean.Design.RationalStellaratorGC.alpha_gc_confined_forever_energy_window \
PlasmaLean.Design.RationalStellaratorGC.alpha_gc_ew_confined_forever_velocity_set \
PlasmaLean.Design.RationalStellaratorGC.alphaEwVel_volume_pos \
PlasmaLean.Design.RationalStellaratorGC.ew_family_torus \
PlasmaLean.Theory.KAM.Bd_interp"

# Generated Lean files (the hand-written window modules are on main already).
TASK_OUTPUTS="PlasmaLean/Design/RationalStellaratorGCEw[1-4]*.lean \
PlasmaLean/Design/RationalStellaratorGCEwNodes.lean \
PlasmaLean/Design/RationalStellaratorGCEwComb*.lean \
PlasmaLean/Design/RationalStellaratorGCEwDisc.lean \
PlasmaLean/Design/RationalStellaratorGCEwRes.lean \
PlasmaLean/Design/RationalStellaratorGCEwExact.lean"

TASK_ARTIFACTS=""

# about 70 CPU-min of Lean and peaks above 6 GB: on-demand top module `lake build PlasmaLean.Design.RationalStellaratorGCEwFamily`
TASK_TARGET="separate"

_EW_NODES="1:16777215/4294967296:-1 2:268435451/68719476736:-5/16 3:268435461/68719476736:5/16 4:16777217/4294967296:1"

# Untrusted numerics (restartable: finished steps are skipped).
task_numerics() {
  if [ "$EW_DELTA" != "0.4" ]; then
    echo "energy-window: EW_DELTA=$EW_DELTA is not supported by this pipeline (see the header)" >&2
    return 1
  fi
  local W="$WS_WORK/energy-window" G=scripts/gc_kam e j R k
  mkdir -p "$W"
  export LAM_DEN=32
  # 1. the certified family torus (initial guess) and the certified low-resolution pipeline
  [ -f "$W/chebH0.npz" ] || "$WS_PY" -I $G/ew_decode_h.py "$W/chebH0.npz"
  if [ ! -f "$W/L0/lam_cert_L.pkl" ]; then
    mkdir -p "$W/L0"
    LAM_LD=5 LAM_LDC=5 EW_OUT="$W/L0" "$WS_PY" -I $G/ew_cert.py L > "$W/L0/log.txt"
  fi
  # 2. the lambda-family tori at the four nodes (16 Chebyshev nodes in lambda each)
  for e in $_EW_NODES; do
    j=${e%%:*}; R=$(echo "$e" | cut -d: -f2)
    mkdir -p "$W/tori_$j"
    for k in $(seq 0 15); do
      [ -f "$W/tori_$j/t_28_20_16_$k.npz" ] || echo "$j $k $R"
    done
  done | xargs -P "$WS_JOBS" -L 1 sh -c \
    'EW_INIT="'"$W"'/chebH0.npz" EW_RHO=$2 LAM_TORI_DIR="'"$W"'/tori_$0" "'"$WS_PY"'" -I scripts/gc_kam/ew_tori.py 28 20 16 $1 1 16 > "'"$W"'/tori_$0/log_$1.txt"'
  # 3. node grids and the four high-resolution node pipelines (sequential: ~8 GB each)
  for e in $_EW_NODES; do
    j=${e%%:*}; R=$(echo "$e" | cut -d: -f2)
    [ -f "$W/hdata_$j.pkl" ] || "$WS_PY" -I $G/ew_hdata.py "$W/tori_$j" "$W/hdata_$j.pkl"
    if [ ! -f "$W/H$j/lam_cert_H.pkl" ]; then
      mkdir -p "$W/H$j"
      LAM_H=36,27,107,12 EW_RHO="$R" EW_HDATA="$W/hdata_$j.pkl" EW_OUT="$W/H$j" \
        "$WS_PY" -I $G/ew_cert.py H > "$W/H$j/log.txt"
    fi
  done
}

# Lean emission: node pipelines (renamed per node), node residuals, combination norms, glue.
task_emit() {
  local W="$WS_WORK/energy-window" G=scripts/gc_kam e j R
  export LAM_DEN=32
  for e in $_EW_NODES; do
    j=${e%%:*}; R=$(echo "$e" | cut -d: -f2)
    rm -rf "$W/emit$j"
    LAM_PKL_H="$W/H$j/lam_cert_H.pkl" LAM_PKL_L="$W/L0/lam_cert_L.pkl" EW_RHO="$R" EW_TMP="$W/emit$j" \
      LAM_GH=68 LAM_HCAP=1 "$WS_PY" -I $G/ew_emit_lean.py all > "$W/emit$j.log"
    "$WS_PY" -I $G/ew_rename.py "$W/emit$j" "$j" "1/256 + ($(echo "$e" | cut -d: -f3)) 2⁻³²"
  done
  "$WS_PY" -I $G/ew_nodes.py
  EW_COMB_OUT="$W" "$WS_PY" -I $G/ew_comb.py "$W/H1/lam_cert_H.pkl" "$W/H2/lam_cert_H.pkl" \
    "$W/H3/lam_cert_H.pkl" "$W/H4/lam_cert_H.pkl"
  EW_GLUE_PKL="$W/glue.pkl" EW_NEAR_PKL="$W/near.pkl" "$WS_PY" -I $G/ew_glue.py \
    "$W/H1/lam_cert_H.pkl" "$W/H2/lam_cert_H.pkl" "$W/H3/lam_cert_H.pkl" "$W/H4/lam_cert_H.pkl" \
    "$W/comb_recs.pkl"
}
