# Phase 16 migration of on-demand KAM families to explicit proof terms: the low-memory kernel
# checks (`decide +kernel` on node3KS/norm3KS/center3KS and the l1 checks) become certificates
# built by `kron_proof`/`kron_lt` (Certificates/KronProof), and the side conditions of the bridges
# `<PRE>LowMem<T>` and chains `<PRE>Chain<T>` become `kernel_fact` proof terms
# (Certificates/KernelFact). Statements are unchanged, so nothing downstream is edited; the
# family's modules are rebuilt up to its top theorem module. Emitter:
# scripts/gc_kam/proofterm/proofterm_emit.py. No numerics.
#
# The file is sourced by scripts/workstation/run.sh (bash 3.2 compatible).
#
# Parameters (environment):
#   PT_FAMILIES  space-separated family prefixes (required), for example
#                "RationalStellaratorGCEw1 RationalStellaratorGCEw2 RationalStellaratorGCEw3
#                 RationalStellaratorGCEw4" (top module RationalStellaratorGCEwFamily),
#                "RationalStellaratorGCMu2" (RationalStellaratorGCMuWide),
#                "RationalStellaratorGCMu3" (RationalStellaratorGCMu3Confined).
#                Every family must be in the low-memory format (lowmem_emit.py) and not migrated.
#
# Cost (laptop, Mu and Fam): about 1.15-1.45x the CPU of the low-memory checks, the same peak
# (about 4.3 GB), oleans +25 KB per node/centre check.
PT_FAMILIES="${PT_FAMILIES:-}"
export PT_FAMILIES

TASK_DESC="proof-term migration (no decide +kernel) of the families: ${PT_FAMILIES:-<PT_FAMILIES unset>}"

_pt_plan() { python3 scripts/gc_kam/proofterm/proofterm_emit.py --plan "$1" $PT_FAMILIES; }

if [ -n "$PT_FAMILIES" ]; then
  # Lean modules, dependencies first (KronProof, KernelFact; per family KvS, checks, LowMem,
  # Chain, and every module up to the top theorem module that imports them).
  TASK_MODULES="$(_pt_plan modules)"
  TASK_ENTRYPOINTS="$(_pt_plan entrypoints)"
  TASK_OUTPUTS="$(_pt_plan outputs)"
fi

TASK_ARTIFACTS=""

TASK_TARGET="separate"  # on-demand top modules

task_numerics() { :; }

# The families' check, bridge and chain files, as a list of paths.
_pt_files() { _pt_plan outputs; }

task_emit() {
  [ -n "$PT_FAMILIES" ] || { echo "PT_FAMILIES is not set" >&2; return 1; }
  local f p t tags
  # refuse anything already migrated or not in the low-memory format
  for f in $(_pt_files); do
    [ -f "$f" ] || { echo "missing $f" >&2; return 1; }
    if grep -q 'kron_proof\|kron_lt\|kernel_fact' "$f"; then
      echo "already (partly) migrated: $f" >&2; return 1
    fi
    case "$f" in
      *Check[HL][0-9]*.lean)
        grep -q 'KronLowMem' "$f" || { echo "not in the low-memory format: $f" >&2; return 1; } ;;
    esac
  done
  for p in $PT_FAMILIES; do
    tags="$(python3 scripts/gc_kam/proofterm/proofterm_emit.py --plan tags "$p" | cut -d: -f2)"
    [ -n "$tags" ] || { echo "no check modules for $p" >&2; return 1; }
    for t in $(echo "$tags" | sed 's/./& /g'); do
      python3 scripts/gc_kam/proofterm/proofterm_emit.py "$p" "$t" --inplace || return 1
    done
  done
  # no decide +kernel may remain in the rewritten files
  if grep -l 'decide +kernel' $(_pt_files); then
    echo "decide +kernel remains in the files above" >&2; return 1
  fi
}
