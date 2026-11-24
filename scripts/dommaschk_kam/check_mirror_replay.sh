#!/usr/bin/env bash
# Check independent packets, then their aggregate and the dependent geometry.
set -euo pipefail
cd "$(dirname "$0")/../.."

aggregate=PlasmaLean/Design/DommaschkActionQuadrature.lean
jobs=1
if (( $# > 0 )); then
    if [[ $# != 2 || $1 != --jobs || ! $2 =~ ^[1-9][0-9]?$ ]]; then
        echo "Usage: $0 [--jobs N]" >&2
        exit 2
    fi
    jobs=$2
fi
mapfile -t packets < <(awk '$1 == "public" && $2 == "import" &&
    $3 ~ /^PlasmaLean\.Design\.DommaschkAction/ {print $3}' "$aggregate")
if (( ${#packets[@]} == 0 )); then
    echo "No mirror packets found in $aggregate" >&2
    exit 1
fi

# All packet files import this same module. Build it once before starting them.
lake build --fail-fast PlasmaLean.Certificates.MirrorActionQuadrature
index=0
while (( index < ${#packets[@]} )); do
    width=$jobs
    if (( jobs > 1 )); then
        # The chunked pilot used 1.63 GiB. Allow 4 GiB per Lake/Lean pair
        # and leave 16 GiB for the desktop and other workstation users.
        available=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
        slots=$(( (available - 16 * 1024 * 1024) / (4 * 1024 * 1024) ))
        if (( slots < 1 )); then
            sleep 10
            continue
        fi
        if (( slots < width )); then width=$slots; fi
    fi
    pids=()
    for (( i=0; i<width && index<${#packets[@]}; ++i, ++index )); do
        module=${packets[index]}
        printf 'Checking %s\n' "$module"
        lake build --fail-fast "$module" &
        pids+=("$!")
    done
    failed=0
    for pid in "${pids[@]}"; do wait "$pid" || failed=1; done
    if (( failed )); then exit 1; fi
done

for module in \
    PlasmaLean.Design.DommaschkRadialSlabsS0H0 \
    PlasmaLean.Design.DommaschkRadialSlabsS0H1 \
    PlasmaLean.Design.DommaschkRadialSlabsS1H0 \
    PlasmaLean.Design.DommaschkRadialSlabsS1H1 \
    PlasmaLean.Design.DommaschkMirrorSectorFlow \
    PlasmaLean.Design.DommaschkLocalMirrorGraphs \
    PlasmaLean.Design.DommaschkActionQuadrature
do
    printf 'Checking %s\n' "$module"
    lake build --fail-fast "$module"
done
