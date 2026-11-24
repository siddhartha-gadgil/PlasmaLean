#!/usr/bin/env bash
# Check the heavy mirror packets one module at a time before importing the aggregate.
set -euo pipefail
cd "$(dirname "$0")/../.."

aggregate=PlasmaLean/Design/DommaschkActionQuadrature.lean
mapfile -t packets < <(awk '$1 == "public" && $2 == "import" &&
    $3 ~ /^PlasmaLean\.Design\.DommaschkAction/ {print $3}' "$aggregate")
if (( ${#packets[@]} == 0 )); then
    echo "No mirror packets found in $aggregate" >&2
    exit 1
fi

for module in "${packets[@]}" \
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
