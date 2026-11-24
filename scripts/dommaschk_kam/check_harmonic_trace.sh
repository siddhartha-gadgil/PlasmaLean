#!/usr/bin/env bash
# Build the shared soundness proof first, then replay disjoint slab blocks.
set -euo pipefail
cd "$(dirname "$0")/../.."
jobs=${1:-4}
if [[ ! $jobs =~ ^[1-9][0-9]*$ ]]; then
    echo "Expected a positive number of parallel block builds" >&2
    exit 2
fi
lake build PlasmaLean.Certificates.TrajectoryHarmonicPacket
seq -w 0 48 | xargs -n1 -P "$jobs" bash -c 'lake build "PlasmaLean.Design.DommaschkHarmonicBlock$1"' _
lake build PlasmaLean.Design.DommaschkHarmonicTrace
