#!/usr/bin/env bash
# Fetch prebuilt dependency outputs so that `lake build` compiles only PlasmaLean:
#   1. Mathlib from the Mathlib cache (`lake exe cache get`);
#   2. TauCeti from TauCeti's public Lake cache (config: scripts/tauceti-cache.toml).
# Run from anywhere; it works in the repository root. Lake looks up the TauCeti revision pinned
# in lake-manifest.json for the toolchain in lean-toolchain. Right after a TauCeti or Lean bump
# the cache may not yet hold that revision (TauCeti's CI publishes it); Lake then searches back
# up to --max-revs earlier revisions, and on a miss `lake build` compiles TauCeti from source.
# Usage: scripts/get_cache.sh [--mappings-only]   (extra arguments go to `lake cache get`)
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
lake exe cache get
LAKE_CONFIG="$root/scripts/tauceti-cache.toml" lake cache get \
  --package=TauCeti --service=tauceti-public --repo=TauCetiProject/TauCeti "$@"
