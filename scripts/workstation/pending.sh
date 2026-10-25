#!/usr/bin/env bash
# List workstation result branches not yet merged into main and not yet recorded in
# workstation/REVIEWED.md, with the verdict of every task in each run. Read-only (apart from
# `git fetch`). Used by the plasmalean-workstation-update skill; see Workstation.md.
#
# usage: scripts/workstation/pending.sh [--all]   (--all: include branches already reviewed)

set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."

ALL=0; [ "${1:-}" = "--all" ] && ALL=1
git fetch --prune -q origin

found=0
for ref in $(git for-each-ref --format='%(refname:short)' 'refs/remotes/origin/workstation/' \
             | sort); do
  br="${ref#origin/}"
  if [ "$ALL" = 0 ]; then
    git merge-base --is-ancestor "$ref" origin/main && continue
    [ -f workstation/REVIEWED.md ] && grep -qF "\`$br\`" workstation/REVIEWED.md && continue
  fi
  found=1
  echo "== $br  ($(git log -1 --format='%cd' --date=iso "$ref"))"
  for s in $(git ls-tree -r --name-only "$ref" -- workstation/results | grep '/summary\.json$'); do
    # only the runs added by this branch, not results already on main
    git cat-file -e "origin/main:$s" 2>/dev/null && continue
    git show "$ref:$s" | python3 scripts/workstation/ws_helper.py show
  done
  echo "   files changed vs main:"
  git diff --stat origin/main..."$ref" -- . ':(exclude)workstation/results' | sed 's/^/     /'
done
[ "$found" = 1 ] || echo "no pending workstation runs"
