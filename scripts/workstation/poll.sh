#!/usr/bin/env bash
# Unattended workstation runner. Every 10 minutes, if the workstation is idle, pull `main` and run
# scripts/workstation/next.sh once per new NEXT_ID. The laptop writes next.sh after every review
# ("update from workstation"), alongside "Next Commands" in Workstation.md. See Workstation.md,
# "Unattended polling".
#
# usage (inside tmux, from the clone):  scripts/workstation/poll.sh [--interval SECONDS] [--once]
#
# - Idle means: no `scripts/workstation/run.sh` and no `lake` process is running.
# - next.sh runs at most once per NEXT_ID, success or failure; a failed batch is not retried. To
#   retry, the laptop issues a new NEXT_ID. Logs: $WS_WORK/poll/<NEXT_ID>.log.
# - Status: on start and end of every batch, a one-file commit (status.txt) is pushed to the
#   branch `ws-status` with git plumbing. The working tree is not touched. On the laptop:
#   `git fetch origin ws-status && git show origin/ws-status:status.txt`
#   (scripts/workstation/pending.sh prints it).
# - Updates: when a pull changes this script, it re-executes the new version.
# - Trust: next.sh comes from `main` of this repository and is executed as is.

main() {
  set -uo pipefail
  local repo interval once
  repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
  interval=600; once=0
  while [ $# -gt 0 ]; do
    case "$1" in
      --interval) interval="$2"; shift 2 ;;
      --once) once=1; shift ;;
      -h|--help) sed -n '2,20p' "$repo/scripts/workstation/poll.sh"; return 0 ;;
      *) echo "unknown option $1" >&2; return 2 ;;
    esac
  done
  cd "$repo" || return 1
  local work="${WS_WORK:-$HOME/plasmalean-work}"
  local state="$work/poll"
  mkdir -p "$state"
  local self="scripts/workstation/poll.sh"
  local selfhash; selfhash="$(git hash-object "$self")"
  log() { echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" | tee -a "$state/poll.log"; }
  log "poller started (pid $$, interval ${interval}s, host $(hostname))"

  while true; do
    if pgrep -f 'scripts/workstation/run\.sh' >/dev/null || pgrep -x lake >/dev/null; then
      log "busy (run.sh or lake running); next check in ${interval}s"
    elif [ -n "$(git status --porcelain --untracked-files=no)" ]; then
      log "tracked files modified in the clone; not pulling (fix by hand)"
    else
      git checkout -q main 2>/dev/null
      if ! git pull -q --ff-only 2>>"$state/poll.log"; then
        log "git pull failed (connection?); retrying later"
      else
        if [ "$(git hash-object "$self")" != "$selfhash" ]; then
          log "poll.sh changed on main; re-executing the new version"
          exec bash "$self" --interval "$interval" $([ "$once" = 1 ] && echo --once)
        fi
        local id; id="$(sed -n 's/^NEXT_ID="\(.*\)"$/\1/p' scripts/workstation/next.sh 2>/dev/null | head -1)"
        if [ -z "$id" ]; then
          log "no NEXT_ID in scripts/workstation/next.sh"
        elif [ -f "$state/done-$id" ]; then
          log "nothing new (last batch $id: $(cat "$state/done-$id"))"
        else
          log "running batch $id"
          push_status "$id" "running" ""
          local t0 rc; t0=$(date +%s)
          bash scripts/workstation/next.sh >"$state/$id.log" 2>&1; rc=$?
          local mins=$(( ($(date +%s) - t0) / 60 ))
          echo "exit $rc after ${mins} min, $(date '+%Y-%m-%d %H:%M')" >"$state/done-$id"
          log "batch $id finished: exit $rc after ${mins} min (log $state/$id.log)"
          git checkout -q main 2>/dev/null
          push_status "$id" "finished, exit $rc after ${mins} min" "$state/$id.log"
        fi
      fi
    fi
    [ "$once" = 1 ] && return 0
    sleep "$interval"
  done
}

# Push status.txt as a new commit on branch ws-status without touching the working tree.
push_status() {
  local id="$1" what="$2" logf="$3" tmp blob tree parent commit
  tmp="$(mktemp)"
  {
    echo "host: $(hostname)"
    echo "time: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "main: $(git rev-parse --short HEAD)"
    echo "batch: $id"
    echo "state: $what"
    if [ -n "$logf" ] && [ -f "$logf" ]; then echo "--- last 40 lines of the batch log ---"; tail -40 "$logf"; fi
  } >"$tmp"
  blob="$(git hash-object -w "$tmp")"; rm -f "$tmp"
  tree="$(printf '100644 blob %s\tstatus.txt\n' "$blob" | git mktree)"
  git fetch -q origin ws-status 2>/dev/null
  if parent="$(git rev-parse -q --verify FETCH_HEAD 2>/dev/null)" && \
     git cat-file -e "$parent:status.txt" 2>/dev/null; then
    commit="$(echo "ws-status: $id $what" | git commit-tree "$tree" -p "$parent")"
  else
    commit="$(echo "ws-status: $id $what" | git commit-tree "$tree")"
  fi
  git push -q origin "$commit:refs/heads/ws-status" 2>/dev/null || echo "(status push failed)"
}

main "$@"; exit $?
