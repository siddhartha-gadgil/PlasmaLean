#!/usr/bin/env bash
# Make sure the PlasmaLean task server (`theory_server`) is running on 127.0.0.1:PORT.
#
# usage: scripts/theory_server/ensure_server.sh [PORT]      (default: $THEORY_SERVER_PORT or 8080)
#
# If the server already answers, report it and exit. Otherwise check that the built library is up
# to date, build the executable, start it in the background and wait until it answers (importing
# Mathlib and PlasmaLean takes about a minute), then exit. The log and the process id are kept in
# .lake/theory_server/. Exit status 0 means the server is ready. Linux, macOS or WSL.
# Stop the server with scripts/theory_server/stop_server.sh [PORT].
#
# Laptop budget (12 GB of Lean memory at a time): the running server holds about 9.3 GB resident,
# of which about 7 GB are memory-mapped .olean files and about 2 GB its own heap. Run it alone,
# or beside light modules only, and stop it before building heavy modules. The script never
# rebuilds the library: `lake build theory_server` builds only the task handlers, and a stale
# `PlasmaLean` must first be rebuilt by frontier (skill plasmalean-develop-theory, resource rules).
set -euo pipefail

PORT="${1:-${THEORY_SERVER_PORT:-8080}}"
TIMEOUT="${THEORY_SERVER_TIMEOUT:-600}"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
STATE="$ROOT/.lake/theory_server"
URL="http://127.0.0.1:$PORT/"
LOG="$STATE/server-$PORT.log"
PIDFILE="$STATE/server-$PORT.pid"

alive() { [ "$(curl -s -o /dev/null -w '%{http_code}' --max-time 5 "$URL" 2>/dev/null)" = 200 ]; }

if alive; then
  echo "theory_server ready at $URL"
  exit 0
fi

command -v lake >/dev/null 2>&1 || { [ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"; }
command -v lake >/dev/null 2>&1 || { echo "lake not found: set up Lean first (scripts/setup.sh)" >&2; exit 1; }

mkdir -p "$STATE"
cd "$ROOT"
# The server imports the built `PlasmaLean`; it must be up to date, or tasks see stale code (and a
# stale root module misses the task handlers). Never rebuild it here: one `lake build PlasmaLean`
# would start every stale module at once.
if ! lake build --no-build PlasmaLean > "$STATE/stale-check.log" 2>&1; then
  echo "PlasmaLean is not up to date; rebuild it by frontier first (lake build --no-build PlasmaLean" >&2
  echo "lists the frontier; build those modules within the laptop budget), then rerun this script." >&2
  grep -E "Building|out-of-date" "$STATE/stale-check.log" | head -20 >&2
  exit 1
fi
NEED_KB="${THEORY_SERVER_NEED_KB:-4000000}"
if [ -r /proc/meminfo ]; then
  avail=$(awk '/MemAvailable/ {print $2}' /proc/meminfo)
  if [ "$avail" -lt "$NEED_KB" ]; then
    echo "only $((avail / 1024)) MB available; the server needs about $((NEED_KB / 1024)) MB of heap" >&2
    echo "(plus reclaimable mapped files). Wait for builds to finish or stop other Lean jobs." >&2
    exit 1
  fi
fi
echo "building theory_server ..." >&2
lake build theory_server >&2
# Run the binary itself (not through `lake exe`), so that the recorded pid is the server's.
LEAN_PATH="$(lake env printenv LEAN_PATH)" nohup "$ROOT/.lake/build/bin/theory_server" "$PORT" \
  > "$LOG" 2>&1 &
echo $! > "$PIDFILE"
echo "starting theory_server on port $PORT (pid $(cat "$PIDFILE"), log $LOG) ..." >&2

start=$(date +%s)
until alive; do
  if ! kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    echo "theory_server exited before becoming ready; end of $LOG:" >&2
    tail -20 "$LOG" >&2
    exit 1
  fi
  if [ $(( $(date +%s) - start )) -ge "$TIMEOUT" ]; then
    echo "theory_server not ready after ${TIMEOUT}s; see $LOG" >&2
    exit 1
  fi
  sleep 2
done
echo "theory_server ready at $URL (pid $(cat "$PIDFILE"), log $LOG)"
