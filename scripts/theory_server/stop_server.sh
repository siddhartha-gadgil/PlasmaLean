#!/usr/bin/env bash
# Stop a theory_server started by ensure_server.sh.  usage: scripts/theory_server/stop_server.sh [PORT]
set -euo pipefail
PORT="${1:-${THEORY_SERVER_PORT:-8080}}"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
PIDFILE="$ROOT/.lake/theory_server/server-$PORT.pid"
if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
  kill "$(cat "$PIDFILE")" && rm -f "$PIDFILE" && echo "stopped theory_server on port $PORT"
else
  rm -f "$PIDFILE"
  echo "no theory_server started by ensure_server.sh is running on port $PORT"
fi
