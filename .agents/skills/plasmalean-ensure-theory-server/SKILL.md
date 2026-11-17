---
name: plasmalean-ensure-theory-server
description: Make sure the PlasmaLean task server (`theory_server`) is running, starting it and waiting until it is ready if it is not. Use before any request to the server, in particular before `plasmalean-check-compilation`, `plasmalean-evaluate-on-server` or an evolutionary search loop, and when the user asks to start the server or whether it is alive.
---

# Ensure the task server is running

The task server answers JSON tasks over HTTP on `127.0.0.1` with Mathlib and the PlasmaLean library
loaded (`theory_server.lean`). Importing them takes about a minute, so the server is started once
and then reused for many requests.

Run, from the repository root:

```bash
scripts/theory_server/ensure_server.sh
```

- If the server already answers `GET /` on the port, the script reports it and exits at once.
- Otherwise it checks that the built `PlasmaLean` is up to date (`lake build --no-build
  PlasmaLean`) and that enough memory is free, builds `theory_server` (only the task-handler
  modules, never the library), starts it in the background, waits until it answers, and exits.
  If the library is stale it stops and lists the stale modules: rebuild them by frontier within
  the laptop budget (`plasmalean-develop-theory`, resource rules), then run it again. It fails with the end of the server log if the server exits early or is not ready in
  time (`THEORY_SERVER_TIMEOUT`, default 600 seconds).
- The port is the first argument, else `THEORY_SERVER_PORT`, else 8080. Use the same port for all
  later requests.
- The log and process id are in `.lake/theory_server/server-<port>.log` and `.pid`. Stop the
  server with `scripts/theory_server/stop_server.sh [PORT]`, for example after a long search or
  before rebuilding the library.

Return only after the script exits with status 0; report a failure with the log excerpt instead
of sending requests.

Notes:

- **Memory.** The running server holds about 9.3 GB resident (measured 17 November 2026): about
  7 GB of memory-mapped `.olean` files, which the system can reclaim, and about 2 GB of its own
  heap. Count it against the laptop budget of 12 GB of Lean memory at a time: while it runs, build
  at most one or two light modules beside it, and stop it before building a heavy module or
  checking `scripts/check_axioms.lean`. Long searches belong on the workstation
  (`Workstation.md`), where the same script works.

- The script needs Lean (run the `start` setup first if `lake` is missing) and runs on Linux,
  macOS or WSL.
- A running server keeps the library it was started with. After changing or adding library
  modules, stop it, rebuild, and ensure it again, or requests will not see the changes.
- The server shares one environment between requests and runs them one at a time. Tasks can run
  arbitrary Lean code, including `#eval` of `IO` actions, which is why it listens only on
  `127.0.0.1`.
