---
name: plasmalean-check-compilation
description: Check whether Lean code compiles, quickly and without changing anything, by sending it to the PlasmaLean task server (task `check`, with the environment left unmodified). Use for candidate definitions or proofs in an evolutionary search, for quick checks of snippets against Mathlib and the PlasmaLean library, and whenever many small pieces of code must be checked in turn.
---

# Check that code compiles on the task server

1. Make sure the server is running with `plasmalean-ensure-theory-server`.
2. Write the candidate code to a file (it may be a scratch file, for example in a task folder
   under `notes/reasoning/`), then run:

   ```bash
   python3 scripts/theory_server/task.py check --code-file path/to/Candidate.lean
   ```

   Use `--code '…'` for a one-line snippet and `--code-file -` to read standard input. The script
   needs only the Python standard library and builds the JSON itself, so code needs no escaping.
   Pass `--port` if the server is not on 8080.

The script sends `{"task": "check", "code": …, "modify_env": false}`: the code is elaborated in the
server's environment (Mathlib and PlasmaLean, plus anything a previous request kept), and the
environment is left unchanged, so candidates do not interfere with each other and the same
declaration names can be reused. Do not pass `--keep` in a search; use it only when later requests
should see the definitions.

## Reading the result

The response has `compiles`, `errors`, `declarations`, `sorry` and `messages`. The exit status is
0 when the code compiles and 1 when it does not (2 if the server could not be reached).

- `compiles` is true when there are no errors and no declaration uses `sorry`. A warning such as
  an unused variable does not make it false.
- `declarations` lists the new declarations, without auxiliary ones such as `f.match_1`; `sorry`
  lists those whose type or value uses `sorry` (including the error-recovery `sorry` of a
  declaration that failed).
- Each message has `severity` (`error`, `warning` or `info`), `line` and `column` in the submitted
  code, and `text`. Feed error messages back into the next candidate.

The code is checked by elaborating it with Lean's frontend, in the server's environment, after a
fixed prefix (`defaultTop` in `PlasmaLean/Elaborate.lean`) that sets a high `maxHeartbeats`. It does
not replace a library build: before a result counts as verified in the project, put it in a module
and build it, following `plasmalean-lean-proofs` and the project policies (for example, no `decide`).
For a single draft file, `lake env lean <file>` is the alternative when the server is not running;
the server pays off when many candidates are checked in turn, since it imports the library once.
