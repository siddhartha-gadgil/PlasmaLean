---
name: plasmalean-evaluate-on-server
description: Evaluate Lean terms on the PlasmaLean task server, optionally after defining functions, without changing its environment (task `eval`). Use to compute values of library or candidate functions, to score candidates in an evolutionary search, and to test definitions on examples.
---

# Evaluate terms on the task server

1. Make sure the server is running with `plasmalean-ensure-theory-server`.
2. Evaluate a term, optionally after elaborating code that defines what it uses:

   ```bash
   python3 scripts/theory_server/task.py eval --term 'PlasmaLean.Transport.svFloorF 10'
   python3 scripts/theory_server/task.py eval --code-file Candidate.lean --term '(List.range 12).map fib'
   ```

The script sends `{"task": "eval", "code": …, "term": …, "modify_env": false}`. The server
elaborates the code, and if it has no errors evaluates the term in the resulting environment and
returns its `repr`. Afterwards the environment is as before: neither the code's definitions nor
anything added while evaluating the term are kept, so each candidate is evaluated from the same
starting point. Pass `--keep` only when later requests should see the code's definitions.

## Reading the result

- On success: `"result": "ok"`, the value as a string in `output`, and the code's `messages`
  (for example warnings). Exit status 0.
- If the code has errors: `"result": "error"` with the `messages` (severity, line, column and
  text in the submitted code), and nothing is evaluated. Exit status 1.
- If the term cannot be evaluated: `"result": "error"` and an `error` text. Common causes are an
  unknown identifier, a type with no `Repr` instance, or a `noncomputable` definition (such as
  most functions on `ℝ`); evaluate a computable version, for example over `ℚ`. Exit status 1.

## In an evolutionary search

Score each candidate with one or more `eval` requests, after a `plasmalean-check-compilation` request when
compiling and scoring should be reported separately. Keep scoring terms small and deterministic.
There is no time limit on evaluation yet, so avoid terms that may not terminate (for example
unbounded recursion through `partial` functions), and record the request and response of every
scored candidate in the task folder of the search.
