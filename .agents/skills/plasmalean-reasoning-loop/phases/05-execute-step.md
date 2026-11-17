# Phase 3 (problem solving): Execute a step

Perform the next deduction of the current proof plan, and append it to
`<task>/04_execution_trace.md`.

1. **Justification.** State exactly which theorem, definition, hypothesis or earlier step
   justifies the move. When it is a project or Mathlib result, give its declaration name; when it
   is a project note that is not verified, say so and keep the step conditional.
2. **Example sanity check.** If the step introduces a new lemma, equality case, claimed
   equivalence or strengthened statement, test it against the examples in
   `<task>/02_examples.md`, or run `plasmalean-examples-counterexamples`.
3. **Recursion.** If the step needs its own strategy and deconstruction, label it `hard` and start
   a subtask in `<task>/subtasks/<slug>/` with the same layout, then resume here with its result.

In exploratory research, execute probes with `09-exploratory-probe.md` instead, unless the current
probe has become a precise theorem-proving subproblem.
