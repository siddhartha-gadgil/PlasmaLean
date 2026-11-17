# Phase 1a: Problem deconstruction

Analyze the claim or research prompt and write `<task>/01_problem_formalization.md`.

1. **Components.** Extract the givens, hypotheses and goal. If the input is exploratory and has no
   fixed theorem to prove, write the best current research aim as the goal and mark it
   provisional.
2. **Definitions.** Define every term formally and resolve ambiguities. When a term already has a
   definition in the project kernel, in `PlasmaLean/` or in Mathlib, quote that definition with
   its declaration name, and record any mismatch with the informal statement.
3. **Intuition.** Give a three-sentence summary at undergraduate level.
4. **Objective classification.** Mark the input as `well_stated_problem`, `research_seed`,
   `extension_request` or `ambiguous`.
5. **Question seeds.** For exploratory inputs, list three to five precise questions or theorem
   candidates, without pretending they are already true.
6. **Example seeds.** List two to five natural examples, boundary cases or possible
   counterexample families suggested by the definitions. For a fixed theorem these are sanity
   checks, not evidence of proof.

For structured output, follow `../schemas/01-problem-formalization.json`.
