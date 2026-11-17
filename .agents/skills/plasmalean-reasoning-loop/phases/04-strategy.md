# Phase 2 (problem solving): Strategy generation

Formulate concrete, step-by-step proof plans by selecting and applying techniques. For exploratory
research use `09-exploratory-probe.md` instead, unless a precise theorem has been selected as the
current target.

1. **Analyze the formalization** in `<task>/01_problem_formalization.md`. If
   `<task>/02_examples.md` exists, use it to discard strategies already refuted by
   counterexamples.
2. **Select techniques** with `plasmalean-proof-techniques`: match the problem against its registry and read
   the matching `TECHNIQUE.md` files. Check also which verified declarations of the project and
   which Mathlib results can be used directly.
3. **Synthesize reasoning:**
   - forward reasoning: three to five deductions from the hypotheses;
   - backward reasoning: two or three conditions implying the goal;
   - simplification: two special cases;
   - example check: two or three examples or boundary cases that a plan must explain. If a
     counterexample appears valid, stop and recommend revising the statement instead of drafting
     a proof.
4. **Draft Plan A and Plan B**, incorporating the selected technique fragments. Label every step
   `easy`, `standard` or `hard`. A `hard` step will become a subtask.
5. Save to `<task>/03_strategy_plans.md`. See `04-strategy-examples.md` for the expected style.
