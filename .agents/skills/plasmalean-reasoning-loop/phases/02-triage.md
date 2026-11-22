# Phase 1b: Inspection and triage

Decide whether to start proof strategy, study sources, or branch into exploratory research.

1. Review `<task>/01_problem_formalization.md`.
2. Assess the objective and its complexity:
   - Is there a precise claim with fixed hypotheses and a fixed goal?
   - Is the request instead to extend, generalize, formulate questions or look for conjectures?
   - Does it invoke advanced, specific machinery that needs source study?
   - Are there small, degenerate or boundary examples that could immediately refute or clarify
     the statement?
   - Is a needed prerequisite already a verified declaration in the project, or only a note?
3. Decide, and record the decision and reason in `<task>/log.md`:
   - `DIRECT_PROOF` if the hypotheses and goal use standard definitions that can be manipulated
     directly;
   - `SOURCE_STUDY` if the problem requires adapting a complex known theorem; suggest keywords or
     specific papers;
   - `EXPLORATORY_RESEARCH` if there is no fixed theorem to prove, or the user asks for
     extensions, questions, conjectures, examples or research directions.
4. **Auxiliary example check.** If the statement's truth is uncertain, hypotheses look sharp or
   definitions are ambiguous, run `plasmalean-examples-counterexamples` before strategy generation. This is
   an auxiliary action, not a separate triage decision.

**Regression rule.** If the input is an ordinary theorem or exercise with an explicit goal, do not
route to exploratory research merely because generalizations might be interesting.
