# Phase 3 (both modes): Metacognition and loop control

Analyze the current trace and decide what to do next. Append the analysis and the decision to
`<task>/log.md`.

1. Read the trace: `<task>/04_execution_trace.md` and the current subgoal in problem solving; or
   `<task>/04_research_trace.md`, `<task>/02_research_questions.md` and the current conjecture in
   exploratory research.
2. **Progress analysis.** Score viability from 1 to 10. Check for circular arguments, exploding
   algebra, or reliance on a claim that is neither proved in the trace nor verified in the
   project.
3. **Example review.** Check whether the examples support, fail to illuminate or refute the current
   plan. If no examples have been examined and the problem is not purely formal, consider an
   example check.
4. **Bottleneck.** If stuck, state the exact obstacle as a precise mathematical question.
5. **Decision in problem solving**, exactly one of:
   - `REFINE`: continue the current plan with minor adjustments;
   - `PIVOT`: abandon the current plan and switch to the next plan in the strategy artifact;
   - `EXAMPLE_CHECK`: run `plasmalean-examples-counterexamples` on a doubtful lemma, sharp hypothesis or
     possible counterexample;
   - `ABANDON`: all plans are exhausted; write `<task>/05_failure_report.md`.
6. **Decision in exploratory research**, exactly one of:
   - `PROBE`: run another example, counterexample, specialization or analogy probe;
   - `FORMULATE`: turn the evidence into a precise conjecture or question;
   - `STRESS_TEST`: test a conjecture against edge cases and weakened hypotheses;
   - `SOURCE_STUDY`: gather or revisit literature for the current obstacle;
   - `THEOREM_MODE`: a precise, plausible theorem has emerged; switch to problem solving;
   - `SYNTHESIZE`: enough has accumulated; write the research brief;
   - `ABANDON`: exploration is exhausted; write `<task>/05_research_obstacles.md`.
