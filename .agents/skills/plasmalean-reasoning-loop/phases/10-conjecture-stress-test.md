# Phase 3 (exploratory research): Conjecture stress test

Test a candidate conjecture or extension before treating it as a theorem. Append the result to
`<task>/04_research_trace.md`.

1. **State the candidate precisely**, with all hypotheses, definitions and the proposed conclusion.
2. **Boundary checks:** degenerate, small, low-dimensional, finite, singular, noncompact,
   noncommutative or non-Noetherian cases, as appropriate.
3. **Counterexample construction:** when a boundary case appears to fail, make the counterexample
   explicit with `plasmalean-examples-counterexamples`.
4. **Hypothesis stress-testing:** remove or weaken one hypothesis at a time and look for failure.
5. **Known-theorem alignment:** compare with known theorems and with the project's verified
   results. Decide whether the candidate is a corollary, strengthening, variant or likely false.
6. **Proof skeleton:** if it survives, outline the most plausible technique (see
   `plasmalean-proof-techniques`) and identify the hardest lemma.
7. **Classification:** `plausible`, `refuted`, `needs_extra_hypotheses`, `known_or_near_known` or
   `open`.

For structured output, follow `../schemas/10-conjecture-stress-test.json`.
