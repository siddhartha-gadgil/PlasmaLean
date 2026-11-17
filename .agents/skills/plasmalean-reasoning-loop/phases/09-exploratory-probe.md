# Phases 2 and 3 (exploratory research): Probes

Design concrete probes, then execute them to gather evidence for the research questions.

1. **Select a question** from `<task>/02_research_questions.md`.
2. **Pick a probe type** and a cost (`low_cost`, `medium_cost` or `high_cost`):
   - `example_search`: compute or construct representative examples;
   - `counterexample_search`: target boundary cases and weakened hypotheses;
   - `specialization`: simpler cases, lower dimension, finite or commutative cases;
   - `generalization`: alter hypotheses or conclusions;
   - `analogy`: compare with a nearby theorem or field;
   - `source_check`: look for known results or named techniques.
3. **Make the probe concrete:** the objects, parameters, computations, lemmas or sources to
   inspect. A computation may use the project's Python environment (`scripts/setup.sh --python`);
   save scripts and outputs in `<task>/computations/` and treat floating-point results as
   evidence to investigate, not as proof.
4. **Construct examples** for example and counterexample searches with `plasmalean-examples-counterexamples`;
   record explicit objects, not sketches.
5. **Record the evidence:** what the probe supports, refutes or leaves undecided.

Save the plan of probes to `<task>/03_exploration_plan.md` and append each probe's result to
`<task>/04_research_trace.md`. For structured output, follow
`../schemas/09-exploratory-probe.json`.
