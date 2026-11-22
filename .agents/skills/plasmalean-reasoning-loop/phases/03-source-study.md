# Phase 1c: Source study

Dissect the relevant literature to extract techniques, reusable lemmas, limitations and possible
extensions. Write the findings to `<task>/02_literature_review.md`.

Read the actual source, not only an abstract, and record authors, title, identifier, version and
theorem or equation locators. For each proof or theorem used:

1. **Structural mapping.** Map which hypothesis justifies which line of the proof.
2. **Hypothesis stress-testing.** Identify what breaks if a key hypothesis is dropped.
3. **Generalization.** Ask whether hypotheses can be weakened, for example from compact to
   locally compact.
4. **Core idea.** Distill the central trick into one to three sentences.
5. **Examples and counterexamples.** Extract the source's examples, counterexamples, sharpness
   examples and boundary cases, and record which hypothesis each one tests.
6. **Research leads.** In exploratory mode, list plausible extensions, sharpness questions,
   examples to compute and nearby open questions. Label speculative leads as speculative.

Sources studied here belong to this task. To integrate a source into the project's notes for
later work, use `plasmalean-update-notes-from` after the loop; it applies this same method to the sources it
is given. For structured output, follow
`../schemas/03-source-study.json`.
