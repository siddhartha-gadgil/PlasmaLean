---
name: plasmalean-examples-counterexamples
description: Construct examples, boundary cases and counterexamples that clarify definitions, test whether a statement or conjecture is true, show which hypotheses are needed, or guide a proof. Use inside `plasmalean-reasoning-loop`, for requests such as "find a counterexample to ...", "test this conjecture" or "is this hypothesis needed?", and when designing the sanity triad for a kernel law.
---

# Construct examples and counterexamples

Examples are evidence and diagnostic tools. They do not prove a universal claim unless the domain
has been reduced to a finite exhaustive list and the exhaustion is explicitly justified.

## Where the output goes

Inside a reasoning loop, write early examples to `<task>/02_examples.md`, and append later ones to
`<task>/04_execution_trace.md` or `<task>/04_research_trace.md`. When invoked on its own, create a
task folder `notes/reasoning/<YYYY-MM-DD>-<slug>/` with a `README.md` task card and write
`02_examples.md` there, as described in `plasmalean-reasoning-loop`. For structured output, follow
`schema.json` in this folder.

## Method

1. **Classify the target:** theorem sanity check, conjecture testing, hypothesis necessity,
   boundary or degenerate case, model for a definition, or counterexample search.
2. **Extract constraints:** the hypotheses an example must satisfy and the conclusion or behaviour
   to test, using the project's or Mathlib's exact definitions when they exist.
3. **Choose construction families:**
   - small finite objects: sets of size 0 to 3, small groups, graphs and categories;
   - degenerate objects: empty set, zero object, identity map, constant function, discrete or
     indiscrete topology, zero parameters;
   - extremal objects: maximal and minimal examples, equality cases, sharpness examples;
   - standard pathological objects: non-Hausdorff spaces, non-Noetherian rings, non-measurable
     sets, discontinuous functions, singular spaces;
   - free or universal examples: free groups, polynomial rings, quotients, products and
     coproducts;
   - for physical models: zero fields or parameters, singular points, boundary effects,
     resonances, adversarial corners of an uncertainty set.
4. **Compute explicitly.** Verify each hypothesis and the conclusion directly. For a candidate
   counterexample, state exactly which hypotheses hold and which conclusion fails. A
   floating-point failure is a lead to investigate; only an exact witness refutes a statement.
5. **Compare variants.** If no counterexample appears, weaken one hypothesis at a time.
6. **Label each object:** `supporting_example`, `counterexample`, `boundary_case`,
   `sharpness_example` or `inconclusive_test`, with the lesson it teaches.
7. **Feed back into the work:**
   - in proof mode, a valid counterexample stops the proof attempt and triggers a correction or a
     failure report;
   - in research mode, examples and counterexamples update conjectures, hypotheses and probes.

## Checking in Lean

An important counterexample, or a supporting example that shows a definition is not vacuous, can
be checked in Lean: write it in `<task>/lean/` and check it with `lake env lean`, following
`plasmalean-lean-proofs`. For a kernel law, the degenerate case, concrete instance and counterexample found
here are the natural candidates for the sanity triad in `PlasmaLean/Sanity/`, added through
`plasmalean-audit-domain` or `plasmalean-formalize-theory`.
