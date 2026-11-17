---
name: plasmalean-examples-counterexamples
description: Construct examples, boundary cases, counterexamples and existence witnesses that clarify definitions, test whether a statement or conjecture is true, show which hypotheses are needed, or prove existence. Use inside `plasmalean-reasoning-loop`, for requests such as "find a counterexample to ...", "find an example of ...", "test this conjecture" or "is this hypothesis needed?", and when designing the sanity triad for a kernel law. Assesses whether an evolutionary search could find the object and, if so, launches one in parallel.
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

## Consider an evolutionary search

When the object sought is not found quickly by hand, by the construction families above or by a
small exhaustive search, assess whether an evolutionary search with `plasmalean-evolve-optimize` could find
it. This applies equally to counterexamples, to examples with prescribed properties, to extremal
or sharpness examples, and to witnesses for existence proofs.

**It is likely to be fruitful when all of these hold:**

- the object can be written as a Lean term of a concrete type: finite data such as lists, tuples,
  matrices, polynomials with rational coefficients, graphs or finite tables, or a short program
  generating them (in PlasmaLean: rational profile or Fourier coefficients, coil data, test
  functions for an energy form, cell lists of a certificate);
- the required properties can be stated as Lean propositions about one candidate and proved for
  it, ideally by computation or standard tactics (`simp`, `norm_num`, `omega`, `kernel_fact`);
- there is a computable graded measure (over `ℚ`, `ℤ` or `ℕ`, not `ℝ`; use the exact enclosures of
  `PlasmaLean/Certificates/`) that improves as candidates get closer to the goal, such as a margin
  whose positivity is the property sought, the number of satisfied conditions, a size, or a
  violation amount; a pure yes-or-no target with no signal of progress gives a needle in a
  haystack;
- the space is too large to search exhaustively, yet each candidate is cheap to evaluate;
- no known construction already settles the question (check the sources first).

**It is unlikely to help** when the object is infinite or noncomputable with no finite
parametrization, when the property cannot be proved for a single candidate, when there is no
graded measure, when a small exhaustive search suffices (run it instead), or when the claim is
probably true and needs a general proof rather than an example.

**Formulating the search.** Encode the goal so that progress is visible:

- make the domain conditions (the hypotheses the object must satisfy) the *constraints*, proved for
  each candidate;
- make the target property a *measure* to optimize, for example a margin `m(candidate)` with the
  property equivalent to `m(candidate) > 0`, or the number of conditions violated;
- once a candidate reaches the target, add the target property as a constraint (or prove it
  separately) so the final package proves it.

**Launching it.** If the assessment is positive, launch the search with a sub-agent in parallel,
and continue the current work meanwhile:

1. Write the problem (`problem.json`, `context.lean` and two or three seeds) in a new run folder
   `notes/reasoning/<YYYY-MM-DD>-evolve-<slug>/`, and record in the current task's `log.md` why
   the search is promising and where it runs.
2. Launch one background sub-agent with the brief: follow `plasmalean-evolve-optimize` on that folder, ensure
   the server with `plasmalean-ensure-theory-server`, run at most a stated budget (by default three
   generations of about twenty candidates, stopping early once the target is reached), generate
   candidates itself if it cannot launch its own sub-agents, and report the best package, its
   score, whether the target property was proved, and the run's main insights.
3. Continue constructing by hand, proving, or exploring other branches. Do not run a second search
   on the same question at the same time; the server checks one candidate at a time.
   The server holds about 9 GB while it runs: launch a search only when no heavy build is running
   or planned during it (laptop budget), or send it to the workstation.
4. When the sub-agent reports, read its run folder rather than trusting the summary. A valid
   package whose constraints include the target property is a Lean-checked witness: a
   counterexample refutes the conjecture, and an existence witness gives an existence proof once
   promoted into the library (see `plasmalean-evolve-optimize`). A search that fails is not evidence that no
   object exists; record it as a barrier with its insights.

In interactive mode, mention the launch in the report to the user; in `keep working` mode,
launch without asking, within the budget.

## Checking in Lean

An important counterexample, or a supporting example that shows a definition is not vacuous, can
be checked in Lean: write it in `<task>/lean/` and check it with `lake env lean`, following
`plasmalean-lean-proofs`. For a kernel law, the degenerate case, concrete instance and counterexample found
here are the natural candidates for the sanity triad in `PlasmaLean/Sanity/`, added through
`plasmalean-audit-domain` or `plasmalean-formalize-theory`.
