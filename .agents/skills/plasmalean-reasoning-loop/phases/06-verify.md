# Phase 3 (both modes): Verify

Check the latest step, lemma or conjecture in the active verification mode, and record the result
in the trace.

## INFORMAL_ONLY: the skeptic's hat

- Act as a critical peer reviewer. Look for gaps: unstated regularity, quantifier order, division
  by zero, empty or degenerate cases, implicit uniformity, misapplied theorems.
- Test the result against edge cases and the examples in `<task>/02_examples.md`. If a plausible
  counterexample appears, make it explicit with `plasmalean-examples-counterexamples`.
- When checking a conjecture or proposed extension, label it `supported`, `refuted`,
  `needs_hypotheses` or `open`; never upgrade it to a theorem without proof.
- For structured output, follow `../schemas/06-verify-informal.json`.

## WITH_LEAN: check the step in Lean

- Make sure Lean is set up (`scripts/get_cache.sh` for Mathlib and TauCeti, then the modules the draft imports built by
  frontier as in `plasmalean-develop-theory`, "Resource rules"), before the first check. Keep within
  the laptop budget: at most 12 GB of Lean memory at a time, a draft that imports a heavy
  certificate module checked alone, and heavy checks sent to the workstation (`Workstation.md`).
- Write the step as a self-contained file in `<task>/lean/`, for example `Step03.lean`, importing
  `Mathlib` or the project modules it needs (`import PlasmaLean.Kernel.Equilibrium`). State the
  lemma exactly as in the trace. Prefer declarative proofs (`have`, `show`, `calc`) so that the
  Lean proof follows the written argument, and follow `plasmalean-lean-proofs` and the project policies: no
  `decide` of any kind, and no `sorry`, `admit` or `axiom` in a step reported as checked.
- Use the existing definitions of Mathlib and the project rather than local copies, so that drafts
  can be promoted unchanged: for example `Even n`, which Mathlib defines as `∃ r, n = r + r`, rather
  than a private evenness predicate.
- Check it with `lake env lean <task>/lean/Step03.lean`, ending the file with `#print axioms` for
  each lemma, and confirm that only `propext`, `Classical.choice` and `Quot.sound` appear.
- Record the exact command, the compiler status and, on failure, an analysis of the error. For
  structured output, follow `../schemas/06-verify-lean.json`.
- These drafts are evidence for the task. They become project results only when promoted into
  `PlasmaLean/` with `plasmalean-formalize-theory` and pass the project's validity gate.

## After verification

In problem solving, verification is binary for the current step: a sound step continues the plan;
an unsound step halts it and passes control to `07-metacognition.md`. The research labels above are
only for exploratory conjectures.
