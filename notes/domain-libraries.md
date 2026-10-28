# Domain libraries in Lean

Instructions for modelling a real-world domain in Lean so that it can be audited cleanly. A
domain library has a *kernel*, *sanity checks* for the kernel, and a *library* of results with
*verification theorems*. The template's worked example is `LeanTheory/Kernel/Example.lean`,
`LeanTheory/Sanity/Example.lean`, `LeanTheory/Bridge/Example.lean` and
`LeanTheory/Certificates/Example.lean`.

Use Lean's module system: every file starts with `module`, the API is `public`, and definitions
that downstream proofs must unfold are `@[expose]`. Every definition and theorem has a docstring
and every module a module docstring. Mathlib is the main dependency; add others in
`lakefile.toml` (`[[require]]`) only when needed.

## Agent runs and loops

On the first run (no kernel yet), build the kernel as below, then its sanity checks, then loop
through the library-building steps, accumulating theory as code until progress halts.

On later runs, examine the kernel and fix errors if any, recording changes in comments and in the
implementation log of `notes/implementation-plan.md`. Extend the kernel only when more external
facts or concepts must be modelled. The main goal of a later run is to assess what has been done
and what remains for the goals, and to add verified code.

After each run, update the progress log of the implementation plan: what was proved (with
declaration names), what failed and why, the checks actually run (`lake build`, the axiom audit),
and the next targets. Distinguish compiled theorems from synthetic examples, supplied data and
planned work.

## Kernel

The layer that models the domain with definitions and externally known facts. Keep it as small as
reasonable while complete: all relevant facts should be consequences, and every query should be
answerable through functions built from the kernel.

NEVER introduce axioms. Ingredients:

* definitions, structures and inductive types for the basic objects of the domain;
* properties modelled by structures, typeclasses or inductive propositions;
* facts and laws modelled as **typeclasses**; results depending on them take them as (instance)
  arguments, e.g. `[OscillatorLaw p x v]` in `Kernel/Example`.

The kernel is a separate file (or folder). Its module docstring explains the domain, the Lean
encoding, and says clearly that it is a kernel file.

## Sanity checks for the kernel

State results that are true in the domain and prove them from the kernel definitions and laws:
characterizing results, special and degenerate cases, bounds. For every law provide at least

* a **degenerate case** (e.g. zero stiffness gives a free particle);
* a **concrete instance**, so the law is satisfiable and theorems about it are not vacuous;
* a **counterexample**: an object that is not an instance, showing the law excludes something.

## Library with verification

The library builds on the kernel incrementally, adding results from the literature and then new
discoveries. Use both theory and exact numerical computation (interval arithmetic, certificates),
prioritizing theory; use computation-based proofs to go beyond the theory where it is unclear how
to extend it.

Whenever a definition or type is introduced, state and prove its properties: characterizing
properties, consequences and special (especially degenerate) cases. If a check fails, correct the
definition. When a theorem is supposed to be useful, check it the same way, by proving corollaries
and special cases, to make sure the statement is right.
