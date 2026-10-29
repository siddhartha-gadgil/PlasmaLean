---
name: plasmalean-discover-theory
description: Develop new mathematical theory for PlasmaLean using conjecture, proof, counterexample, and refinement loops. Use when existing results do not yield a useful stability margin, transport bound, equilibrium theorem, error estimate, or constructive design condition.
---

# Discover useful plasma mathematics

Read the selected research note (`notes/theory/`), its goal/question and dependencies in the research graph of `notes/implementation-plan.md`, the actual kernel, `notes/formalization/00-model-contracts.md`, the relevant topic note, `08-roadmap.md` and, for model-adequacy questions, `notes/goals/`. Preserve the project's preference for theoretical advances; use numerical experiments to discover structure and produce counterexamples or candidate certificates. Heavy numerics go to the workstation (`Workstation.md`).

**Dependency gating.** Only compiled Lean declarations count as established. Do not assume an upstream note, a sourced theorem or a numerical observation is true unless its required declaration compiles (default build, or an on-demand module under the workstation policy). Otherwise keep the dependency explicit and every downstream claim conditional and unverified.

## Choose a precise gap

Select one missing implication on the path to a practical design. Specify inputs, output, model, norm, boundary conditions, parameter range, and quantifiers. Prefer a reusable inequality or reduction over another opaque objective function.

Useful targets include completing squares in the MHD energy, identifying the correct quotient by neutral displacements, bounding a coupling block, certifying an invariant barrier, bounding drift through an approximate invariant, obtaining a coil-to-field derivative estimate, and proving a robust thermal or stress margin.

## Run the discovery loop

1. Formulate the proposed theorem with all constants and hypotheses.
2. Look up the closest primary literature and its limitations. Record novelty as provisional until the search and source comparison are complete.
3. Seek a proof using algebraic rearrangement, conservation, symmetry, comparison, compactness, variational arguments, perturbation theory, or validated computation.
4. Independently seek counterexamples: zero modes, resonances, vanishing field, near-axis singularities, boundary displacement, large gradients, omitted Fourier modes, degraded materials, and adversarial uncertainty corners.
5. Check an experimental counterexample against the exact definitions. A floating-point failure is evidence to investigate; an exact witness refutes the statement.
6. If refuted, repair the claim by a physically interpretable hypothesis or narrower conclusion. Record why the change is necessary.
7. Prove the repaired theorem and test its useful special cases. Formalize it with `plasmalean-formalize-theory` when the argument and prerequisites are ready; otherwise create the next research note or record a clearly stated obstruction. Repeat until a meaningful theorem or obstruction remains.

Keep conjectures, exact counterexamples, proof sketches, compiled Lean theorems, and numerical observations separate. Never add a conjecture as an axiom, claim novelty from Lean acceptance, or hide an unresolved estimate inside a typeclass instance.

## Make the mathematics constructive

Prefer conclusions supplying a margin, an explicit radius, a parameter interval, or a checkable witness. For example, seek `q(ξ) ≥ c ‖ξ‖²` on a declared admissible quotient, with computable `c > 0`, rather than an unquantified claim of stability. For design uncertainty, prove bounds for every parameter in the stated set; do not replace universal quantifiers by a sample grid.

Keep the theorem's actual scope when coercivity fails. Explore nonnegative energy, observable control, finite-time confinement, parameter-restricted stability, or an instability witness. Treat the research targets in `08-roadmap.md` as proposals, not promises that existing machinery solves them.

## Finish with an actionable record

Update the note (new notes follow `notes/note-template.md`) with the final claim, proof or obstruction, exact hypotheses, literature comparison, counterexample attempts, difficulty, barriers, Lean readiness, design implication and next dependencies. Create new `N-*` or `Q-*` entries for substantial branches.

**Update the note graph and the plan after every work unit, including failures.** Record the outcome in the note and in the registries of `notes/implementation-plan.md` (status, readiness, next action, newly ready dependants) and add a dated §13 entry when the result matters to the plan. A refuted conjecture or a failed approach is recorded as a barrier, so it is not retried blindly (re-planning trigger, plan §6). Do not inflate a restricted mathematical improvement into a verified result or a proof of full reactor feasibility.
