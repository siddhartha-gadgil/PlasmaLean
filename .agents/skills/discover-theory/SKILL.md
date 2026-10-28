---
name: discover-theory
description: Develop new mathematical theory for a LeanTheory-based formalization using conjecture, proof, counterexample and refinement loops. Use when existing results do not yield a useful margin, bound, existence theorem, error estimate or constructive design condition.
---

# Discover useful mathematics

Read the actual kernel, `notes/formalization/00-model-contracts.md`, `notes/implementation-plan.md` and the method notes in `notes/goals/`. Prefer theoretical advances; use numerical experiments to discover structure and to produce counterexamples or candidate certificates.

## Choose a precise gap

Select one missing implication on the path to a useful result or design. Specify inputs, output, model, norm, boundary conditions, parameter range and quantifiers. Prefer a reusable inequality or reduction over another opaque objective function.

Typical targets: completing squares in an energy functional, identifying the right quotient by symmetry or neutral modes, bounding a coupling block, certifying an invariant barrier, bounding drift through an approximate invariant, a derivative estimate from design parameters to the quantity of interest, a robust margin under parameter uncertainty.

## Run the discovery loop

1. Formulate the proposed theorem with all constants and hypotheses.
2. Look up the closest primary literature and its limitations. Record novelty as provisional until the search and source comparison are complete.
3. Seek a proof by algebraic rearrangement, conservation, symmetry, comparison, compactness, variational arguments, perturbation theory or validated computation.
4. Independently seek counterexamples: zero modes, resonances, degenerate parameters, singular points, boundary effects, large gradients, truncated modes, adversarial corners of the uncertainty set.
5. Check an experimental counterexample against the exact definitions. A floating-point failure is evidence to investigate; an exact witness refutes the statement.
6. If refuted, repair the claim by an interpretable hypothesis or a narrower conclusion, and record why the change is necessary.
7. Prove the repaired theorem, formalize it (`formalize-theory`), and test its useful special cases (the sanity triad of `audit-domain`). Repeat until a meaningful theorem or a clearly stated obstruction remains.

Keep conjectures, exact counterexamples, proof sketches, compiled Lean theorems and numerical observations separate. Never add a conjecture as an axiom, claim novelty from Lean acceptance, or hide an unresolved estimate inside a typeclass instance.

## Make the mathematics constructive

Prefer conclusions supplying a margin, an explicit radius, a parameter interval or a checkable witness. For example, seek `q(ξ) ≥ c ‖ξ‖²` on a declared admissible quotient with computable `c > 0`, rather than an unquantified positivity claim; the template's `amplitude_bound` (`LeanTheory/Bridge/Example.lean`) is the simplest instance of this shape: an explicit bound from a conserved quantity. For uncertainty, prove bounds for every parameter in the stated set; do not replace universal quantifiers by a sample grid.

Keep the theorem's actual scope when the strong form fails. Explore weaker but true statements (nonnegativity instead of coercivity, finite-time instead of all-time, parameter-restricted results) or an explicit witness of failure.

## Finish with an actionable record

Write the final claim, proof or obstruction, exact hypotheses, literature comparison, counterexample attempts, Lean status, design implication and next dependency. Update `notes/implementation-plan.md` after successful formalization. Do not inflate a restricted mathematical improvement into a claim about the full real-world system.
