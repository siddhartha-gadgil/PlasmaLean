---
name: plasmalean-discover-theory
description: Develop new mathematical theory for PlasmaLean using conjecture, proof, counterexample, and refinement loops. Use when existing results do not yield a useful stability margin, transport bound, equilibrium theorem, error estimate, or constructive design condition.
---

# Discover useful plasma mathematics

Read the actual kernel, `notes/formalization/00-model-contracts.md`, the relevant topic note, and `08-roadmap.md`. Preserve the project's preference for theoretical advances; use numerical experiments to discover structure and produce counterexamples or candidate certificates.

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
7. Prove the repaired theorem, formalize it, and test its useful special cases. Repeat until a meaningful theorem or a clearly stated obstruction remains.

Keep conjectures, exact counterexamples, proof sketches, compiled Lean theorems, and numerical observations separate. Never add a conjecture as an axiom, claim novelty from Lean acceptance, or hide an unresolved estimate inside a typeclass instance.

## Make the mathematics constructive

Prefer conclusions supplying a margin, an explicit radius, a parameter interval, or a checkable witness. For example, seek `q(ξ) ≥ c ‖ξ‖²` on a declared admissible quotient, with computable `c > 0`, rather than an unquantified claim of stability. For design uncertainty, prove bounds for every parameter in the stated set; do not replace universal quantifiers by a sample grid.

Keep the theorem's actual scope when coercivity fails. Explore nonnegative energy, observable control, finite-time confinement, parameter-restricted stability, or an instability witness. Treat the research targets in `08-roadmap.md` as proposals, not promises that existing machinery solves them.

## Finish with an actionable record

Write the final claim, proof or obstruction, exact hypotheses, literature comparison, counterexample attempts, Lean status, design implication, and next dependency. Update the theory and roadmap after successful formalization. Do not inflate a restricted mathematical improvement into a proof of full reactor feasibility.
