---
name: plasmalean-proof-techniques
description: Library of mathematical proof techniques (logic, construction, induction, counting, invariants, bounding, epsilon-delta, density, compactness, universal properties, algorithm correctness, diagram chases, generic arguments, Bochner) with selection guidance and worked examples. Use when planning a proof, in the strategy phase of `plasmalean-reasoning-loop`, in `plasmalean-discover-theory`, or when an argument is stuck and a different technique may help.
---

# Choose and apply a proof technique

Each technique lives in `techniques/<area>/<name>/` with three files:

- `TECHNIQUE.md`: when the technique applies and the step-by-step method;
- `examples.md`: worked problem shapes showing the method in use;
- `manifest.json`: name, area and keywords used for matching.

## Select

1. Read the formalized problem: hypotheses, goal, definitions and any recorded examples.
2. Match its context against the registry keywords below, and read the `TECHNIQUE.md` of every
   plausible match. Respect a technique's stated pre-conditions: do not force an invariant
   argument onto a problem with no transformations, or a Bochner argument without a Riemannian
   setting.
3. Prefer a combination when the problem has several layers, for example a reduction followed by
   induction, or compactness followed by a uniform bound.
4. Turn each selected technique into concrete strategy fragments: named steps, the lemma each step
   needs, and where the hypotheses are used.

In a Lean formalization, also search the pinned Mathlib with `rg` for the matching API before
planning the proof by hand: `Finset.card` lemmas for counting, induction principles for descent,
`IsCompact` and `Filter.Tendsto` for compactness and limits, and the lifting lemmas of quotients
and products for universal properties. Follow `plasmalean-lean-proofs` when writing the code.

## Registry

| Technique | Area | Keywords | Path |
| :--- | :--- | :--- | :--- |
| Direct, contrapositive and contradiction proofs | Core logic | implication, contrapositive, contradiction, negation | `techniques/core/direct_contrapositive_contradiction/` |
| Cases and exhaustion | Core logic | cases, finite cases, parity, residues, signs | `techniques/core/cases_exhaustion/` |
| Equivalence and reduction | Core logic | iff, equivalent conditions, reduction, known theorem | `techniques/core/equivalence_reduction/` |
| Existence, construction and uniqueness | Construction | exists, witness, construction, unique, canonical object | `techniques/construction/existence_uniqueness/` |
| Induction, minimal counterexample and descent | Induction | induction, strong induction, structural induction, minimal counterexample, descent | `techniques/induction/induction_and_descent/` |
| Counting, double counting and pigeonhole | Combinatorics | counting, double counting, pigeonhole, finite set, incidence | `techniques/combinatorics/counting_pigeonhole/` |
| Invariant construction | General | combinatorics, group actions, game theory, iterative processes | `techniques/invariants/` |
| Bounding, monotonicity and extremal objects | Order, analysis, combinatorics | bounds, monotonicity, squeeze, maximal, minimal, extremal | `techniques/order/bounding_extremal/` |
| Epsilon-delta proofs | Analysis | limit, continuity, convergence, epsilon delta, metric space | `techniques/analysis/epsilon_delta/` |
| Density and approximation | Analysis, topology | density, approximation, dense subset, continuity, limit passage | `techniques/analysis/density_approximation/` |
| Compactness and local-to-global gluing | Topology, geometry, logic | compactness, local-to-global, gluing, open cover, finite subcover | `techniques/local_global/compactness_gluing/` |
| Universal property arguments | Algebra, category theory | universal property, product, coproduct, quotient, tensor product, adjunction | `techniques/algebra/universal_property/` |
| Algorithmic correctness | Algorithms, discrete mathematics | algorithm, termination, correctness, loop invariant, recursion | `techniques/algorithms/correctness/` |
| Diagram chase and diagrammatic reasoning | Algebra, topology, geometry | diagram chase, commutative diagram, exact sequence, geometric diagram | `techniques/diagrammatic/diagram_chase/` |
| Bochner technique | Geometry | Riemannian geometry, manifolds, curvature | `techniques/geometry/bochner_technique/` |
| Generic arguments | General | Baire category, measure theory, Zariski, dense open | `techniques/generic_arguments/` |

## Add a technique

Create `techniques/<area>/<name>/` with `TECHNIQUE.md`, `examples.md` and `manifest.json` (fields
`name`, `area`, `keywords`, `path`), then add a row to the registry above. PlasmaLean should
add the techniques its own proofs keep using, for example energy principles and coercivity,
comparison and Grönwall/Riccati arguments, or reductions of a design claim to a finite
certificate.
