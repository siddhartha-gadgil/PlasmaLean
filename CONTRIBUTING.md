# Contributing

A useful contribution can be a precise theorem with a paper proof, a counterexample to a proposed
implication, a clearer explanation of an existing verified result, a reproducible numerical
candidate, or Lean code. Lean experience is not a prerequisite for the first four.

Choose one concrete target and identify the model and theorem it advances. The
[implementation plan](notes/implementation-plan.md) is the plan of record.

## Three reading paths

### 1. Understand what a verified statement means

Read the [model contracts](notes/formalization/00-model-contracts.md), then the worked example:
the [kernel](LeanTheory/Kernel/Example.lean) (a law stated as a typeclass), its
[sanity checks](LeanTheory/Sanity/Example.lean) (degenerate case, instance, counterexample) and
the [bridge](LeanTheory/Bridge/Example.lean) (composition theorems). For an advertised result,
locate the Lean declaration and read its hypotheses before reading the proof. Distinguish an
assumed solution from a constructed one, and a model statement from a claim about reality.

### 2. Follow one complete chain

[Certificates/Example](LeanTheory/Certificates/Example.lean) goes from exact data, through a
`kernel_fact` certificate, to a semantic statement about every trajectory obeying the law. For
a larger chain, follow the analytic route of `Theory/KAM`:
[Diophantine estimates](LeanTheory/Theory/KAM/Diophantine.lean),
[the cohomological equation](LeanTheory/Theory/KAM/Cohomological.lean),
[the strip algebra](LeanTheory/Theory/KAM/StripAlgebra.lean) and
[convergence of Newton iterations](LeanTheory/Theory/KAM/KamSequence.lean).

### 3. Contribute a numerical certificate or Lean proof

Read [SubsetSum](LeanTheory/SubsetSum.lean), then
[polynomial interval checking](LeanTheory/Certificates/PolyInterval.lean) and the
[radii-polynomial theorem](LeanTheory/Certificates/RadiiPolynomial.lean). The intended chain is:
an untrusted search proposes data; a proved checker validates bounds, coverage and remainders;
an analytic theorem converts the bounds into a continuum conclusion. Document the whole chain.
A dense grid alone is not a uniform bound, and an exact certificate for an approximate model
needs a separate model-error estimate before it supports a claim about a more detailed model.

## Result card

Include this in the note or pull-request description (brief for a small lemma):

```text
Title and status: proved / conditional / numerical observation / research target
Exact Lean declaration(s), or proposed statement:
Model, domain, boundary conditions, units and parameter ranges:
Object shared with other claims (same witness?):
Input assumptions, with sources and locators:
Conclusion, including all quantifiers:
Existence: proved here / proved elsewhere / supplied as a hypothesis
Model reductions or empirical data still supplied:
Proof outline and dependencies:
Positive example and relevant failure case:
Numerical generation command, dependencies, seeds and artifact hashes, if applicable:
Verification command and observed resource requirements:
Remaining bridge to the next claim:
```

## Review the model and the proof separately

**Model review** checks that the statement represents the intended problem, that cited theorems
have the right hypotheses, and that all parts refer to the same object; it checks units,
approximation errors, quantifiers, boundary conditions and whether assumptions can be met.
**Formal review** checks definitions, statements, dependency closure and proofs, including the
bridge from generated data to the quantities in the theorem. Lean and the axiom audit establish
the deduction, not the accuracy of a supplied model or empirical law.

Keep the kernel small and every modeling assumption discoverable where it is defined. New laws
come with an ordinary-language statement, a source or rationale, and sanity theorems. When an
attempt fails, record the obstruction and correct the statement; do not leave a refuted formula
as the current specification.

## Reproducing numerical searches

Committed certificates are checked without trusting their generators; regenerating them is a
separate task. A generator should have pinned dependencies (`scripts/requirements.txt`),
configurable paths, reproducible inputs, recorded precision/rounding/tail bounds and output
hashes, and must validate every emitted bound in exact arithmetic before writing Lean.

## Build and check

```sh
scripts/setup.sh --check-axioms        # or: lake exe cache get && lake build
lake build LeanTheory.Kernel.Example    # a small target while developing
lake build                              # must finish with zero warnings
lake env lean scripts/check_axioms.lean # standard axioms only
```

Large certificates can take several gigabytes per process: build them in small groups, keep each
process ≤ 6 GB, and report the checks actually completed. Register new entry points in
`scripts/check_axioms.lean` and new modules in `LeanTheory.lean`.
