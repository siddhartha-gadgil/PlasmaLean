---
name: certify-numerics
description: Build and check numerical proof certificates for a LeanTheory-based formalization using exact arithmetic, validated enclosures and analytic remainder estimates. Use for existence by contraction, spectral or coercivity bounds, polynomial and interval checks, quadrature, continuous parameter families or uncertainty sets; external solvers only propose candidates.
---

# Certify a numerical candidate

Read the kernel definitions, the relevant theory, `notes/formalization/00-model-contracts.md`, and the existing certificate modules in `LeanTheory/Certificates/` before writing a new checker. Reuse what is there; do not assume a package mentioned in a planning note is installed or sound for the required operations.

## Define the certificate boundary

Specify the decoded mathematical candidate, the exact theorem to conclude, the continuous domain, the uncertainty set, the norm, and every error source. Record source commit, solver and version, units, normalizations, coefficient ordering and a hash of the data. Treat floats, meshes, optimizer convergence flags and external interval reports as untrusted inputs.

Parse decimal coefficients as exact rationals or explicitly bounded measurements. Prove parser/checker correctness and interval containment. Handle division (exclude zero), transcendental enclosures, integration remainders, mesh coverage, singularities and infinite tails.

## Use the appropriate proof route

- **Finite algebra:** an exact factorization or a rigorously perturbed matrix inequality (`Certificates/BlockBounds`, `Certificates/RationalIntervals`).
- **Polynomial and piecewise bounds on an interval:** `QPoly.checkOn` (`Certificates/PolyInterval`), `IccListCert`.
- **Continuous parameter families:** prove every parameter box covered and bound the function between samples; reject a certificate based solely on sampled values.
- **Existence near an approximate solution:** a radii-polynomial or contraction argument (`Certificates/RadiiPolynomial`, `Certificates/Contraction`) for the actual operator, including boundary conditions, gauge fixing and tails. For `T = id - A ∘ F`, prove that a fixed point gives `F = 0` (for example by injectivity of `A`).
- **Sequence spaces and spectral data:** `WeightedEll1`, `ConvAlgebra`, `FourierRegularity`, the Kronecker ball modules (`KronBall*`, `Kronecker2D*`).
- **Quadrature and transcendental functions:** fixed-point interval balls `FIv` (`ValidatedQuadrature`, `ValidatedTrig`, `ValidatedTrigFast`).
- **Discretizations:** `SBP`, `DiscreteMaxPrinciple`. Keep a discrete result explicitly discrete if the continuum transfer is missing.
- **Stability and coercivity:** bound the retained block, the omitted subspace, cross terms, coefficient errors, quadrature, and the change from the approximate to the certified state.
- **Empirical data:** bound coefficients on their valid envelope and quantify over every state in the claimed range.

Failure to close a bound is an unresolved certificate, not evidence that the property fails.

## Build a small sound checker

Define certificate data independently of the search algorithm. Prove a theorem of the form `check c = true → ClaimedProperty (decode c)`, or an inductive certificate predicate with a soundness theorem, using exact kernel-checkable reasoning. Keep noncomputable analytic definitions behind soundness theorems. Never import native execution, GPU output, Python assertions or an SMT success flag as an unchecked theorem.

Close concrete instances without any `decide` (see `lean-proofs` §2):

- `kernel_fact` for closed side conditions and finite quantifiers over lists and ranges (as in `initialStates_energy_le`);
- `bool_cert` for Boolean checkers; `eval_cert` / `fiv_cert` for whole ball, interval and polynomial evaluations;
- the SubsetSum pattern (`LeanTheory/SubsetSum.lean`) for a new large certificate format;
- `norm_num` / `rfl` for a handful of closed facts.

Generators must validate every emitted bound with exact rational arithmetic before writing it (round outward, recompute, assert). Test valid and invalid fixtures: missing coverage, zero denominators, altered coefficients, omitted tail bounds, contradictory intervals. Build the affected modules one at a time and inspect `#print axioms` for the public soundness theorem; heavy builds go to the workstation (`workstation-update`, `Workstation.md`).

## Worked example

`LeanTheory/Certificates/Example.lean`: exact data `initialStates` (21 rational states), rational energy `energyQ` with the cast lemma `energyQ_cast`, the certificate `initialStates_energy_le` by `kernel_fact`, the semantic statement `amplitude_cert` via `amplitude_bound`, and the rejected fixture `initialStates_not_le_small`.

## Report

Certified quantities and margins, assumptions supplied by other theorems or law instances, arithmetic/truncation uncertainty, data uncertainty, and remaining model discrepancy. Attach the candidate's identity (data hash, definitions) to the result so a later change of the candidate cannot reuse its certificate accidentally.
