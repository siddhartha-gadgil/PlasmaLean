---
name: plasmalean-certify-numerics
description: Build and check numerical proof certificates for PlasmaLean using exact arithmetic, validated enclosures, and analytic remainder estimates. Use for equilibrium validation, spectral bounds, KAM hypotheses, continuous geometry, quadrature, or parameter uncertainty; use external solvers only to propose candidates.
---

# Certify a numerical candidate

Read `notes/formalization/05-verified-numerics.md`, the topic note, the kernel definitions, and the existing checker implementation. Check actual interval-library compatibility before importing a package. Do not assume that a package mentioned in a planning note is installed or sound for the required operations.

## Define the certificate boundary

Specify the decoded mathematical candidate, exact theorem to conclude, continuous domain, uncertainty set, norm, and every error source. Record source commit, solver/version, units, Fourier normalization, current orientation, coefficient ordering, and coefficient hash. Treat floats, meshes, optimizer convergence flags, and external interval reports as untrusted inputs.

Parse decimal coefficients as exact rationals or explicitly bounded measurements. Prove parser/checker correctness and interval containment. Handle division by excluding zero, transcendental enclosures, integration remainders, mesh coverage, geometric singularities, and infinite tails.

## Use the appropriate proof route

- **Finite algebra:** verify an exact factorization or a rigorously perturbed matrix inequality.
- **Continuous geometry:** prove all parameter boxes covered and bound between samples; reject a certificate based solely on sampled distances.
- **Equilibrium:** prove a contraction or other existence theorem for the actual continuum operator, including boundary conditions, phase/gauge fixing, and tails. For `T = id - A ∘ F`, prove that a fixed point implies `F = 0`, for example through injectivity of `A`.
- **Stability:** bound the retained block, omitted subspace, cross terms, coefficient errors, quadrature, and the change from the approximate to the certified equilibrium. Keep a discrete result explicitly discrete if continuum transfer is missing.
- **KAM:** check nondegeneracy, regularity, residual, and all small denominators through a theorem. Use exact arithmetic structure for an infinite Diophantine statement; a finite resonance scan is insufficient.
- **Materials:** bound empirical coefficients on their valid envelope and quantify every operating state in the claimed range.

Use the inequalities and soundness targets in `05-verified-numerics.md`. Failure to close a bound is an unresolved certificate, not evidence of physical instability.

## Build a small sound checker

Define certificate data independently of the search algorithm. Prove a theorem of the form `check c = true → ClaimedProperty (decode c)` using exact, kernel-checkable reasoning. Keep noncomputable analytic definitions behind soundness theorems and the decidable checker in the computational layer. Do not import native execution, GPU output, Python assertions, or an SMT success flag as an unchecked theorem. For large certificates, prefer an inductive certificate predicate whose proof term is built step by step from the witness (the SubsetSum pattern) over one monolithic `decide +kernel` run; follow `plasmalean-lean-proofs`.

Test valid and invalid certificate fixtures, including missing coverage, zero denominators, altered coefficients, omitted tail bounds, and contradictory intervals. Run the affected Lean build and inspect axioms of the public soundness theorem.

Report certified quantities and margins, the assumptions supplied by other theorems or law instances, arithmetic/truncation uncertainty, physical-data uncertainty, and remaining model discrepancy. Attach the candidate's identity to the result so a later coil or profile change cannot reuse its certificate accidentally.
