---
name: plasmalean-certify-numerics
description: Build and check numerical proof certificates for PlasmaLean using exact arithmetic, validated enclosures, and analytic remainder estimates. Use for equilibrium validation, spectral bounds, KAM hypotheses, continuous geometry, quadrature, or parameter uncertainty; use external solvers only to propose candidates.
---

# Certify a numerical candidate

Read `notes/formalization/05-verified-numerics.md`, the originating research note and its dependency requirements (research graph in `notes/implementation-plan.md`), the topic note, the kernel definitions, and the existing certificate modules in `PlasmaLean/Certificates/` (index: `PlasmaLean/Certificates/README.md`) before writing a new checker. Reuse what is there. Check actual interval-library compatibility before importing a package. Do not assume that a package mentioned in a planning note is installed or sound for the required operations.

**Dependency gating.** The analytic theorem that turns a certificate into a continuum statement must itself be compiled. If it is only sourced or sketched, the certificate proves a finite statement only; keep the continuum claim explicitly conditional until the bridge theorem compiles.

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

Define certificate data independently of the search algorithm. Prove a theorem of the form `check c = true → ClaimedProperty (decode c)` using exact, kernel-checkable reasoning. Keep noncomputable analytic definitions behind soundness theorems and the decidable checker in the computational layer. Do not import native execution, GPU output, Python assertions, or an SMT success flag as an unchecked theorem. Close concrete instances without any `decide` (follow `plasmalean-lean-proofs` §2):

- `kernel_fact` for closed side conditions and finite quantifiers over lists and ranges;
- `bool_cert` for Boolean checkers; `eval_cert`/`fiv_cert` (and `eval_decide`/`fiv_decide`) for ball, interval, rational and polynomial evaluations; `icc_cert` for sums and quantifiers over integer intervals;
- the Kronecker and family certificates (`kron_proof`, `kron2_proof`, `kron_lt`, `l1kron_cert`, `fampack_cert`) for KAM-family checks;
- a new inductive certificate predicate with a `meta` builder (the SubsetSum pattern, `PlasmaLean/SubsetSum.lean`) for a new large format, as `Design/PolygonCoilCubicLineCert.lean` does for coil lines.

Generators validate every emitted bound with exact rational arithmetic before writing Lean (round outward, recompute, assert; see `scripts/gc_kam/lamcell/validate.py`).

Test valid and invalid certificate fixtures, including missing coverage, zero denominators, altered coefficients, omitted tail bounds, and contradictory intervals. Build the affected modules one at a time (≤ 6 GB per process; record CPU, peak memory and private olean size) and inspect axioms of the public soundness theorem. Heavy searches and first builds go to the workstation (`Workstation.md`, `plasmalean-workstation-update`); the workstation's job is a smaller certificate, not a bigger proof.

Report certified quantities and margins, the assumptions supplied by other theorems or law instances, arithmetic/truncation uncertainty, physical-data uncertainty, and remaining model discrepancy. Attach the candidate's identity to the result so a later coil or profile change cannot reuse its certificate accidentally.

**Update the note graph and the plan after every work unit, including failures.** Record declaration names, verification status (default build or on-demand), margins, build cost, remaining barriers and newly ready notes in the originating note and in the registries of `notes/implementation-plan.md`, with a dated §13 entry. A certificate that does not close is an open item with its measured obstruction (resolution, memory, olean size), not evidence that the property fails.
