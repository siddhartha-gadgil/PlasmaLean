---
name: plasmalean-audit-domain
description: Audit and extend the PlasmaLean domain kernel, its physical assumptions, and its sanity checks. Use when starting work in PlasmaLean, choosing a model, reviewing a stability claim, changing foundational definitions, or planning the next sound formalization task.
---

# Audit the PlasmaLean domain

## Establish the actual state

Work from the selected PlasmaLean checkout. Read `AGENTS.md` if present, `lean-toolchain`, `lakefile.toml`, `notes/domain-libraries.md`, and the relevant Lean files. Read `notes/formalization/00-model-contracts.md` and the applicable topic note. Treat website examples and planning notes as specifications until matching compiled declarations exist. The source snapshot used for these guides, commit `466920416e97561e4669759ab4077b9a23281ebd`, contains starter code, not the advertised complete theory.

Record the checkout commit and dependency versions. Search pinned Mathlib and any installed TauCeti sources with `rg` before proposing new infrastructure. Check compatibility before adding a dependency; do not change the toolchain merely to make a proof easier.

## Maintain the domain architecture

1. Keep domain definitions and external model laws in a small `Kernel` layer.
2. Represent laws as predicates, structures, or typeclasses with explicit fields. Pass law instances as hypotheses; do not add project axioms or an unproved universal instance.
3. Keep source-dependent material data and model-validity envelopes separate from mathematical consequences.
4. Prove sanity checks in a separate layer and derived results in `Theory`.
5. Put coefficient decoding, interval checkers, and candidate importers in `Certificates` or `Bridge`; keep heuristic solvers outside the trusted theorem path.

Use a single library initially; the repository already has `[[lean_lib]] name = "PlasmaLean"`. Add additional library targets only when there is a real dependency boundary. Provide module documentation and docstrings for definitions and theorems; expose the intended public API using the pinned Lean version's module conventions.

## Audit each claim

Write its model, domain, boundary conditions, regularity, units, parameter range, perturbation class, norm, and time horizon. Classify it as:

- a definition;
- a supplied physical or empirical assumption;
- a mathematical consequence to prove;
- a numerical observation;
- a proposed conjecture or research problem;
- a compiled theorem, with its declaration name and assumptions.

Keep equilibrium existence, field-line confinement, particle confinement, linear MHD stability, nonlinear stability, transport, and component feasibility as distinct predicates. Compose them only through proved implications. Distinguish the domain-model kernel from Lean's logical kernel.

## Challenge the inherited claims

Check the corrections in `00-model-contracts.md`. In particular:

- Derive `B · ∇p = 0`; require compact, connected, orientable regular pressure surfaces and a nonvanishing tangent field before deducing torus topology. Do not infer a global foliation.
- Make Boozer coordinates a chart structure on a flux annulus with a checked Jacobian. Do not postulate nonsingular global angles across the magnetic axis.
- Distinguish `p = 0` from the additional condition `J = 0`.
- Treat the Garren–Boozer expansion as a source-specific compatibility result, not a universal impossibility theorem.
- Separate a Mercier or ballooning diagnostic from a full energy-principle certificate.
- Require all-mode bounds before transferring finite-dimensional positivity to continuum stability.
- Treat KAM barriers and their hypotheses individually; do not claim that KAM supplies a complete foliation.
- Source engineering thresholds from the chosen machine and material, instead of treating example distances as universal constants.

## Prove that definitions have content

For each new definition, prove characterizing properties and at least one meaningful limiting case. Construct witnesses for key law bundles in simple consistent models. Check zero field, uniform field, constant pressure, axisymmetry, zero current, neutral displacement, zero heat source, and collapsed uncertainty intervals as appropriate. Diagnose inconsistent or vacuous assumptions before proving further consequences.

Prefer the smallest theorem that opens a useful next step. Conclude with an assumption ledger, any corrected definitions, compiled sanity theorems, and the next theorem target. Record unresolved physical assumptions explicitly. Never label the real device stable solely because a conditional formal theorem compiles.
