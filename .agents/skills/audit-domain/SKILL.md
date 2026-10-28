---
name: audit-domain
description: Audit and extend the domain kernel, model assumptions and sanity checks of a LeanTheory-based formalization. Use when starting work in a LeanTheory project, choosing or changing a model, reviewing a claimed theorem, changing foundational definitions, or planning the next sound formalization task.
---

# Audit the domain and its assumptions

## Establish the actual state

Work from the selected checkout. Read `AGENTS.md` if present, `lean-toolchain`, `lakefile.toml`, `notes/domain-libraries.md`, `notes/formalization/00-model-contracts.md`, `notes/implementation-plan.md` and the relevant Lean files. Treat planning notes, papers and website text as specifications until matching compiled declarations exist.

Record the checkout commit and dependency versions. Search pinned Mathlib (`.lake/packages/mathlib`) with `rg` before proposing new infrastructure. Check compatibility before adding a dependency; do not change the toolchain merely to make a proof easier.

## Maintain the layered architecture

1. **Kernel** (`LeanTheory/Kernel/`): domain definitions and the external model laws, kept small. Template: `LeanTheory/Kernel/Example.lean` (`OscParams`, `energy`, the law `OscillatorLaw p x v`, consequences `energy_conserved`, `potential_le_energy`).
2. **Laws as typeclasses or structures with explicit fields**, passed as hypotheses (`[OscillatorLaw p x v]`). Never add a project `axiom` or an unproved universal instance.
3. **Sanity** (`LeanTheory/Sanity/`): the sanity triad for every law (below). Template: `LeanTheory/Sanity/Example.lean`.
4. **Theory** (`LeanTheory/Theory/`): derived, reusable mathematics.
5. **Bridge** (`LeanTheory/Bridge/`): structural lemmas and the theorems that turn certificate data into semantic statements. Template: `LeanTheory/Bridge/Example.lean` (`OscillatorLaw.shift/add/smul`, `amplitude_bound`).
6. **Certificates** (`LeanTheory/Certificates/`): checkers, decoders and proof-term certificates; heuristic solvers stay outside the trusted path. Template: `LeanTheory/Certificates/Example.lean`.
7. **Design** (`LeanTheory/Design/`): concrete candidates composed from the layers above (see `domain-design`).

Keep source-dependent data (measured constants, validity envelopes) separate from mathematical consequences. Use the single library `LeanTheory` unless a real dependency boundary appears. Every module needs a module docstring and every declaration a docstring.

## Audit each claim

Write down its model, domain, boundary conditions, regularity, units, parameter range, perturbation class, norm and time horizon. Classify it as:

- a definition;
- a supplied model or empirical assumption (a law instance);
- a mathematical consequence to prove;
- a numerical observation;
- a conjecture or research problem;
- a compiled theorem, with its declaration name and assumptions.

Keep distinct properties as distinct predicates (existence, invariance, linear stability, nonlinear stability, quantitative bounds, feasibility) and compose them only through proved implications. Distinguish the domain-model kernel from Lean's logical kernel.

Check the corrections and contracts recorded in `00-model-contracts.md`, and add new ones there. Typical issues to challenge:

- a global structure inferred from a local one (a chart, coordinate system or foliation assumed everywhere);
- a degenerate case silently excluded or silently included (zero parameter, zero field, vanishing denominator);
- a diagnostic or necessary condition presented as a sufficient one;
- a finite-dimensional or truncated result presented as a statement about the full continuum model;
- a source-specific or asymptotic result stated as universal;
- example constants from one source treated as universal thresholds.

## The sanity triad

For every new law or law bundle, prove all three:

- **Degenerate case**: a limiting parameter where the law reduces to something elementary (`free_velocity_const`: with stiffness `0`, velocity is constant).
- **Concrete instance**: an explicit model satisfying the law, so theorems about it are not vacuous (`instOscillatorLawCos`).
- **Counterexample**: an explicit object that fails the law, so the law has content (`not_oscillatorLaw_exp`).

For each new definition also prove characterizing properties and at least one meaningful limiting case. For each certificate format, an accepted and a rejected fixture (`initialStates_energy_le` / `initialStates_not_le_small`). Diagnose inconsistent or vacuous assumptions before proving further consequences.

## Deliver

- **Assumption ledger**: every law instance and supplied constant used by the claim, with its source and validity envelope.
- **Scope statement**: exactly what the compiled theorem says (model, quantifiers, norm, range) and what it does not.
- Corrected definitions, compiled sanity theorems, and the next theorem target (prefer the smallest theorem that opens a useful next step).

Record unresolved model assumptions explicitly. Never describe the real system as having a property solely because a conditional formal theorem compiles.
