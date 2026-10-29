---
name: plasmalean-audit-domain
description: Strictly audit the PlasmaLean domain kernel, its physical assumptions, sanity checks and the claims built on them, old code as well as new. Use on `start`, when opening an unfamiliar checkout, choosing a model, reviewing a stability or confinement claim, changing foundational definitions, or deciding what research can soundly feed later formalization.
---

# Audit the PlasmaLean domain

## Establish the actual state

Work from the selected PlasmaLean checkout. Read `AGENTS.md` if present, `lean-toolchain`,
`lakefile.toml`, `notes/domain-libraries.md`, `notes/formalization/00-model-contracts.md`, the
"Research graph" part of `notes/implementation-plan.md` (registries and the strict-audit table),
the applicable topic and research notes, and the relevant Lean files. Treat website text, planning
notes, proof sketches and papers as unverified inputs until matching compiled declarations exist.
(The source snapshot used for the original guides, commit
`466920416e97561e4669759ab4077b9a23281ebd`, contained starter code, not the advertised theory.)

Record the checkout commit and dependency versions. Search pinned Mathlib
(`.lake/packages/mathlib`) and any installed TauCeti sources with `rg` before proposing new
infrastructure. Check compatibility before adding a dependency; do not change the toolchain merely
to make a proof easier.

**Do not grandfather previous code.** Compilation is necessary but is not a semantic audit, and the
age or apparent stability of a declaration is not evidence that its statement matches the intended
physics or mathematics. On a first audit (no audited commit in the plan), review **all** existing
kernel declarations and their sanity coverage. On later audits, review every change since the last
audited commit and all definitions, instances and theorems transitively affected by it.

## Run the strict repository audit

Prioritize the kernel (`PlasmaLean/Kernel/`: `Equilibrium`, `Slab`, `ThermalSlab`, `Transport`,
`Vacuum`, `Fusion`), then audit outward through `Sanity`, `Theory`, `Bridge`, `Certificates` and
`Design`:

1. **Full kernel inventory.** List every kernel definition, law (typeclass or structure),
   instance and exported theorem. Map each to its source, model status, validity envelope, users
   and sanity theorems. Do not sample the kernel.
2. **Repository search.** Search the whole tree for `axiom`, `sorry`, `admit`, `native_decide`,
   any `decide` variant in new code, `unsafe`, unchecked generated facts and suspicious universal
   instances. Inspect every match in context. Track the legacy `decide +kernel` count (Phase 16)
   and opaque `kernel_fact` leaves (`scripts/audit_kernel_fact.py`).
3. **Red-team checklist** for each kernel contract: contradictory fields; empty domains;
   zero-duration or zero-parameter witnesses (zero field, zero pressure, zero density, zero
   current, `D = 0`); unguarded division, square root, log or supremum (Lean's totalized `x / 0 =
   0`); hidden classical choices; missing bounds; wrong quantifier order (`∀ parameter, ∃ state`
   versus `∃ state, ∀ parameter`); unit or normalization errors (SI versus model units, Fourier and
   flux conventions, current orientation); accidental weakening; a hypothesis equivalent to the
   conclusion inside a law bundle.
4. **Statements match claims.** Check that exported theorems state the advertised model, domain,
   regularity, boundary conditions, norm, parameter range and time horizon, and whether solutions
   are constructed or supplied (for example `solovev_one_plasma_actual` supplies the transport
   solution). Trace important results back to kernel laws; do not accept a theorem merely because
   an over-strong hypothesis makes it easy.
5. **Note-to-code and code-to-note links.** Every established dependency in a note or the plan
   needs a matching named compiled declaration with compatible hypotheses; grep every cited name.
   Every advertised result (README, slides, progress) must match its declaration. Downgrade stale
   or unmatched claims.
6. **Checks run.** Build the affected modules one at a time within the laptop budget (≤ 6 GB per
   process; stale dependencies one at a time). For a startup or full audit, run `lake build` and
   `lake env lean scripts/check_axioms.lean` when the build budget permits, and
   `scripts/check_axioms_heavy.lean` for on-demand top modules that are built. On-demand modules
   follow the workstation policy (spot-checked; `workstation/REVIEWED.md`). Record exactly what
   ran, failures, warnings and resource limitations; do not claim a check that did not run.
7. **Audit record.** Record findings by severity, corrections, affected downstream results and
   the audited commit in the strict-audit table of `notes/implementation-plan.md`. An unresolved
   kernel finding blocks claims that depend on it.

After any kernel correction, re-run its sanity suite and re-audit all dependent public results.

## Maintain the domain architecture

1. Keep domain definitions and external model laws in a small `Kernel` layer.
2. Represent laws as predicates, structures or typeclasses with explicit fields. Pass law
   instances as hypotheses; never add a project axiom or an unproved universal instance.
3. Keep source-dependent material data and model-validity envelopes separate from mathematical
   consequences.
4. Prove sanity checks in `Sanity` and derived results in `Theory`.
5. Put coefficient decoding, interval checkers and candidate importers in `Certificates` or
   `Bridge`; keep heuristic solvers and oracles (`scripts/`) outside the trusted theorem path.

The repository has `[[lean_lib]] name = "PlasmaLean"` plus `PlasmaLeanMeta` (precompiled
untrusted `meta` builders). Add library targets only for a real dependency boundary. Provide module
documentation and docstrings for definitions and theorems; expose the public API with the module
system (`module`, `public section`, `@[expose]`).

## Audit each claim

Write its model, domain, boundary conditions, regularity, units, parameter range, perturbation
class, norm and time horizon. Classify it as:

- a definition;
- a supplied physical or empirical assumption (a law instance);
- a mathematical consequence to prove;
- a numerical observation;
- a proposed conjecture or research problem;
- a compiled theorem, with its declaration name, assumptions and build status (default or
  on-demand).

Keep equilibrium existence, field-line confinement, particle confinement, linear MHD stability,
nonlinear stability, transport and component feasibility as distinct predicates. Compose them only
through proved implications. Distinguish the domain-model kernel from Lean's logical kernel.

Check the note's dependency metadata, difficulty, barriers and readiness. If a prerequisite is not
formalized, formalize it first or keep it as an explicit conditional dependency; never promote the
dependent claim to verified. Add newly exposed gaps as `Q-*` or `N-*` entries rather than burying
them in a report.

## Challenge the inherited claims

Check the corrections in `00-model-contracts.md` and plan §1, and add new ones there. In
particular:

- Derive `B · ∇p = 0`; require compact, connected, orientable regular pressure surfaces and a
  nonvanishing tangent field before deducing torus topology. Do not infer a global foliation.
- Make Boozer coordinates a chart structure on a flux annulus with a checked Jacobian. Do not
  postulate nonsingular global angles across the magnetic axis.
- Distinguish `p = 0` from the additional condition `J = 0`.
- Treat the Garren–Boozer expansion as a source-specific compatibility result, not a universal
  impossibility theorem.
- Separate a Mercier or ballooning diagnostic from a full energy-principle certificate; name the
  supplied ballooning reduction.
- Require all-mode bounds before transferring finite-dimensional positivity to continuum
  stability.
- Treat KAM barriers and their hypotheses individually; do not claim that KAM supplies a complete
  foliation.
- Quasisymmetry of |B| is not a PDE symmetry (`quasisymmetry_not_pde_symmetry`).
- A pressure upper bound `p_thermal ≤ p_eq` is a budget, not force balance for the bounded
  pressure; an all-time bound for supplied solutions does not prove their existence.
- Positive measure in velocity space is not physical robustness unless the energy and pitch ranges
  are physically meaningful.
- Source engineering thresholds from the chosen machine and material instead of treating example
  distances as universal constants.

## Required and risk-specific sanity checks

For every new law or law bundle, prove the **sanity triad**:

- **degenerate case**: a limiting parameter where the law reduces to something elementary (zero
  field, uniform field, constant pressure, axisymmetry, zero current, zero heat source, collapsed
  uncertainty interval);
- **concrete instance**: an explicit model satisfying the law, so theorems about it are not vacuous
  (as `Sanity/BoschHaleInstance`, `Sanity/FilamentVacuum`);
- **counterexample**: an explicit object that fails the law, so the law has content (as
  `Sanity/ProbeEscape`, `Sanity/NeutralMode`).

The triad is only the baseline. For every kernel law or law bundle also require at least one
**risk-specific adversarial check** chosen from the actual hazards: singularity exclusion (the
magnetic axis, `R = 0`, vanishing `|B|`), boundary behaviour (degenerate axis, edge Dirichlet
data), symmetry or equivariance, conservation or monotonicity, dimensional scaling, parameter
endpoints, quantifier order, nonempty domains, or another independent characterization. Expect more
than one when the law has several hazards; never stop because a quota is met. **Add a compiled
regression theorem for every defect found during an audit.**

For each new definition also prove characterizing properties and a meaningful limiting case. For
each certificate format, an accepted and a rejected fixture. Diagnose inconsistent or vacuous
assumptions before proving further consequences.

## Deliver

- **Assumption ledger**: every law instance and supplied constant used by the claim, with its source
  and validity envelope.
- **Scope statement**: exactly what the compiled theorem says (model, quantifiers, norm, range,
  supplied solutions) and what it does not.
- Corrected definitions, compiled sanity and regression theorems, and the next theorem target
  (the smallest theorem that opens a useful next step).
- Updated note and goal/question dependencies, readiness and barriers.
- **Audit record** in the plan: audited commit, kernel inventory status, checks run, findings by
  severity, missing risk-specific sanity checks and downstream claims requiring re-audit.

Record unresolved physical assumptions explicitly. Never label the real device stable or confined
solely because a conditional formal theorem compiles.
