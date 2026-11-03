---
name: plasmalean-design-stellarator
description: Advance a PlasmaLean stellarator candidate from a mathematical specification toward a constructible design with composed proof certificates. Use for coil or boundary optimization, design tradeoffs, operating envelopes, tolerance studies, or deciding which verified milestone a candidate has reached.
---

# Design against explicit contracts

Read `notes/formalization/00-model-contracts.md`, `06-coils-and-design.md`, `07-materials-and-engineering.md`, `08-roadmap.md`, `notes/design/vacuum-demonstrator.md` and the "Research graph" part of `notes/implementation-plan.md` (model ladder M0–M6 in §5). Inspect the actual implemented kernel, theory, bridge and certificate modules (`PlasmaLean/Design/README.md` lists the design families and on-demand top modules) before describing a capability as available.

## Place the design in the research graph

Every design task serves registered goals and questions. Record which `G-*` it advances (G-1 confinement and stability, G-2 thermal performance, and the more specific design goals), which `Q-*` it answers or depends on, and which `N-*` notes supply its theory. When a gate needs mathematics that does not exist, open a `Q-*`/`N-*` entry and route it to `plasmalean-discover-theory` instead of pushing a larger computation: the project builds theory while designing.

**Never treat an unformalized note as established.** A sourced theorem, an informal proof in `notes/theory/`, a numerical scan or an optimizer result can guide the search, but a design claim may rest only on compiled declarations (default build, or on-demand modules under the workstation policy) and on explicitly named law instances and supplied reductions. Anything else stays a conditional or open item in the design record.

## Freeze a design specification

Record the intended machine class, plasma species, major/minor scale, pressure/density/temperature profiles, magnetic-field range, heating and exhaust, duty cycle, perturbation class, manufacturing tolerances, and component data. Source numerical requirements from a named experiment, reactor study, or material characterization. Use a symbolic envelope until such data exist; do not inherit the illustrative distances in `notes/Stellerator.md` as universal limits.

Record fixed/free plasma boundary, conducting/resistive wall, coil-current model, finite conductor geometry, maintenance access, and shielding/blanket budget. Treat transport and stability targets separately. Permit quasi-isodynamic/omnigenous designs as well as quasisymmetric designs.

## Name the verification level

Name the level a candidate has reached precisely; never round up. This generic ladder from the
LeanTheory template complements the roadmap gates P0–P9 (`08-roadmap.md`) and the contract clauses
C1–C5. A candidate may be at different levels for different clauses.

| Level | Meaning | Evidence |
| --- | --- | --- |
| L0 Specification | the design problem is stated as Lean predicates on decoded parameters | `Design/` definitions with docstrings; the sanity triad for the laws used |
| L1 Candidate | a concrete candidate exists with exact (rational) data and provenance | data `def`s; source commit, solver and version; data hash (e.g. `DommaschkQA2R.candidate`, from the recorded workstation run) |
| L2 Pointwise certificate | the target properties hold at the nominal candidate | kernel-checked certificates (`plasmalean-certify-numerics`) |
| L3 Envelope certificate | they hold for every state in the operating envelope or every member of a family | coverage plus between-sample bounds, or a family certificate (e.g. every B₀R₀ in an interval) |
| L4 Robust certificate | they hold with margins over the whole tolerance set | margins propagated through every certificate, with the same uncertainty parameters |
| L5 Composed design theorem | one theorem in `Design/` concludes all target predicates for the candidate from the stated law instances only | `#print axioms` clean; listed in `scripts/check_axioms.lean` or `check_axioms_heavy.lean` |

Example: the Dommaschk field is at L2 for C1 and for the vacuum Q-16 criterion, on two certified
tori (`DommaschkKamQ16.dommaschk_Q16_vacuum`). It is at L0 at most for C2, and unaddressed for C3
and C5.

## Explore, then certify

1. Choose the next achievable gate in `08-roadmap.md`.
2. Parameterize axis, surfaces, coils, currents, tape orientation, and operating profiles with explicit units and symmetry conventions.
3. Use theory to reduce the search space and derive sufficient conditions. Use SIMSOPT, DESC, VMEC, SPEC, or another documented solver as a candidate generator appropriate to the model.
4. Check implementation/version-specific conventions. Keep nested-surface and island/stepped-pressure models distinct; supply the finite-pressure plasma-current field when mapping coils to equilibrium.
5. Optimize physically meaningful objectives and retain hard constraints separately. An objective penalty or its optimum is not a proof of feasibility.
6. Generate and check the exact geometric, equilibrium, stability, orbit, thermal, stress, magnet, and lifetime certificates needed at the selected gate.
7. Propagate manufacturing and operating uncertainty through margins. Recompute dependent certificates after any geometry, profile, data, or model change.
8. Use the workstation (`Workstation.md`, task scripts in `scripts/workstation/tasks/`) when a step needs heavy numerics or a first build would exceed the laptop budget (6 GB per Lean process; stale dependencies built one at a time). Heavy families can be on-demand top modules not imported by `PlasmaLean.lean`; bring results back with `plasmalean-workstation-update`.

Do not require a proof of global optimality to certify one useful feasible design. Claim an optimum only with a separate optimality certificate.

## Compose results without changing quantifiers

Ensure all certificates refer to the same decoded geometry, fields, profiles, material state, operating interval, and uncertainty parameters. Preserve correlations between inputs. Compose implications only when one theorem's conclusion supplies the next theorem's hypotheses in the correct norm.

Distinguish `∀ parameter, ∃ nearby equilibrium` from one state valid for every parameter. Distinguish fixed-boundary linear stability from free-boundary stability and from nonlinear or kinetic claims. Use a design record containing the exact predicates proved and their evidence rather than a single ambiguous `Stable` flag.

## Tradeoff and tolerance studies

- State tradeoffs as families: a certified bound as a function of the design parameter, certified on
  boxes covering the range, rather than a few sampled points.
- For tolerances, certify the property on the whole uncertainty box and report the margin. Report
  the largest box you could certify, not the one you hoped for.
- A failure to certify is an open item, not evidence that the design fails; an exact
  counterexample is.

## Deliver a usable milestone

Provide the candidate coefficients and provenance, compiled declaration names, quantitative margins, remaining physical-law assumptions, missing certificates, model-validity evidence, and the next experiment or theoretical target. For a reactor-scale design also account for blanket/tritium, neutron damage, cryogenics, quench, power balance, and maintenance. Name the achieved gate accurately; a vacuum-field demonstration is a useful first gate.

A milestone is done when its certificates compile with zero warnings, no `sorry`/axiom/`decide` and only standard axioms (`scripts/check_axioms.lean`, or `scripts/check_axioms_heavy.lean` for on-demand modules); accepted and rejected fixtures exist; an assumption ledger and scope statement exist (`plasmalean-audit-domain`); and the affected `G-*`/`Q-*`/`N-*` entries and a dated §13 entry in `notes/implementation-plan.md` record the gate reached, declaration names, margins, build cost, missing certificates and the next target. Update the plan also when the attempt fails.

## Finish the stage

After each completed stage of progress (including a recorded failure or barrier), follow the reporting
protocol in `notes/domain-libraries.md`: update the notes and plan registries, refresh
`progress/slideshow.json` (and the progress report when substantive), regenerate and check the site
(`node scripts/generate_handbook.mjs`, `node scripts/check_site.mjs`), then commit with explicitly
staged paths and `git push`.
