# PlasmaLean: Codex skills and mathematical development guides

Prepared on 10 October 2026 against [PlasmaLean](https://github.com/siddhartha-gadgil/PlasmaLean) commit `466920416e97561e4669759ab4077b9a23281ebd`. The package develops the architecture in [domain-libraries.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/466920416e97561e4669759ab4077b9a23281ebd/notes/domain-libraries.md) and the mathematical directions in [Stellerator.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/466920416e97561e4669759ab4077b9a23281ebd/notes/Stellerator.md).

The source snapshot contains starter Lean code. These files supply workflows, mathematical specifications, source leads, and a research program; the proposed theorems have not been implemented or compiled by this work.

## Start here

Read [model contracts](notes/formalization/00-model-contracts.md), then [the roadmap](notes/formalization/08-roadmap.md). Select one small theorem and use the relevant skill. The [literature guide](notes/formalization/09-literature.md) gives annotated primary entry points and a protocol for extracting exact hypotheses.

The first practical sequence is force-balance tangency and consistent examples; an abstract energy theorem; exact interval arithmetic; continuous clearance; an exact thermal margin; and Biot–Savart estimates. The roadmap extends this to finite-pressure equilibrium, all-mode stability, kinetic/exhaust bounds, components, uncertainty, and a common practical-design certificate.

## Codex skills

Each directory contains `SKILL.md` and `agents/openai.yaml`. Retain the directory structure when putting these files in the Codex skills location used by your environment. Paths named in a skill are resolved relative to the selected PlasmaLean checkout.

| Skill | Purpose | File |
| --- | --- | --- |
| `plasmalean-audit-domain` | Inspect the real kernel, classify assumptions, correct overbroad claims, and choose useful sanity theorems | [SKILL.md](.agents/skills/plasmalean-audit-domain/SKILL.md) |
| `plasmalean-formalize-theory` | Extract a source result and formalize it with explicit hypotheses and compiled checks | [SKILL.md](.agents/skills/plasmalean-formalize-theory/SKILL.md) |
| `plasmalean-discover-theory` | Develop new lemmas through proof, counterexample, refinement, and formalization | [SKILL.md](.agents/skills/plasmalean-discover-theory/SKILL.md) |
| `plasmalean-certify-numerics` | Build sound checkers with coverage, remainder, tail, coupling, and error bounds | [SKILL.md](.agents/skills/plasmalean-certify-numerics/SKILL.md) |
| `plasmalean-design-stellarator` | Advance a coil/plasma/component candidate through accurately named design milestones | [SKILL.md](.agents/skills/plasmalean-design-stellarator/SKILL.md) |
| `plasmalean-model-materials` | Model heat, stress, tape strain, magnets, quench, irradiation, fuel, and lifetime | [SKILL.md](.agents/skills/plasmalean-model-materials/SKILL.md) |

The skills follow the project's small kernel → sanity checks → derived theory architecture. They require physical laws and empirical data as explicit hypotheses, exact source extraction, meaningful instances/counterexamples, and a sound boundary between candidate generators and Lean proofs.

## Mathematics and models

Copy `notes/formalization/` into the corresponding repository directory so the skill references and note links retain their meaning.

| File | Scope |
| --- | --- |
| [00-model-contracts.md](notes/formalization/00-model-contracts.md) | Proof meanings, assumption ledger, architectural interfaces, corrections, and common-witness composition |
| [01-geometry-and-fields.md](notes/formalization/01-geometry-and-fields.md) | Pressure-surface topology, flux forms, Boozer charts, field-line maps, KAM, symmetry, near-axis theory |
| [02-plasma-models-and-equilibrium.md](notes/formalization/02-plasma-models-and-equilibrium.md) | Ideal/resistive/anisotropic/kinetic models, energy, fixed/free boundaries, smooth/weak/relaxed equilibrium |
| [03-mhd-stability.md](notes/formalization/03-mhd-stability.md) | Linearization, energy principle, useful inequalities, neutral modes, continuum spectrum, nonlinear targets |
| [04-particles-and-transport.md](notes/formalization/04-particles-and-transport.md) | Lorentz/guiding-centre motion, invariants, loss horizons, drift/gyrokinetics, profiles and fusion power |
| [05-verified-numerics.md](notes/formalization/05-verified-numerics.md) | Rational enclosures, continuous geometry, contraction, all-mode block bounds, KAM/ODE certificates |
| [06-coils-and-design.md](notes/formalization/06-coils-and-design.md) | Biot–Savart, finite conductors, plasma-current field, inverse design, geometry and manufacturing tolerances |
| [07-materials-and-engineering.md](notes/formalization/07-materials-and-engineering.md) | Thermal/mechanical laws, superconductors, quench, neutronics, breeding, damage, lifetime and maintenance |
| [08-roadmap.md](notes/formalization/08-roadmap.md) | Ten evidence gates, first modules, established theory, and eight ambitious research directions |
| [09-literature.md](notes/formalization/09-literature.md) | Annotated literature, official software/data entry points, corrigenda, extraction protocol and reading order |

Each topic includes concrete equations, hypotheses, useful early theorem targets, and a backlog. Engineering laws have validity envelopes and data-provenance requirements rather than universal invented material limits. The thermal note includes a synthetic exact parameter-box example for a first checker.

## Scientific scope

A positive sampled/discretized stability diagnostic does not establish a continuum lower bound. KAM tori do not establish all-particle confinement. Fixed-boundary ideal-MHD stability does not supply free-boundary, nonlinear, or kinetic stability. Practical feasibility requires the specified contracts to hold for the same equilibrium, geometry, material state, and uncertainty parameters.

The roadmap distinguishes formalizing established mathematics, developing numerical validation, and proposing new research. Research directions include constructive nonaxisymmetric finite-pressure equilibria, all-mode/free-boundary stability, nonlinear control and continuation, imperfect-symmetry confinement, kinetic heat-flux bounds, controlled reductions, coupled lifetime envelopes, and scalable proof certificates.
