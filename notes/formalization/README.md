# notes/formalization/

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-24` |
| Title | Formalization specifications 00–09: model contracts and topic specifications |
| Kind | formalization (specifications; 00 model contracts is normative) |
| Addresses | all goals; `G-11`, `Q-21`; evidence gates P0–P9 (08) |
| Depends on | sources in 09 (extraction protocol); the implementation plan and `progress/` for what is compiled |
| Dependency requirement | none for the specifications; a theorem may cite a contract only once its Lean definition and sanity triad exist |
| Produces | the contract predicates (C1–C5 and the model hierarchy, 00); topic specifications and task lists (01–07); evidence gates and research problems R1–R8 (08); literature and reading order (09) |
| Difficulty | varies by chapter; the C1/C2 definitions were moderate, ε_eff (Nemov et al. 1999) and C5 as a contract are open |
| Status | stated (active specifications; 00 normative, updated for C1/C2 on 30 October and AC-1 on 2 November); C1 and C2 definitions verified in Lean; ε_eff and C5 not in Lean; chapters 01–09 are 12 October planning text |
| Lean evidence | C1: `Theory/Contract/StellaratorContract` (`CurrentFreeTransform`, `netToroidalCurrent`, `IotaOnTorus`, `iota_eq_zero_of_purelyToroidal`, `not_currentFreeTransform_of_purelyToroidal`); C2: `Theory/Contract/BoozerModel` (`OmnigeneityContract`), `Theory/Kinetic/Omnigeneity` (`OmnigenousOn`, `ApproxOmnigenousOn`, `bounceAvgDrift`); composition `Bridge/Contracts`; witness `Design/RationalStellaratorContract.rationalStellarator_currentFreeTransform`; all default build. Planned, not present: `EffectiveRippleBound`, `ThermalPerformance`, a `StellaratorContract` record; `BounceAveragedDrift` and `Omnigenous` exist as `bounceAvgDrift` and `OmnigenousOn` |
| Audit evidence | 30 October docs audit: chapters 01–09 unchanged since 12 October, 66 of 119 task entries say "Planning only" although several are partly done; per-chapter contract updates listed (01 C1/C2, 02 Solov'ev as tokamak, 03 C3, 04 omnigeneity, 08 gates to C1–C5). 31 October refresh audit AR-M5: the "1.5 μs" horizon in 04 is r₀/285000 s. 2 November AC-1: C2 tied to the physical field |
| Last updated | 3 November 2026: metadata added (the chapters themselves unchanged) |

**Current state (3 November 2026).** 00 is current (C1 and C2 in Lean, C2 tied to the physical field by AC-1). Chapters 01–09 keep their 12 October planning context: their progress strings predate the contract and the Dommaschk results (C1 on nested certified tori and a certified QA defect, N-33–N-35, on demand), so the plan's RG.1–RG.3 and §13 are authoritative for status.

Formalization specifications: what a PlasmaLean theorem may claim, and the planned Lean interfaces
for each part of the domain. Most of these notes are published as handbook pages.

| Note | Content |
| --- | --- |
| [`00-model-contracts.md`](00-model-contracts.md) | Normative: separate contract predicates instead of one vague "stable", the origin of each assumption, corrections to loose claims, the model hierarchy, composition with a common witness |
| [`01-geometry-and-fields.md`](01-geometry-and-fields.md) | Pressure surfaces, flux coordinates, field-line dynamics, quasisymmetry, near-axis theory |
| [`02-plasma-models-and-equilibrium.md`](02-plasma-models-and-equilibrium.md) | Ideal MHD, static and weak equilibria, boundary conditions, model reductions |
| [`03-mhd-stability.md`](03-mhd-stability.md) | Energy principles, continuum operators, neutral modes, honest stability certificates |
| [`04-particles-and-transport.md`](04-particles-and-transport.md) | Full and reduced orbits, confinement horizons, kinetic transport, reactor profiles |
| [`05-verified-numerics.md`](05-verified-numerics.md) | Exact inputs, continuous bounds, equilibrium validation, certificate identity |
| [`06-coils-and-design.md`](06-coils-and-design.md) | Biot–Savart fields, inverse coil design, manufacturing geometry, robust workflows |
| [`07-materials-and-engineering.md`](07-materials-and-engineering.md) | Heat, stress, magnets, quench, neutronics, lifetime, power, maintenance |
| [`08-roadmap.md`](08-roadmap.md) | Evidence gates P0–P9, the first coding sequence, research problems R1–R8 |
| [`09-literature.md`](09-literature.md) | Primary sources, the extraction protocol, software roles, theorem reading order |

These notes keep their original planning context; the implementation plan and `progress/` record
what is compiled. Open discovery work lives in `notes/theory/`; a result moves into this track
when its statement, proof and prerequisites are ready. Link items by their `G-*`/`Q-*`/`N-*` IDs.
