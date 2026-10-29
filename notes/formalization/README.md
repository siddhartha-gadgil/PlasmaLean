# notes/formalization/

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
