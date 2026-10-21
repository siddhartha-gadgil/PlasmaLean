# PlasmaLean

This is a library for Lean and AI-assisted mathematics towards design of a *stellerator* - a kind of fusion reactor where plasma can potentially be stable for extended times. The Lean code is organized into a *kernel*, which has the basic models, *sanity checks* for the kernel, proving which increases confidence in the correctness of the kernel, and a library with verified functions.

Besides the specific goals, this project is an experiment with using the power of modern AI systems with correctly designed Lean verification to address problems that are very useful, hard and mathematical in nature. Work produced and formalized by AI can be queried and understood, and ideas at various levels can be added to guide and spur development of theory and solutions.

## Progress

The latest checked results (14 October 2026) are source-free Maxwell identities for closed
filament fields; the Suydam interchange criterion in both directions; Newcomb/Riccati
stability certificates discharged by an exact polynomial checker; and two exact
finite-pressure equilibria (toroidal Solov'ev, and a nonaxisymmetric helically symmetric
one at 5 T and 4% β) verified against the kernel force-balance law, with all-time
full-orbit confinement theorems via Noether's canonical momentum. These are idealized
symmetric models: no coil-produced stellarator, all-mode MHD stability or 3.5 MeV alpha
confinement is certified.

On 20 October an [implementation plan](notes/implementation-plan.md) was fixed. It cycles
between theory, certificate techniques and a ladder of successively realistic models, targeting
both confinement and keeping the plasma hot. Ten phases are complete:

- **one consistent plasma:** for one exact Solov'ev field satisfying force balance, 3.5 MeV alphas
  born in the core are confined for all time, the core stays at or above 10 keV for all time, and
  the plasma pressure stays below the equilibrium pressure. This holds on the equilibrium's own
  flux geometry (fully derived, including the coarea step) and up to ignition (zero auxiliary heating, with
  a larger edge-pressure offset);
- **first stellarator field:** an exact non-axisymmetric vacuum field with two field periods and
  stellarator symmetry, whose magnetic axis is linearly elliptic and whose field lines near the
  axis are **confined for all time**: a verified explicit-constant KAM theorem produces an exact
  invariant torus around the axis, and every field line starting inside it stays inside forever
  (field lines proved to exist and be unique; vacuum model field); passing 3.5 MeV alpha guiding
  centres (μ = 0, either sign of v∥, one exact B₀R₀ ≈ 69 T·m, Littlejohn model) are also confined for all time
  — a measure-zero set of alphas, not alpha confinement in general;
- **coils:** a concrete set of closed polygonal coils produces a field whose lines near the axis
  are certified to stay confined for 52 toroidal transits;
- **finite β without axisymmetry:** an explicit finite-pressure, non-axisymmetric toroidal
  equilibria (Landreman families 1 and 2, the latter with proved shear; idealized) satisfy the
  kernel force balance, but are Mercier-unstable (family 1 proved, family 2 numerically);
- **stability:** Mercier stability and ideal-ballooning stability of that equilibrium are certified
  on every flux surface (with the standard reductions supplied);
- **near-quasisymmetric alphas:** passing alphas are held for 0.19 s;
- **burn windows** follow from the IPB98 and ISS04 scaling laws;
- **validation:** a slab Grad–Shafranov equilibrium with an exponential profile is validated;
- **screw pinch:** all-mode Newcomb stability is proved.

The library has 371 modules and 33964 audited declarations, using standard axioms only. See the
[progress slideshow](docs/slides.html) and the [latest report](progress/2026-10-21-progress-9.md).

## Code structure

```text
PlasmaLean.lean             Public library imports
PlasmaLean/
  Kernel/                  Explicit model definitions and laws
  Sanity/                  Consistent examples and counterchecks
  Theory/                  Geometry, fields, equilibrium, stability, kinetic and engineering results
  Certificates/            Exact arithmetic and proved numerical checkers
  Bridge/                  Common-candidate and witness contracts
  Design/                  Vacuum fixture, exact equilibria and confinement/stability examples
notes/                     Design basis and formalization plans
progress/                  Dated evidence, task status and slideshow content
docs/                      Static website, illustrated landing page and slides
scripts/                   Axiom audit, website generation and regression checks
```

## Build and audit

Lean and Mathlib are pinned to v4.34.1. From the repository root:

```sh
lake build
lake env lean scripts/check_axioms.lean
node scripts/generate_handbook.mjs
node scripts/check_site.mjs
```

Import `PlasmaLean` for the public library, or a specific module.
Model laws are hypotheses, not new axioms. The audit rejects
unexpected logical axioms in every declaration owned by a project module.

## Read the program

The [website](docs/index.html) retains the original motivations and interactive
graphics and links to the [slideshow](docs/slides.html),
[handbook](docs/handbook.html) and task progress. Source
plans live in [notes/domain-libraries.md](notes/domain-libraries.md) and
[notes/formalization/](notes/formalization/08-roadmap.md). They retain their original
planning context; the dated progress ledger identifies subsequent compiled work.

After each run, refresh [progress/slideshow.json](progress/slideshow.json) alongside
the report and task status, then regenerate and check the site with the commands
above. The slides support keyboard navigation, a read-all view and printing.

## Contributions

I, Siddhartha Gadgil, am the maintainer of this repository. I am on the faculty of the Indian Institute of Science, and also (currently) a chief scientist at [Emergence Research](https://east.emergence.ai/). Emergence has generously sponsored tokens for building the code in this site. I also have support from [Renaissance Philanthropy](https://east.emergence.ai/).
