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
between theory, certificate techniques and a ladder of successively realistic models, and targets
both confinement and keeping the plasma hot. Its Phase 1 is complete: a reactor-scale 0-D D-T
plasma (with fuel dilution) provably stays at or above 10 keV for all time under supplied Bosch–Hale
data and stated confinement-time hypotheses. Phase 1 also proved a comparison principle for radial
heat transport and the vacuum maximum principle (field errors are bounded by their boundary
values). The library has 67 modules and 2383 audited declarations, using standard axioms only. See
the [progress slideshow](docs/slides.html) and the [latest report](progress/2026-10-20-progress-2.md).

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
