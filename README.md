# PlasmaLean

This is a library for Lean and AI-assisted mathematics toward verified stellarator design.

## Progress

The latest checked run (12 October 2026) has 32 Lean modules, 175 source theorems
(including private helpers), and 448 audited project declarations. Reusable
equilibrium, energy, geometry, field and exact-certificate results now support a
two-coil vacuum calibration fixture with continuous field derivatives,
manufacturing/current error bounds, a nonzero probe field and tube clearance.
This is **partial P2**, not a practical stellarator or a confinement certificate.
Finite conductors, a nonaxisymmetric candidate and sourced hardware data remain
ahead. See the [progress slideshow](docs/slides.html) and
[checked results and assumptions](progress/2026-10-12-progress-2.md).

## Code structure

```text
PlasmaLean.lean             Public library imports
PlasmaLean/
  Kernel/                  Explicit model definitions and laws
  Sanity/                  Consistent examples and counterchecks
  Theory/                  Geometry, fields, equilibrium, stability, kinetic and engineering results
  Certificates/            Exact arithmetic and proved numerical checkers
  Bridge/                  Common-candidate and witness contracts
  Design/                  Synthetic examples and vacuum-fixture certificates
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
