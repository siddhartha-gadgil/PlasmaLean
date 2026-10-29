# PlasmaLean

This is a library for Lean and AI-assisted mathematics towards design of a *stellerator* - a kind of fusion reactor where plasma can potentially be stable for extended times. The Lean code is organized into a *kernel*, which has the basic models, *sanity checks* for the kernel, proving which increases confidence in the correctness of the kernel, and a library with verified functions.

Besides the specific goals, this project is an experiment with using the power of modern AI systems with correctly designed Lean verification to address problems that are very useful, hard and mathematical in nature. Work produced and formalized by AI can be queried and understood, and ideas at various levels can be added to guide and spur development of theory and solutions.

Heavy numerics and large certificate builds can be offloaded to a workstation; see
[Workstation.md](Workstation.md).

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
both confinement and keeping the plasma hot. Ten phases are complete, and Phases 11, 14, 15 and 16 are in progress:

- **one field with a pressure-budget band:** one exact Solov'ev field satisfies force balance with
  the offset pressure p_eq + 40 kPa; 3.5 MeV alphas born in the core are confined for all time (full
  Lorentz orbits); and for *every* classical solution of the radial transport model that starts in a
  certified band, the core stays at or above 10 keV and the plasma pressure stays within the budget
  p ≤ p_eq + 40 kPa for all time. The existence of such a solution is assumed, not proved, and the
  thermal pressure is bounded by the budget, not equal to the force-balance pressure. This is proved on
  the equilibrium's own flux geometry (`solovev_one_plasma_actual`; with the coarea step derived,
  `solovev_one_plasma_actual_coarea`), at high Q (`solovev_one_plasma_highQ_actual`) and up to
  ignition with zero auxiliary heating and a 90 kPa offset (`solovev_one_plasma_ignited_actual`);
- **first stellarator field:** an exact non-axisymmetric vacuum field with two field periods and
  stellarator symmetry, whose magnetic axis is linearly elliptic and whose field lines near the
  axis are **confined for all time**: a verified explicit-constant KAM theorem produces an exact
  invariant torus around the axis, and every field line starting inside it stays inside forever
  (field lines proved to exist and be unique; vacuum model field); passing 3.5 MeV alpha guiding
  centres (μ = 0, either sign of v∥, Littlejohn model) are also confined for all time, for every
  B₀R₀ ∈ [67.95, 69.99] T·m, and with μ > 0 for every pitch parameter λ ∈ [0, 1/4] (the limit of the
  passing argument) at one energy and one B₀R₀;
  over the energy window |E − 3.5 MeV| ≤ 0.4 eV × λ ∈ [0, 1/16] the confined initial velocities
  form a set of positive measure in 3-D velocity space, but only in a narrow energy band and at one
  B₀R₀ (these heavy certificates are on-demand top modules, outside the default build);
- **coils:** a concrete set of closed polygonal coils produces a field whose lines near the axis
  are certified to stay confined for 52 toroidal transits;
- **finite β without axisymmetry:** an explicit finite-pressure, non-axisymmetric toroidal
  equilibria (Landreman families 1 and 2, the latter with proved shear; idealized) satisfy the
  kernel force balance; family 1 is Mercier-unstable, while family 2 at low β (λ = 200) has a
  certified Mercier-stable band of flux surfaces (flux labels derived from the field); its ideal
  ballooning stability is reduced exactly to one pointwise certificate and is numerically stable
  (tail margin ×2.36–×9.39 in pressure), but **no certificate has been found**;
- **stability:** Mercier stability and ideal-ballooning stability of the Solov'ev equilibrium are certified
  on every flux surface (with the standard reductions supplied);
- **near-quasisymmetric alphas:** passing alphas are held for 0.19 s;
- **burn windows** follow from the IPB98 and ISS04 scaling laws;
- **validation:** a slab Grad–Shafranov equilibrium with an exponential profile is validated;
- **screw pinch:** all-mode Newcomb stability is proved.

Heavy certificates are offloaded through a workstation pipeline (Phase 15) and re-checked on the
laptop before merging; on-demand results are spot-checked rather than rebuilt in full, and compiled
modules can be copied between machines; see [Workstation.md](Workstation.md). Kernel checks now peak
at 4.3 GB per process, within the 6 GB laptop target. Large checks are being rewritten as explicit
proof-term certificates (Phase 16): `decide +kernel` is down from about 28,700 uses to about 2,500
lines containing it (690 lines in the default build).

The library uses standard axioms only (no project axioms). See the
[progress slideshow](docs/slides.html) and the [latest report](progress/2026-10-26-progress-14.md).

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
scripts/                   Setup, axiom audit, website generation, oracles and workstation pipeline
```

## Getting started

On Linux or macOS, the idempotent setup script installs `elan` if needed (the Lean version is the
one pinned in `lean-toolchain`), fetches the Mathlib cache and builds the default library:

```sh
scripts/setup.sh --check-axioms     # also run the axiom audit
scripts/setup.sh --no-build         # only elan and the Mathlib cache
scripts/setup.sh --python --no-build && source .venv-ws/bin/activate   # Python for oracle scripts
```

The default build is large (several hundred certificate modules); keep each Lean process within
about 6 GB and build stale heavy modules one at a time (see
[scripts/README.md](scripts/README.md) and [Workstation.md](Workstation.md)).

## Working with agents

PlasmaLean develops theory as well as formalizing it while designing stellarators. The agent
skills (`.agents/skills/`, entry point `plasmalean-develop-theory`) understand a few conventions:

- **`start`**: the first command in a new or unfamiliar checkout. The agent strictly audits the
  existing code, especially every kernel declaration, records the audited commit and findings, and
  then summarizes the status and offers ready choices. No new theory is built on an unaudited
  foundation.
- **`status`**: goals, questions, the verified frontier, active and blocked notes, ready choices.
- **`work on G-…`, `Q-…`, `N-…`** or a topic: one coherent work unit on that item (literature,
  discovery, counterexample search, numerics, proof or Lean formalization), followed by an update of
  the notes and the plan.
- **`keep working`**: autonomous mode; the agent repeatedly picks the most valuable ready item and
  continues until a user decision is needed or nothing useful is ready.

The **research graph** lives in [notes/implementation-plan.md](notes/implementation-plan.md): goals
(`G-*`), questions (`Q-*`) and research notes (`N-*`, written with
[notes/note-template.md](notes/note-template.md)) with their dependencies, status and barriers.
**Lean is the validity gate**: a result counts as established only when a named Lean declaration
compiles with the standard axioms; sketches, sourced theorems and numerics stay explicitly
conditional. The workflow guards against two failure modes: **research drift** (long runs that
lose the motivating question, repeat abandoned approaches or silently change definitions) and
**validity drift** (a plausible argument, sampled computation or cited result treated as if it
had been checked under the exact hypotheses needed downstream).

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
