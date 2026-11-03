# PlasmaLean

This is a library for Lean and AI-assisted mathematics towards the design of a *stellarator*, a
kind of fusion reactor in which the plasma can potentially be stable for extended times. The Lean
code is organized into a *kernel*, which has the basic models, *sanity checks* for the kernel,
proving which increases confidence in the correctness of the kernel, and a library with verified
functions.

**The aim: the stellarator contract** (adopted 30 October 2026). Tokamaks confine plasma with a large
toroidal plasma current, which brings current-driven instabilities, disruptions and the need for
current drive; that is why stellarators exist. So the goal is not merely a "non-axisymmetric" or
"non-tokamak" solution, but a candidate with the properties a stellarator needs, which rule out
tokamaks and are achievable by stellarators:

- **C1, current-free rotational transform:** net toroidal plasma current zero or at most a stated
  bootstrap-level bound (a vacuum field is the limiting case), with rotational transform
  ι ≥ ι_min > 0 provided by the external field. An axisymmetric current-free field has ι = 0, so C1
  excludes tokamaks.
- **C2, omnigeneity:** small neoclassical transport for *thermal* ions and electrons (not only
  alphas): the bounce-averaged radial drift of trapped particles vanishes or is bounded, or the
  effective ripple ε_eff is bounded. Quasisymmetric and quasi-isodynamic fields are special cases.
- **C3, MHD stability at finite β:** Mercier, ballooning and interchange; current-driven modes are
  absent by C1.
- **C4, existence:** nested flux surfaces (certified invariant tori) and force balance.
- **C5, thermal performance:** on the *same* candidate, the core stays above a burn temperature
  (e.g. 10 keV) over the operating interval and below wall limits, from power balance with alpha
  heating, bremsstrahlung and transport losses; neoclassical losses come from C2, and anomalous
  transport is a stated, supplied scaling. Poor omnigeneity can make burn inaccessible.

Non-axisymmetry is a consequence of these clauses, not a goal. The contract is stated precisely in
the [implementation plan](notes/implementation-plan.md) and as model contracts in
[notes/formalization/00-model-contracts.md](notes/formalization/00-model-contracts.md).

Besides the specific goals, this project is an experiment with using the power of modern AI systems with correctly designed Lean verification to address problems that are very useful, hard and mathematical in nature. Work produced and formalized by AI can be queried and understood, and ideas at various levels can be added to guide and spur development of theory and solutions.

Heavy numerics and large certificate builds can be offloaded to a workstation; see
[Workstation.md](Workstation.md).

## Progress

**Against the contract (3 November 2026), honestly:** one stellarator candidate now has verified
C1 together with a certified quasisymmetry defect, in vacuum. C2–C5 are open for it.

- **The lead candidate: an exact Dommaschk quasi-axisymmetric vacuum field.** It is a purely
  rational field with two field periods (`Design/DommaschkQA2R`). It was found by untrusted
  workstation numerics and then certified in Lean through on-demand modules, standard axioms only
  ([N-31](notes/theory/dommaschk-qa.md), [N-33](notes/theory/dommaschk-kam-certificate.md),
  [N-34](notes/theory/dommaschk-qs-defect.md)). Main theorem:
  `DommaschkKamQ16.dommaschk_Q16_vacuum`.
  - **Exact field:** a vacuum field, `DommaschkQA2R.candidate_vacuum`, in the default build.
  - **Certified tori:** two exact invariant tori C and A, with ι_C = −(85+√5)/361 and
    ι_A = −(19+√5)/89, from an a posteriori KAM theorem applied to 96 × 80 Fourier tori. The tori
    are proved nested (`DommaschkKamNested.dommaschk_nested`).
  - **C1:** zero net toroidal current and |ι| ≥ 0.2386 on both tori
    (`DommaschkKamNested.dommaschk_nested_C1`).
  - **Quasi-axisymmetry:** on both tori the off-QA Boozer spectral defect is certified at
    ≤ 0.0063 |ι| (C) and ≤ 0.0090 |ι| (A), the strong tier. This meets the decided vacuum criterion
    of question Q-16 on a nested pair.
  - **Not proved:** confinement of field lines inside the tori, more than two surfaces (an exact
    continuum is impossible for this non-integrable field), C2 (no Boozer chart of the field over a
    volume, see audit AC-1), and finite β, C3 and C5.
- **C1 elsewhere:** the earlier rational stellarator vacuum field has a KAM-certified torus with
  ι ≈ 0.137 that confines its field lines for all time. The C1 current is the Ampère circulation
  μ₀⁻¹∮B·dl around each torus's own poloidal loop; this is audit fix AR-H1, since an earlier
  section-based clause could be satisfied vacuously. Landreman family 2 fails C1
  (`family2_not_currentFreeTransform`).
- **C2:**
  - **Contract:** since audit fix AC-1, C2 is a property of the physical field. It requires a proved
    Boozer chart (`Contract.BoozerModelOf`); the only field-level instance so far is the vacuous
    ∇φ fixture.
  - **The bridge:** in the Boozer guiding-centre model, quasisymmetry implies omnigeneity, exactly
    and with a per-bounce defect bound (`omnigenousOn_of_exactQS`, `approxOmnigenousOn_of_defect_le`).
    The `exactQA`/`reactorQA` results are statements about a supplied Boozer model.
  - **Not in Lean:** ε_eff.
  - **Alphas:** the alpha results below concern 3.5 MeV alphas, mostly passing orbits, which is at
    most one part of C2.
- **C3 (test beds only):** Mercier stability on a band of Landreman family 2 (current-carrying),
  and Mercier and ballooning stability of a Solov'ev tokamak equilibrium. Nothing for a current-free
  equilibrium.
- **C4:** the vacuum fields inside their certified tori. Finite-β exact equilibria exist only for
  symmetric models and the current-carrying Landreman families.
- **C5 (tokamak model and 0-D only):** a burn-temperature band holds on a Solov'ev (tokamak) field
  for every *supplied* transport solution. On stellarator parameters there are only 0-D windows and
  proved obstructions at measured confinement factors.

The next priorities (choices for the maintainer):
- C2 for the actual field: an approximate Boozer chart with a certified defect, or another route;
- ε_eff in Lean;
- a current-free finite-β equilibrium near the certified vacuum tori.

The earliest checked results (14 October 2026) are source-free Maxwell identities for closed
filament fields; the Suydam interchange criterion in both directions; Newcomb/Riccati
stability certificates discharged by an exact polynomial checker; and two exact
finite-pressure equilibria (toroidal Solov'ev, and a nonaxisymmetric helically symmetric
one at 5 T and 4% β) verified against the kernel force-balance law, with all-time
full-orbit confinement theorems via Noether's canonical momentum. These are idealized
symmetric models: no coil-produced stellarator, all-mode MHD stability or 3.5 MeV alpha
confinement is certified.

On 20 October an [implementation plan](notes/implementation-plan.md) was fixed. It cycles
between theory, certificate techniques and a ladder of successively realistic models, targeting
both confinement and keeping the plasma hot. Ten phases are complete, and Phases 11, 14, 15 and 16 are in progress. Since 30 October the work has
been organized by the stellarator contract and the research graph (below), which led to the Dommaschk
certification above. The earlier results by topic, with their role under the contract:

- **one field with a pressure-budget band (a tokamak model for C5, not a candidate):** one exact Solov'ev field satisfies force balance with
  the offset pressure p_eq + 40 kPa; every 3.5 MeV alpha orbit born in the core stays confined for all time
  (full Lorentz orbits; such orbits are proved to exist for all time from every admissible birth
  point, `reactor_alpha_born_confined`); and for *every* classical solution of the radial transport model that starts in a
  certified band, the core stays at or above 10 keV and the plasma pressure stays within the budget
  p ≤ p_eq + 40 kPa for all time. The existence of such a solution is assumed, not proved, and the
  thermal pressure is bounded by the budget, not equal to the force-balance pressure. This is proved on
  the equilibrium's own flux geometry (`solovev_one_plasma_actual`; with the coarea step derived,
  `solovev_one_plasma_actual_coarea`), at high Q (`solovev_one_plasma_highQ_actual`) and up to
  ignition with zero auxiliary heating and a 90 kPa offset (`solovev_one_plasma_ignited_actual`);
- **first stellarator field (C1 and C4 in vacuum; C2 unknown):** an exact non-axisymmetric vacuum field with two field periods and
  stellarator symmetry, whose magnetic axis is linearly elliptic and whose field lines near the
  axis are **confined for all time**: a verified explicit-constant KAM theorem produces an exact
  invariant torus around the axis, and every field line starting inside it stays inside forever
  (field lines proved to exist and be unique; vacuum model field); passing 3.5 MeV alpha guiding
  centres (μ = 0, Littlejohn model) are also confined for all time: with v∥ > 0 for every
  B₀R₀ ∈ [67.95, 69.99] T·m, with v∥ < 0 at the design B₀R₀, and with μ > 0 for every pitch parameter λ ∈ [0, 1/4] (the limit of the
  passing argument) at one energy and one B₀R₀;
  over the energy window |E − 3.5 MeV| ≤ 0.4 eV × λ ∈ [0, 1/16] the confined initial velocities
  form a set of positive measure in 3-D velocity space, but only in a narrow energy band and at one
  B₀R₀ (these heavy certificates are on-demand top modules, outside the default build);
- **coils:** a concrete set of closed polygonal coils produces a field whose lines near the axis
  are certified to stay confined for 52 toroidal transits (field-line existence assumed; the
  toroidal-field return conductor is idealized, placed at 10⁶ R₀);
- **finite β without axisymmetry (C3/C4 test beds; they carry net toroidal current, so not
  current-free):** explicit finite-pressure, non-axisymmetric toroidal
  equilibria (Landreman families 1 and 2, the latter with proved shear; idealized) satisfy the
  kernel force balance; family 1 satisfies in Lean the hypotheses of a Grad counterexample in the formulation of
  Cardona et al. (Conjecture 2.5): smooth MHS, toroidal level sets, non-constant pressure, no continuous
  Euclidean symmetry. All its field lines are closed (ι ≡ 2), so it is non-generic. This is mathematical
  infrastructure, not design progress. Neither family is weakly quasisymmetric on a region containing its
  magnetic axis; family 1 is Mercier-unstable, while family 2 at low β (λ = 200) has a
  certified Mercier-stable band of flux surfaces (flux labels derived from the field; the
  Landreman–Jorge Mercier formula is supplied); its ideal
  ballooning stability is reduced exactly to one pointwise certificate and is numerically stable
  (tail margin ×2.36–×9.39 in pressure), but **no certificate has been found**;
- **stability (tokamak model):** Mercier stability and ideal-ballooning stability of the Solov'ev equilibrium are certified
  on every flux surface (with the standard reductions supplied);
- **near-quasisymmetric alphas:** passing alphas are held for 0.19 s (orbits away from the magnetic axis);
- **burn windows** follow from the IPB98 and ISS04 scaling laws;
- **validation:** a slab Grad–Shafranov equilibrium with an exponential profile is validated;
- **screw pinch:** Newcomb stability is proved for every mode with m ≠ 0 (Newcomb's reduced
  form of δW is supplied).

Heavy certificates are offloaded through a workstation pipeline (Phase 15) and re-checked on the
laptop before merging; on-demand results are spot-checked rather than rebuilt in full, and compiled
modules can be copied between machines; see [Workstation.md](Workstation.md). The KAM certificate checks
peak at 4.3 GB per process; the one module that exceeded the 6 GB laptop target
(`LandremanFamily2MercierStable`, 6.17–6.74 GB) is now split into parts peaking at most 2.74 GB, so every
module with a recorded peak is within the target (the four `NearAxisQAAveraged` parts have no
recorded individual peaks). Large checks are being rewritten as explicit
proof-term certificates (Phase 16): `decide +kernel` is down from about 28,700 uses to 1,971
lines containing it (130 lines in the default build, after the Landreman outer arcs were converted).

The library uses standard axioms only (no project axioms). See the
[progress slideshow](docs/slides.html) and the [latest report](progress/2026-10-30-progress-15.md).

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
notes/                     Plan, research notes and specifications (see "Notes and the research graph")
  implementation-plan.md   Plan of record: the contract, the research graph (goals, questions, notes),
                           audit status, work selection, dated logs
  theory/                  Research notes N-*, one file each, indexed in theory/README.md
  formalization/           Model contracts (00, normative) and topic specifications 01–09
  audit/                   Strict audit records with finding IDs
  goals/                   How to state goals (method.md); goal proposals N-22
  design/                  Design notes (vacuum demonstrator, N-23)
  note-template.md         Template every research note follows
progress/                  Dated evidence, task status and slideshow content
docs/                      Static website, slides, and GettingStarted.md (the workflow)
scripts/                   Setup, axiom audit, website generation, oracles and workstation pipeline
.agents/skills/            Agent skills (`.claude` is a symlink to `.agents`)
```

## Getting started

The workflow for users and agents (the [LeanTheory](https://github.com/siddhartha-gadgil/LeanTheory)
method, which was extracted from this project, with the stellarator domain filled in) is described in
[docs/GettingStarted.md](docs/GettingStarted.md): the project graph, the architecture, a work unit
from setup to the validity gate, the ways to interact, and copy-paste prompts for agents.

On Linux or macOS, the idempotent setup script installs `elan` if needed (the Lean version is the
one pinned in `lean-toolchain`), fetches the Mathlib cache and builds the default library:

```sh
scripts/setup.sh --check-axioms     # also run the axiom audit
scripts/setup.sh --no-build         # only elan and the Mathlib cache
scripts/setup.sh --python --no-build && source .venv-ws/bin/activate   # Python for oracle scripts
```

Request the Python environment only when a task needs it, and activate `.venv-ws` in every new shell
rather than installing project packages globally.

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
- **`work status`** (or **`summarise work`** / **`summarize work`**): goals, questions, the verified frontier, active and blocked notes, ready choices.
- **`work on G-…`, `Q-…`, `N-…`** or a topic: one coherent work unit on that item (literature,
  discovery, counterexample search, numerics, proof or Lean formalization), followed by an update of
  the notes and the plan.
- **`keep working`**: autonomous mode; the agent repeatedly picks the most valuable ready item and
  continues until a user decision is needed or nothing useful is ready.
- **`add a note`** (or **`make a note`**, **`record this`**): record the outcome of a discussion, result,
  failure, source assessment or design decision as a registered research note (skill
  `plasmalean-add-note`), or update an existing note to its current state.
- **`update notes`** (or **`modify notes`**, **`add notes`**): change what the notes say. The agent surveys the notes
  and their metadata, edits in place only notes with no Lean implementation, and records every
  other change as a new note: a *method note* for an additional approach, or a *patch note* for a
  change to a wholly or partially implemented note (skill `plasmalean-modify-notes`).
- **`update notes from <files>`**: the same, with the changes coming from given theory sources
  (papers, a colleague's brief, drafts, Lean files from elsewhere). The agent reads them in full,
  extracts each claim with its kind and locator, checks it against the compiled Lean code and the
  notes (re-deriving explicit formulas where cheap), records a source-assessment note, and then
  updates the notes by the same rule (skill `plasmalean-update-notes-from`).
- **`update from workstation`**: review, re-check and merge workstation runs (skill
  `plasmalean-workstation-update`); the workstation can run an unattended poller that executes the
  commands the laptop queues in `scripts/workstation/next.sh`.

The **research graph** lives in [notes/implementation-plan.md](notes/implementation-plan.md): goals
(`G-*`), questions (`Q-*`) and research notes (`N-*`, written with
[notes/note-template.md](notes/note-template.md)) with their dependencies, status and barriers.
**Lean is the validity gate**: a result counts as established only when a named Lean declaration
compiles with the standard axioms; sketches, sourced theorems and numerics stay explicitly
conditional. The workflow guards against two failure modes: **research drift** (long runs that
lose the motivating question, repeat abandoned approaches or silently change definitions) and
**validity drift** (a plausible argument, sampled computation or cited result treated as if it
had been checked under the exact hypotheses needed downstream).

## Notes and the research graph

All planning and theory development is recorded in `notes/`, in a fixed structure.

- **The plan of record,** [notes/implementation-plan.md](notes/implementation-plan.md), holds:
  - the stellarator contract;
  - the research graph: a goal registry (RG.1, `G-*`), a question registry (RG.2, `Q-*`) and a note
    registry with dependency edges (RG.3, `N-*`);
  - the strict-audit status (RG.4), the work-selection rules (RG.5) and the definition of done
    with the evidence gates (RG.6);
  - dated progress logs (§9, §10, §13).
- **Research notes** live in [notes/theory/](notes/theory/README.md), one file per note. A few
  topic notes (N-18 to N-21, N-25), the goal proposals (`notes/goals/`, N-22) and the design note
  (`notes/design/`, N-23) sit elsewhere in `notes/`, indexed in [notes/README.md](notes/README.md).
  - Each note has a stable ID `N-k`, a row in RG.3 and a line in the index `notes/theory/README.md`.
  - Each note starts with the metadata table of [notes/note-template.md](notes/note-template.md):
    kind, what it addresses, dependencies, difficulty, status, Lean evidence, audit evidence, last
    update.
  - The body follows the template's sections: purpose and scope, dependencies, sources, theory
    development, claims and evidence, barriers and readiness, outputs.
  - Every claim carries exactly one status: conjecture, proof sketch, complete proof, numerical
    observation (untrusted), sourced theorem, or compiled Lean theorem with its declaration name.
- **Specifications** live in [notes/formalization/](notes/formalization/00-model-contracts.md).
  `00-model-contracts.md` is normative: model contracts, and C1–C5 in Lean form.
- **Goals.** [notes/goals/method.md](notes/goals/method.md) explains how to choose and state goals
  and questions: outputs before methods, kinds of uncertainty, checkable obligations, shared
  scenario records, activation rules.
- **Audit records** live in [notes/audit/](notes/audit/). Findings have IDs, such as AR-H1 and
  AC-1, with severity and resolution.
- **Implemented notes keep their content.** A note that is wholly or partially implemented in Lean
  is the specification its code was built against, so it is not rewritten.
  - It only gets bookkeeping: implementation progress in its Status and Lean evidence rows, and
    pointers to later notes.
  - A changed method, target, statement or plan becomes a new note that depends on it: a *method
    note* (an additional or alternative approach) or a *patch note* (with a `Patches` row naming
    the changed sections, and the effect on the existing declarations).
  - A note is read as the original plus its patches. Many patches are consolidated into a new
    note.
  - `scripts/notes/implementation_status.py` classifies notes from their metadata as `none`,
    `partial` or `whole`.
- **Workflow.** Notes are updated after every work unit, including failures. A note without
  implementation is rewritten to its current state rather than appended to indefinitely. No note
  file exists without registration. The agents follow this through the skills
  `plasmalean-develop-theory`, `plasmalean-add-note`, `plasmalean-modify-notes` and
  `plasmalean-update-notes-from`.

## Policies

- **No `decide` of any kind** (`decide`, `decide +kernel`, `decide_cbv`, `native_decide`) in new
  code. Use `norm_num` or `rfl` for a few closed facts, `kernel_fact`, `bool_cert` or `eval_cert`
  for medium checks, and explicit proof-term certificates (the SubsetSum pattern, Kronecker
  certificates) for large ones. The remaining `decide +kernel` lines are legacy, being removed
  under Phase 16.
- **Standard axioms only:** `scripts/check_axioms.lean` (default build) and
  `scripts/check_axioms_heavy.lean` (on-demand modules) report only `propext`, `Classical.choice`
  and `Quot.sound`. No `sorry`, `admit` or `axiom`; model laws are typeclass hypotheses.
- **Zero warnings** in `lake build`, including the 100-character line linter.
- **At most 6 GB per Lean process:** split large certificates over several modules, and build
  stale heavy modules one at a time. First builds of very heavy certificates go to the workstation.
- Every module, definition and theorem has a docstring. Every new law has the sanity triad
  (degenerate case, instance, counterexample) plus risk-specific checks. Every certificate format
  has accepted and rejected fixtures.
- **Strict audits include previous code:** on `start`, every kernel declaration is inventoried and
  red-teamed, the build and axiom audit run, and the audited commit is recorded. Every defect found
  gets a compiled regression check.
- **Lean is the validity gate,** and implemented notes keep their content (see "Notes and the
  research graph").

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
