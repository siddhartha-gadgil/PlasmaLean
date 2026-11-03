# Getting started with PlasmaLean: develop theory, check it with Lean

**Repository:** [`siddhartha-gadgil/PlasmaLean`](https://github.com/siddhartha-gadgil/PlasmaLean)
**Template it follows:** [`siddhartha-gadgil/LeanTheory`](https://github.com/siddhartha-gadgil/LeanTheory)
(extracted from this project; the same workflow, with the stellarator domain filled in)
**Methodology:** research-note graphs, a small auditable domain kernel, and Lean as the validity gate

## 1. Purpose

PlasmaLean develops the mathematical theory needed to design a stellarator and checks it with Lean.
It is not merely a pipeline for translating finished mathematics into Lean. The project has several
goals (confinement and stability, thermal performance, current-free rotational transform,
omnigeneity), open questions, partial approaches, sources, calculations and design problems.
Agents and users develop these interactively or autonomously.

The aim is fixed by the **stellarator contract** C1–C5 (see the [README](../README.md) and the
[implementation plan](../notes/implementation-plan.md)).

Lean is the validity gate.
- Literature summaries, proof sketches, numerical experiments and conjectures are valuable research
  artifacts, but they are not established results.
- A later step may rely on an earlier result as proved only after a corresponding Lean declaration
  compiles, with standard axioms only.
- Exploratory work may investigate the consequences of an unverified conjecture, provided the
  dependency stays explicit and no conclusion is reported as established.

Compilation does not rule out a badly stated or vacuous theorem. Strict semantic audits therefore
review old as well as new code, with complete coverage of the domain kernel (`PlasmaLean/Kernel/`).
An audit checks four things:
- definitions express the intended physical model;
- assumptions are consistent;
- sanity checks are strong enough;
- downstream claims use the verified statement they advertise.

Audit fix AR-H1 is an example. An early version of the C1 clause could be satisfied vacuously, and
the audit replaced it with the Ampère circulation around each torus's own poloidal loop.

The method prevents two common failures:

1. **Research drift:** long agent runs lose the motivating question, repeat abandoned approaches or
   silently change definitions.
2. **Validity drift:** a plausible argument, sampled computation or cited result is treated as if
   it had already been checked under the exact hypotheses needed downstream.

## 2. The project graph

The project tracks three kinds of first-class items, registered in the "Research graph" part of
[notes/implementation-plan.md](../notes/implementation-plan.md):

- **Goals (`G-*`, RG.1)** are desired mathematical, scientific or engineering outcomes. There are
  several, and a goal may support another.
- **Questions (`Q-*`, RG.2)** are unresolved issues whose answers may be the project output or a
  prerequisite for a goal. A question can be independent, auxiliary, blocked, parked or refuted.
- **Notes (`N-*`, RG.3)** are work units. A note may do any of the following:
  - synthesize literature;
  - develop a definition;
  - explore a conjecture;
  - record a counterexample;
  - give a proof;
  - specify a computation;
  - prepare a Lean formalization;
  - document a verified result;
  - log a multi-step certificate build.

Every note follows [the note template](../notes/note-template.md) and records:

- the goals and questions it addresses;
- note and Lean-declaration dependencies, with the verification required from each;
- its expected outputs and any new notes it creates;
- difficulty, barriers and unknowns;
- research status and formalization readiness;
- claims, counterexamples, sources and compiled Lean declarations, without conflating them.

Processing a note need not end in Lean code. It may produce new theory, split a question into
tractable subquestions, expose a barrier, refute an approach, update priorities or create further
notes. When a claim becomes precise and justified enough to formalize, its note moves to
`lean-ready`; only successful compilation moves the result to `verified`.

**Notes and implementation.** A note that is wholly or partially implemented in Lean is the
specification its code was built against, so its content is not rewritten. A changed method,
target or statement goes into a new *method note* or *patch note*. Only notes with no
implementation are edited in place. See "Notes and the research graph" in the README and the skill
`plasmalean-modify-notes`.

Guidance on choosing and stating goals is in [notes/goals/method.md](../notes/goals/method.md).

## 3. Repository architecture

| Part | Purpose |
| --- | --- |
| `notes/` | The plan and research graph, research notes (`theory/`), specifications (`formalization/`), audit records (`audit/`), goal proposals (`goals/`) |
| `PlasmaLean/Kernel/` | Small domain specification: core objects and physical laws (force balance, Maxwell, guiding centres, transport) as structures or typeclasses, never project axioms |
| `PlasmaLean/Sanity/` | Degenerate cases, concrete instances, counterexamples and regression tests for every law |
| `PlasmaLean/Theory/` | Reusable proved mathematics: geometry, fields, KAM, stability, kinetics, the contract |
| `PlasmaLean/Bridge/` | Theorems connecting abstract theory and finite certificates to domain claims, with a common witness |
| `PlasmaLean/Certificates/` | Exact checkers, enclosures and certified data; external solvers stay untrusted |
| `PlasmaLean/Design/` | Concrete candidates (rational stellarator field, Dommaschk field, coils, equilibria) composed from the verified layers |
| `scripts/` | Setup, axiom audits, oracles and generators (untrusted, exact validation before emitting Lean), the workstation pipeline, website generation |
| `progress/`, `docs/` | Dated reports, the slideshow and the generated website |
| `.agents/skills/` | Agent skills (`.claude` is a symlink to `.agents`) |

The domain kernel is distinct from Lean's logical kernel. Lean verifies consequences of the encoded
model; expert review and validation determine whether the model applies to a real plasma.

## 4. Working on the project

### Step 1: Set up the checkout

The startup audit is the first point at which Lean is needed. Check whether it is available:

```bash
lean --version
```

If that command is unavailable, or if the checkout has not yet fetched its dependencies, run:

```bash
scripts/setup.sh --check-axioms
```

On Linux and macOS this idempotent script does the following:
- installs `elan` if necessary;
- selects the Lean version pinned by `lean-toolchain`;
- fetches the Mathlib cache;
- builds the default library and runs the axiom audit.

If a newly installed `lean` or `lake` is not visible in the current shell, open a new shell or run
`source "$HOME/.elan/env"`. Do not install another Lean version separately from the pinned
toolchain.

The default build is large. Keep each Lean process within about 6 GB, and build stale heavy modules
one at a time. Heavy certificates are *on-demand top modules*, outside the default build. Each
module's docstring gives its build command.

The first command to give the agent in a new or unfamiliar checkout is:

```text
start
```

`start` means:
1. inspect the repository;
2. strictly audit the existing kernel and the affected code;
3. run the available build and axiom checks;
4. record the audited commit and findings (RG.4 of the plan);
5. summarize goals, questions, verified results, barriers and ready choices.

It does not begin new theory until the foundation has been audited.

### Step 2: Add goals, questions, sources and ideas

The registries are already seeded. New directions enter the same graph. Give the agent the
scientific context, papers, user ideas and desired outputs; a colleague's brief is an example
(note N-32). Use this prompt, replacing the bracketed fields:

```text
Add the following to the PlasmaLean research graph.

- Topic or idea: [what is proposed]
- Relation to the contract and existing goals: [which of C1–C5, G-*, Q-* it serves]
- Sources: [papers, books, data, with precise locators where available]
- Constraints: [models, parameter ranges, units, tolerances, computational limits]

Read notes/implementation-plan.md (stellarator contract, RG.1–RG.5), notes/note-template.md and the
related notes first. Then:
1. Decide whether this is a new goal, a new question, or work under an existing one; create stable
   G-*/Q-* entries only for genuinely new items, with success criteria and support links.
2. Record the source and idea in a note (skill plasmalean-add-note): distinguish published
   theorems, empirical inputs, proposed models, user ideas, conjectures and numerical observations.
   If the change concerns an implemented note, write a method or patch note instead of rewriting it
   (skill plasmalean-modify-notes).
3. Record dependencies, the evidence required from them, outputs, difficulty, barriers and Lean
   readiness, and the dependency edges.
4. Suggest where it fits the priority order (RG.5), separately from verified facts.

Do not label sourced or plausible claims as verified. Report the changes, unresolved ambiguities and
2–5 ready choices, then ask what to work on next.
```

### Step 3: Develop the note graph

Choose a goal, question or note and process one coherent work unit. Depending on readiness, this may
mean any of the following:
- studying literature;
- testing definitions;
- deriving a lemma;
- searching for a counterexample;
- running an exploratory calculation;
- writing a proof;
- formalizing it in Lean.

When a note first needs a Python oracle, generator or workstation helper, create the repository's
environment and activate it:

```bash
scripts/setup.sh --python --no-build
source .venv-ws/bin/activate
```

This creates `.venv-ws` from `scripts/requirements.txt`, and it is safe to run again when the
requirements change. Activate `.venv-ws` in each new shell used for project Python work. Do not
install project packages globally. Heavy numerics and first builds of large certificates go to the
workstation (see [Workstation.md](../Workstation.md)).

The work unit ends by updating the affected notes and registries, and a dated entry in §13 of the
plan. New mathematical ideas belong in notes even when they are not ready for formalization. New
obstacles become explicit barriers or questions, rather than disappearing into a progress narrative.

### Step 4: Formalize ready mathematics

Formalize only when the claim, hypotheses, definitions and proof route are precise enough. Search
Mathlib and the existing project before adding infrastructure. Put each kind of result in its layer:
- model laws in `Kernel/`, as explicit hypotheses;
- derived mathematics in `Theory/`;
- domain connections in `Bridge/`;
- exact checks in `Certificates/`.

Every new law needs the sanity triad:

1. a meaningful degenerate or limiting case;
2. a concrete satisfying instance, guarding against vacuity;
3. a counterexample, showing that the law excludes something.

The triad is a baseline, not sufficient audit coverage. Every kernel law also needs at least one
risk-specific adversarial check, such as one of these:
- singularities (the axis, `R = 0`);
- symmetry;
- conservation;
- dimensional scaling;
- parameter endpoints;
- boundary behavior;
- quantifier order;
- nonempty domains;
- accepted and rejected certificate fixtures.

Add a compiled regression check for every defect found later.

Concrete checks use no `decide` of any kind. Use `norm_num` or `rfl` for a few facts,
`kernel_fact`, `bool_cert` or `eval_cert` for medium checks, and explicit proof-term certificates
for large ones (skill `plasmalean-lean-proofs`).

### Step 5: Pass the validity gate

Compile the affected modules, run the axiom audit, and record exact declaration names and
hypotheses. No downstream note may mark the result as an established dependency until this
succeeds. A failed formalization returns useful information to the research note: a missing
hypothesis, a false conjecture, an unsuitable definition or a library gap.

Then perform semantic review. For kernel or foundational changes, re-audit all affected existing
code, not only the new lines. Check the following:
- vacuity and degenerate witnesses;
- totalized operations;
- quantifiers, units and source fidelity;
- model scope;
- the continued validity of downstream theorems.

Record the audited commit and unresolved findings in the plan.

### Step 6: Report and select the next work

After every work unit, report:

- what changed in the theory and the note graph;
- what is compiled and therefore available downstream (default build or on demand);
- what remains conjectural, empirical or blocked;
- newly created questions, notes and barriers;
- ready next choices and why they are ready.

Each stage of progress also refreshes the slideshow and the site, and is committed and pushed. In
interactive mode, the agent asks what to work on next.

## 5. Ways to interact

These phrases are conventions rather than a rigid command language. The distinctive phrases are
preferred over generic requests, so that the agent reliably selects the project skill.

- **`start`**: run or refresh the strict audit, record its scope and results, then give a status
  summary and ready choices.
- **`work status`** / **`summarise work`**: goals, questions, verified results (declaration names),
  active and blocked notes, open audit findings and ready choices.
- **`work on N-…`**, **`work on G-…`** or **`work on Q-…`**: one work unit on that item. For a
  broad goal or question, the agent chooses and announces the nearest useful subnote.
- **`discuss …`**: explore an idea, source or objection. Durable outcomes become notes and
  dependency edges.
- **`add a note`** / **`make a note`** / **`record this`**: record a result, failure, source
  assessment or decision as a registered note (skill `plasmalean-add-note`).
- **`modify notes`** / **`add notes`**: change what the notes say. Notes without implementation
  are edited in place; implemented notes get method or patch notes (skill
  `plasmalean-modify-notes`).
- **`keep working`**: autonomous mode. The agent repeatedly chooses the highest-value ready item,
  develops or formalizes it, updates the graph and continues, with concise progress updates. It
  stops when a real user decision is needed, nothing useful is ready, authorization is needed, or
  the user pauses it.
- **`update from workstation`**: review, re-check and merge workstation runs (skill
  `plasmalean-workstation-update`).

Interactive mode is the default. Autonomous mode uses the same validity gates; it changes work
selection, not standards of evidence or authority.

## 6. Prompts for agents

### Repository startup

```text
Start. Before doing new work, strictly audit this repository at its current commit. Review every
existing kernel declaration and its sanity coverage, red-team assumptions and degenerate cases,
inspect affected downstream results, run the feasible build and axiom checks (within the laptop
budget), and record findings and the audited commit. Add missing risk-specific sanity or regression
checks. Then summarize the project and offer ready choices.
```

### Note worker

```text
Work on [N-ID, G-ID, Q-ID or topic]. Read its dependencies and verification requirements first.
Choose the appropriate activity: literature synthesis, theory discovery, counterexample search,
proof development, numerical exploration or Lean formalization. Do not use an unformalized claim
as an established premise. Update the note graph, readiness and barriers, then report verified
outputs separately from conjectural progress and offer ready next choices.
```

### Specification auditor

```text
Audit this model or proposed theorem for vacuity, contradictory hypotheses, degenerate witnesses,
unguarded total operations, missing quantifier bounds, unit or normalization errors, and a mismatch
between the claim and its cited source. Produce corrections, sanity checks and new research
questions. A correction is not verified until its Lean declaration compiles.
```

### Autonomous coordinator

```text
Keep working. Survey the goal/question/note graph, select the highest-value item whose established
prerequisites are compiled, and complete one coherent work unit. Update notes and verification
evidence, report a concise status update, then select the next ready item. Continue until genuinely
blocked or a user decision or new authorization is required.
```
