---
name: plasmalean-develop-theory
description: Entry point for PlasmaLean. Coordinate interactive or autonomous theory development and stellarator design through goals (G-*), questions (Q-*) and dependency-aware research notes (N-*). Use for `start`, project status or summaries, "work on ...", discussion that may change the research graph, and "keep working"; route ready tasks to discovery, formalization, numerics, audit or design while keeping Lean as the validity gate.
---

# Coordinate PlasmaLean theory development

PlasmaLean builds theory **and** formalizes it while designing stellarators. The design work
(confinement, stability, burn, coils) is the motivation; the durable output is reusable, verified
mathematics plus honest certificates for concrete candidates. Every work unit should leave the
theory, the note graph and the plan in a better state, not only a new design number.

Read first:

- `notes/implementation-plan.md`: the plan of record. Its "Research graph" part holds the goal,
  question and note registries, the strict-audit status and the work-selection rules; §9, §10 and
  §13 are the dated logs.
- `notes/note-template.md`: metadata and sections of a research note.
- `notes/domain-libraries.md`: the run protocol (kernel, sanity, library; progress report, slides,
  site regeneration after every run).
- `notes/formalization/00-model-contracts.md`: separate contract predicates and the corrections.
- `notes/theory/` (index `notes/theory/README.md`): discovery notes; the relevant ones for the item.
- `Workstation.md`: the laptop budget and the workstation pipeline for heavy numerics and builds.

Inspect actual Lean declarations (`rg` in `PlasmaLean/`) before describing a dependency as verified.

## Maintain the research graph

Use stable identifiers for goals (`G-*`), questions (`Q-*`) and notes (`N-*`), registered in the
plan. Goals and questions may be independent or auxiliary. Each note records what it addresses,
its dependencies and the evidence it needs from them, outputs, difficulty, barriers, status and
Lean evidence (template). Older notes in `notes/theory/` use the status tags of
`notes/theory/README.md`; retrofit the template metadata when a note is touched, not wholesale.
Do not confuse `N-*` note IDs with the §12 work packages N1–N3 or with the gates P0–P9, E0–E8.

Processing a note may yield a proof, counterexample, source comparison, computation, new theory,
new notes or changes to goals and questions. Do not force exploratory mathematics into Lean before
its statement and argument are ready.

**Lean results gate dependencies.** Only a named, compiled Lean declaration (standard axioms only)
passes the gate. An informal proof, a sourced theorem, a sympy check or a float computation is an
input, not an established premise. Conditional exploration on a conjecture is allowed when every
downstream result stays explicitly conditional and unverified. Model laws (Littlejohn guiding
centres, ballooning reductions, Bosch-Hale enclosures, a supplied transport solution) are
hypotheses: name them in the scope of every claim that uses them.

**On-demand modules.** Modules not imported by `PlasmaLean.lean` (the on-demand top modules such as
`PlasmaLean.Design.RationalStellaratorGCMuQuarter`, `…GCEwFamily`, `…GCMuWide`, `CoilKamCert`) count
as verified under the workstation policy of 25 October 2026: built and axiom-checked
(`scripts/check_axioms_heavy.lean`) on the workstation and spot-checked on the laptop
(`workstation/REVIEWED.md`). Say so when citing them, and note when they are stale after an
upstream change.

## Interpret user requests

- **`start`**: run `plasmalean-audit-domain` strictly before ordinary work. If the plan's audit
  table has no audited commit, do a full strict audit of existing code, especially every kernel
  declaration (`PlasmaLean/Kernel/`). Otherwise inspect all changes since the audited commit and
  refresh the affected audits. Then report repository status, audit findings and ready choices.
  Do not begin new theory on an unaudited foundation. Respect the laptop budget (below): if a full
  build is not affordable, audit by reading and targeted module builds, and record exactly what
  ran.
- **`status`** or a summary: goals, questions, verified frontier (declaration names), active and
  blocked notes, open audit findings, and a few ready choices. Match the requested detail.
- **`work on <item>`**: resolve the ID, note path or topic. If it is broad, select and announce the
  nearest useful subnote. Respect the user's selection even when it is blocked: explain the missing
  prerequisites and work on one only when that is the closest in-scope way forward. Recommend
  sub-agents when independent strands can produce concrete inputs in parallel.
- **Discussion**: engage with the mathematics, physics or source. Record durable conclusions,
  objections, sources and new subquestions in the graph when they affect future work.
- **`keep working`**: autonomous mode. Continue across work units without asking the user to pick
  after each one. Use sub-agents for independent ready tasks or independent attacks on a hard
  question when this improves progress.

## Use sub-agents deliberately

Prefer sub-agents when at least two substantial tasks can proceed independently: primary-source
review, counterexample search, Mathlib reconnaissance, numerical exploration (untrusted oracles),
proof attempts, an independent kernel/specification audit (the plan's lane E). Give each a precise
item ID, inputs, output format, the specialized skill to use, and a non-overlapping scope. The
prompt template is in the plan, §7.

- **File ownership.** All agents share the checkout. Assign each agent its own new files and
  namespace (`PlasmaLean.<X>`); no two agents edit the same file. Shared files (`PlasmaLean.lean`,
  `scripts/check_axioms*.lean`, the plan, README, progress files) are edited by the coordinator
  only. Use `isolation: "worktree"` only for refactors of shared files: every worktree rebuilds
  `.lake`.
- **Serialized heavy builds.** At most one heavy Lean build at a time across all agents. Never let
  two agents run `lake build` on overlapping stale dependencies.
- **The coordinator verifies reports.** A sub-agent report is not evidence. Before integrating,
  grep every cited declaration (one Phase 5 report cited declarations that did not exist), read
  the statements, reconcile definitions and hypotheses, build the affected modules and check
  `#print axioms`.

Do not delegate a trivial task, a tightly coupled proof step, or work whose coordination cost
exceeds the likely gain.

## Resource rules (laptop)

- Each Lean process stays within **6 GB** peak memory. The default build must stay within about
  60 CPU-minutes and an on-demand top module within 240.
- **Build stale dependencies one at a time** (or in small groups of light modules). `lake build
  Top` starts every stale dependency in parallel; 14 certificate modules at once nearly exhausted
  memory. Find stale modules with `lake build --no-build <Top>`, check `memory_pressure`, and wait
  if free memory is below 40 %.
- Heavy numerics (KAM families, ballooning searches, Chebyshev families) and first builds of large
  certificates go to the **workstation** (`Workstation.md`, `scripts/workstation/run.sh`, task
  scripts in `scripts/workstation/tasks/`). Its job is to find *smaller* certificates; results
  return through `plasmalean-workstation-update`.

## Proof policy

No `sorry`, `admit`, `axiom`, `native_decide` or unsafe proof anywhere. New code uses **no
`decide` of any kind**: concrete checks are short tactic proofs or explicit proof terms
(`kernel_fact`, `bool_cert`, `eval_cert`/`fiv_cert`, the Kronecker and family certificates, or a
new predicate in the SubsetSum pattern), as in `plasmalean-lean-proofs`. Remaining
`decide +kernel` lines are legacy under Phase 16. Generators validate every emitted bound in exact
arithmetic before writing Lean.

## Run one work unit

1. Verify the dependency status of the item and choose one coherent outcome.
2. Route to the method:
   - `plasmalean-discover-theory`: an open mathematical gap (conjecture, proof, counterexample);
   - `plasmalean-formalize-theory`: a complete sourced theorem or proof to put in Lean;
   - `plasmalean-audit-domain`: model and specification risk, kernel changes, claim review;
   - `plasmalean-certify-numerics`: a numerical candidate to turn into a certificate;
   - `plasmalean-design-stellarator`: a stellarator candidate, its gates and composed certificates;
   - `plasmalean-model-materials`: coils, walls, blanket and other engineering constraints;
   - `plasmalean-lean-proofs`: whenever Lean is written;
   - `plasmalean-workstation-update`: integrating workstation runs.
3. Develop, test or formalize the result. Failed approaches and counterexamples are outputs:
   record the barrier they establish.
4. Compile and audit Lean output in proportion to the claim, within the resource rules. Record
   exact declaration names, assumptions and whether the module is default-build or on-demand;
   otherwise leave the status below verified.
5. Update the affected notes, the registries in `notes/implementation-plan.md` (and a dated log
   entry in §13), including newly ready dependants, and do this also after a failure. After a
   run, follow the reporting protocol of `notes/domain-libraries.md` (progress report, slideshow,
   README summary, `node scripts/generate_handbook.mjs`, `node scripts/check_site.mjs`).

Re-run the relevant strict audit after any change to the kernel, a foundational definition, a law
instance, a certificate soundness theorem or a top-level claim. Existing code is in scope.

## Select autonomous work

Choose among items whose established prerequisites are compiled. Prefer, by project value rather
than mechanically:

- a prerequisite that unlocks several important notes or questions;
- a validity gap on the path to an active goal (an open audit finding, a supplied reduction);
- an inexpensive counterexample test for a risky conjecture;
- a lean-ready theorem that advances the verified frontier (theory before one-off certificates);
- a research note likely to make a blocked question precise.

Keep G-1 and G-2 both moving, and keep theory and design interleaved: a design gate that needs new
mathematics becomes a question and a note, not an ever-larger computation. Re-planning trigger
(plan §6): an approach that failed twice is downgraded or turned into an obstruction study.

Create auxiliary notes or questions when discovery requires them, but do not silently replace a
top-level goal or make a materially new commitment (a new kernel law, a large disk or CPU budget).
Stop autonomous mode when no useful item is ready, a user decision is needed, authority or
external input is missing, or the user pauses it.

## Report and hand off

After each work unit, distinguish compiled results (default build or on-demand), complete but
unformalized arguments, conjectures, numerical observations and barriers. In interactive mode, ask
what to work on next and offer a short set of ready notes, goals or questions plus free discussion.
In autonomous mode, give a concise progress update, name the next selected item and continue.
Never describe the real device as confined or stable because a conditional theorem compiles.
