# notes/

The research workspace of PlasmaLean: goals, questions, sources, theory development, dependencies,
barriers and the boundary between exploratory and Lean-verified work. Nothing here is a compiled
theorem unless it names a Lean declaration. The structure follows the
[LeanTheory](https://github.com/siddhartha-gadgil/LeanTheory) template; the workflow is described in
[docs/GettingStarted.md](../docs/GettingStarted.md).

Every research note has an `N-*` ID, the template metadata table, a row in RG.3 of the plan and an
index line (here or in `theory/README.md`). Notes without Lean implementation are edited in place;
wholly or partially implemented notes keep their content, and changes go into new method or patch
notes (skills `plasmalean-add-note`, `plasmalean-modify-notes`;
`scripts/notes/implementation_status.py` classifies notes from their metadata).

- [`implementation-plan.md`](implementation-plan.md): the plan of record. Its "Research graph" part
  holds the goal (`G-*`), question (`Q-*`) and note (`N-*`) registries, the strict-audit status,
  the work-selection rules and the definition of done (RG.6); §0–§13 are the plan of 20 October 2026 and the dated logs.
- [`note-template.md`](note-template.md): metadata and sections for a new research note
  (dependencies and the evidence they need, difficulty, barriers, readiness, Lean evidence).
- [`domain-libraries.md`](domain-libraries.md): the run protocol (kernel, sanity checks, library;
  progress report, slideshow and site regeneration after every run).
- [`theory/`](theory/README.md): research notes N-1–N-17 and N-26 onwards, one file each, all with
  the template metadata.
- [`audit/`](audit/): strict audit records (finding IDs such as AR-H1, AC-1).
- [`formalization/`](formalization/README.md): model contracts and the topic specifications (N-24).
- [`goals/`](goals/README.md): [`method.md`](goals/method.md), how to choose and state goals and
  questions (generic guidance with PlasmaLean examples), and the G-3 proposals (model adequacy,
  probabilistic goals) (N-22).
- [`design/`](design/vacuum-demonstrator.md): the vacuum demonstrator fixture and its boundary (N-23).
- Active topic notes: `pde-bounds-and-verification-roadmap.md` (N-18, stages and milestones),
  `bkm-regularity-and-perelman-burn-bounds.md` (N-19, corrected evolution specification, plan §11),
  `microturbulence-and-available-energy.md` (N-20), `holomorphic-bundles-kym-wick-rotations.md`
  (N-21, exploratory geometry); `Stellerator.md` (N-25) is the original design basis (historical).

Several notes are rendered on the website by `scripts/generate_handbook.mjs`; edit the Markdown,
not the generated HTML.
