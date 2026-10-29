# notes/

The research workspace of PlasmaLean: goals, questions, sources, theory development, dependencies,
barriers and the boundary between exploratory and Lean-verified work. Nothing here is a compiled
theorem unless it names a Lean declaration.

- [`implementation-plan.md`](implementation-plan.md): the plan of record. Its "Research graph" part
  holds the goal (`G-*`), question (`Q-*`) and note (`N-*`) registries, the strict-audit status and
  the work-selection rules; §0–§13 are the plan of 20 October 2026 and the dated logs.
- [`note-template.md`](note-template.md): metadata and sections for a new research note
  (dependencies and the evidence they need, difficulty, barriers, readiness, Lean evidence).
- [`domain-libraries.md`](domain-libraries.md): the run protocol (kernel, sanity checks, library;
  progress report, slideshow and site regeneration after every run).
- [`theory/`](theory/README.md): discovery notes (lane A), with status tags; new notes use the
  template.
- [`formalization/`](formalization/README.md): model contracts and the topic specifications.
- [`goals/`](goals/README.md): the G-3 proposals (model adequacy, probabilistic goals).
- [`design/`](design/vacuum-demonstrator.md): the vacuum demonstrator fixture and its boundary.
- Active topic notes: `pde-bounds-and-verification-roadmap.md` (stages and milestones),
  `bkm-regularity-and-perelman-burn-bounds.md` (corrected evolution specification, plan §11),
  `microturbulence-and-available-energy.md`, `holomorphic-bundles-kym-wick-rotations.md`
  (exploratory geometry); `Stellerator.md` is the original design basis (historical).

Several notes are rendered on the website by `scripts/generate_handbook.mjs`; edit the Markdown,
not the generated HTML.
