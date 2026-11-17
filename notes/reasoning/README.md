# notes/reasoning/

One folder per proof attempt or exploration, created by the `plasmalean-try-to-prove` and
`plasmalean-explore-mathematics` skills through `plasmalean-reasoning-loop`, and per source
analysis of `plasmalean-update-notes-from` (`<YYYY-MM-DD>-source-<slug>/`). Folders are named
`<YYYY-MM-DD>-<short-slug>/` and hold every artifact of the task:

- `README.md`: the task card, with the input, modes, linked goals, questions or notes, status,
  outcome and an index of the artifacts;
- `log.md`: a dated log of phases, decisions and commands;
- `01_` to `05_` files: formalization, examples, sources, questions, strategy or exploration
  plans, execution or research traces, and the final manuscript, failure report, research brief
  or obstacles report;
- `lean/`: Lean drafts checked with `lake env lean` (within the laptop memory budget);
  `computations/`: exploratory scripts and their outputs; `subtasks/`: recursive loops on hard
  lemmas.

A task's outcome is linked into the research graph in `../implementation-plan.md` when it ends
(skill `plasmalean-add-note`). Its evidence state follows `../note-template.md` and
`../domain-libraries.md`: an informal proof is proof-ready, a checked Lean draft is lean-ready,
and only a result promoted into `PlasmaLean/`, compiled in the build with standard axioms and
audited is verified.
