---
name: plasmalean-add-note
description: Record a PlasmaLean research note correctly, as a new note or an update to an existing one, after a discussion, a result, a failed attempt, a source assessment or a design decision. Use for "add a note", "make a note", "record this", "note this down", "write this up", "save this as a note", "update the note on …" (and close variants). Allocates the N-* ID, fills notes/note-template.md, registers the note in the plan's research graph and the theory index, updates the affected G-*/Q-* rows and the dated log, regenerates the site, and commits and pushes.
---

# Add or update a PlasmaLean research note

Notes are the durable record of theory development; the research graph in
`notes/implementation-plan.md` (part "Research graph": RG.1 goals, RG.2 questions, RG.3 notes)
indexes them. A note that is not registered is invisible to later work. This skill turns a
conclusion into a registered, template-conformant note in one pass.

Read first: `notes/note-template.md` (the structure), the RG.1–RG.3 tables of
`notes/implementation-plan.md`, and `notes/theory/README.md` (the index of discovery notes).

## 1. Decide: new note or update

- **Update** when the topic already has a note (search RG.3 and `notes/theory/README.md` for the
  subject, the question ID and key words; `rg -l` in `notes/`). Updating keeps one current record:
  rewrite the metadata rows (Status, Lean evidence, Last updated) and the "Claims and evidence"
  section so they state the *current* state; put the history in a short dated paragraph or in the
  plan's §13 log, not as an ever-growing tail of appended sections. If a note already has a long
  appended history, add or refresh a "Current state" summary right after the metadata table.
- **New** when the content is a substantial unit of its own: a new question or route, a source
  assessment, a design study, a proof or obstruction, a computation campaign. Small facts belong in
  an existing note or in the plan's §13 log instead.
- Running logs of a multi-step build (status notes kept by sub-agents) are notes too: give them an
  ID and a metadata table (Kind: status log), or fold them into the design note they serve. Never
  leave an unregistered file in `notes/theory/`.

## 2. Create a new note

1. **ID.** The next free `N-*`: the largest ID in RG.3 plus one (check `rg -o "\`N-[0-9]+\`"
   notes/implementation-plan.md | sort -V | tail -1`). Do not reuse IDs, and do not confuse `N-*` with
   the work packages N1–N3 or the gates P0–P9, E0–E8.
2. **File.** Discovery notes go in `notes/theory/<kebab-case-name>.md`; formalization
   specifications go in `notes/formalization/`. Copy the template; fill every metadata row; delete
   the guidance text.
3. **Content discipline** (from the template and the develop-theory skill):
   - Give models, domains, units, conventions and quantifiers.
   - Mark each claim with exactly one status: conjecture, proof sketch, complete mathematical proof,
     numerical observation (untrusted), sourced theorem, or compiled Lean theorem. Lean claims carry
     exact declaration names, their hypotheses (supplied model laws, solutions) and
     default-build/on-demand status. Grep each name before citing it.
   - Record user-contributed ideas and sources with provenance; do not overstate novelty.
   - Keep untrusted numerics reproducible (scripts in `scripts/<family>/`, not only `/tmp`).
   - Record failed approaches and the barrier they establish.
   - State scope limits plainly (what is not proved, which contract clauses are not addressed).

## 3. Register and cross-link (both new notes and updates)

1. **Plan, RG.3:** add or update the row `| \`N-..\` | path: title | addresses | depends on |
   difficulty | status | next |`, keeping it consistent with the note's metadata. Add new
   dependency edges below the table when they matter.
2. **Plan, RG.1/RG.2:** update every goal or question the note changes (status, current best
   answer, evidence names). Create a new `Q-*` when the note opens a genuine new question.
3. **Plan, §13:** append a short dated log entry (what changed, declaration names, numbers).
4. **Index:** add or update the line in `notes/theory/README.md` (or the formalization index).
5. **Other notes:** add a one-line pointer in notes that the new note corrects or supersedes, and
   mark superseded claims there.
6. **Audit:** if the note reports a defect in a definition, contract or claim, record it in the
   current audit note under `notes/audit/` with an ID and severity, and in the plan's RG.4.

## 4. Publish

1. If the note changes a headline claim, update `README.md` and `progress/slideshow.json`
   consistently (no overclaiming; untrusted numerics labelled).
2. `node scripts/generate_handbook.mjs` and `node scripts/check_site.mjs` (must pass).
3. Commit with explicitly staged paths (never `git add -A`; other agents may have untracked
   files), `git pull --rebase` if needed, then `git push`.

## Checklist

- [ ] new vs update decided; existing note found if any
- [ ] template metadata complete and current; claims carry one status each
- [ ] RG.3 row, affected RG.1/RG.2 rows, §13 entry
- [ ] theory index line; pointers in related notes
- [ ] audit item recorded if a defect was found
- [ ] README/slides if a headline changed; site regenerated and checked
- [ ] committed with explicit paths and pushed
