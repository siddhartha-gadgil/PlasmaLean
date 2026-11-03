---
name: plasmalean-modify-notes
description: Change PlasmaLean research notes without rewriting history that Lean already implements. Use for "update notes", "modify notes", "add notes", "change the notes", "revise the notes", "update the notes with …", "amend the plan in the notes" (and close variants), whenever the request is to change what notes say (methods, targets, plans, statements) rather than to record one new result. Surveys the present notes and their metadata, edits in place only notes with no implementation, and records every other desired change as a new note: a method note (an additional or alternative approach) or a patch note (a change to a wholly or partially implemented note). Registration and publishing follow plasmalean-add-note. When the changes come from given source files ("update notes from …"), use plasmalean-update-notes-from instead.
---

# Modify or add PlasmaLean notes, respecting implementation

A note whose content has been implemented in Lean is the specification that code was built
against. Rewriting it silently breaks the link between the note, the declarations and the audit
records. So changes are split:

- a note with **no implementation** is edited in place;
- a note that is **wholly or partially implemented** keeps its content. A desired change becomes a
  **new note** that depends on it.

When the changes come from given theory source files ("update notes from …"), use the variant
`plasmalean-update-notes-from`, which first analyses and checks the sources.

`plasmalean-add-note` stays the procedure for recording a single new result or discussion. This
skill decides *where* each requested change goes, then uses add-note for allocating IDs, the
template, registration and publishing.

## 1. Survey the present notes

1. Read the request and list the changes it asks for: new methods, changed targets, corrected
   statements, new plans, dropped routes. Find the notes each change touches: RG.3 of
   `notes/implementation-plan.md`, `notes/theory/README.md`, and `rg` for the topic, the `Q-*`/`G-*`
   IDs and key words in `notes/`.
2. Classify the notes from their metadata:

   ```bash
   python3 scripts/notes/implementation_status.py            # all notes in notes/theory/
   python3 scripts/notes/implementation_status.py notes/theory/<file>.md ...
   ```

   The script reads the `Status` and `Lean evidence` rows and checks which cited names are declared
   in `PlasmaLean/`. It prints one of:
   - `none`: no compiled Lean evidence;
   - `partial`: Lean evidence, and the status names open parts;
   - `whole`: Lean evidence, and no open part named;
   - `check`: undecided.
3. Confirm each classification by reading the note's metadata and its "Claims and evidence"
   section:
   - **Implemented** (partially or wholly): at least one claim of the note is a compiled Lean
     declaration (default build or on demand), or Lean code was written to its specification
     (spec notes, plans carried out, status logs of a build).
   - **No implementation**: no claim of the note is a compiled declaration and no code follows it.
     Its content is conjecture, sketch, source synthesis, numerics or an unexecuted plan.
   - Classify the note as a whole, not section by section. A partially implemented note counts as
     implemented even when the change concerns only its open part. When unsure, treat the note as
     implemented.
4. Show the user the plan before editing when the request is broad: a short table with note,
   class, the change, and where it goes (in place, method note N-new, patch note N-new). For a
   narrow, unambiguous request, proceed and report the table at the end.

## 2. Notes without implementation: edit in place

- Rewrite the affected sections and the metadata (Status, Depends on, Produces, Last updated) to the
  new current state. Keep failed approaches and their barriers. Put a dated one-line summary of
  the change in "Last updated", and the history in the plan's §13 log.
- If the change adds a substantial method of its own, a separate method note (§3) is still
  allowed. Use judgment: one note per coherent approach.

## 3. Implemented notes: new notes, not rewrites

Create one new note per coherent change, following `plasmalean-add-note` §2 (next free `N-*`, the
template, content discipline). There are two kinds:

- **Method note** (Kind: `method`, plus the usual kind words): an additional or alternative
  approach to the same goal or question, such as a new route, technique or design variant. Its
  `Depends on` names the original note and what it reuses from it. It does not restate the
  original's claims; it cites them.
- **Patch note** (Kind: `patch`): a change to an implemented note. This covers a corrected or
  strengthened statement, a changed target or parameter, an extension of a partially implemented
  plan, a dropped or replaced step, and an erratum. Its metadata has a `Patches` row: the original
  note's ID and the exact sections or claims it changes. The body states, for each patched item:
  - the original text (quoted briefly) and the replacement;
  - the reason;
  - the effect on Lean: either "none" (the declarations stand) or which declarations become stale,
    misnamed or insufficient, and the new Lean work needed.

  A patch never changes what a compiled declaration says. If the declaration itself is wrong for
  the purpose, the patch says so, and an audit item is recorded (add-note §3.6).

The original implemented note gets **bookkeeping edits only**:
- a `Patched by` / `Alternatives` metadata row (create it if absent) listing the new note IDs;
- a one-line pointer under its title: "Patched by N-k (sections …)" or "Alternative method: N-k";
- Status and Last updated changed only to record that a patch exists (for example "verified; patched
  by N-k").

Implementation progress that really happened is also recorded in the note it implements: the
Status, Lean evidence and Last updated rows, as in the develop-theory skill. That is bookkeeping,
not a content change. Do not edit its theory development, claims (except their evidence status),
targets or plan.

Readers and agents resolve a note as the original plus its patches in ID order. A note with more
than about three patches should get a consolidation note: a new note that states the combined
current content and supersedes the original and its patches. The old files remain as the record.

## 4. Register, cross-link and publish

For every new note and every in-place edit, follow `plasmalean-add-note` §3–§4:
- RG.3 rows: a new row for each new note, with the dependency edge to the original (`patches N-x`
  or `method for N-x`); the original's row updated with "patched by N-k";
- affected RG.1/RG.2 rows;
- a §13 log entry listing in-place edits and new notes;
- index lines in `notes/theory/README.md`;
- an audit item if a defect was found;
- README/slides if a headline changes;
- `node scripts/generate_handbook.mjs` and `node scripts/check_site.mjs`;
- commit with explicit paths, `git pull --rebase`, `git push`.

## Report

Give the user a table:

| Note | Class | Change | Result |
| --- | --- | --- | --- |
| `N-…` | none / partial / whole | … | edited in place / method note `N-…` / patch note `N-…` |

Add the commit hash.

## Checklist

- [ ] requested changes listed; affected notes found
- [ ] each note classified (script plus reading); unsure treated as implemented
- [ ] unimplemented notes edited in place, metadata current
- [ ] implemented notes untouched except bookkeeping; method/patch notes created with `Patches` or
      `Depends on` rows and Lean effects stated
- [ ] RG.3 rows and edges, RG.1/RG.2, §13, index, audit item if needed
- [ ] site regenerated and checked; committed with explicit paths and pushed
