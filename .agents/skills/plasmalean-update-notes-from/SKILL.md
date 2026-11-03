---
name: plasmalean-update-notes-from
description: Update PlasmaLean research notes from given theory source files. Use for "update notes from <files, directory or URL>", "update the notes from this paper/brief/draft", "incorporate <file> into the notes", "bring the notes up to date with <source>" (and close variants). The sources may be papers, preprints, a colleague's brief, lecture notes, LaTeX or Markdown drafts, or Lean files from another project. They are analysed claim by claim, checked against the compiled Lean code and the existing notes, recorded in a source-assessment note, and the notes are then updated as in plasmalean-modify-notes: in place only where nothing is implemented, method or patch notes otherwise.
---

# Update notes from theory source files

This is the variant of "update notes" (skill `plasmalean-modify-notes`) in which the desired changes
come from source files rather than from the user's own words. The extra work is to read the
sources carefully, extract what they actually claim, and check it before anything enters the notes.
A source is an input, never evidence: nothing from it is established until a Lean declaration
compiles here. Example of the expected output: N-32, the assessment of a colleague's brief
(`notes/theory/holomorphic-qs-brief.md`).

Read first: `plasmalean-modify-notes` (the in-place versus method or patch rule),
`plasmalean-add-note` (IDs, template, registration), `notes/formalization/09-literature.md` (the
extraction protocol), and the RG.1–RG.3 tables of `notes/implementation-plan.md`.

## 1. Acquire the sources safely

- Read local files in place. For URLs, or files the user has just downloaded, put each one in its
  own new, empty directory outside the repository, and read it with tools that do not execute
  it: PDF and text readers, `pdftotext`. Never run scripts, notebooks or build files that come with
  a source. Lean files from elsewhere are not built inside this checkout unless the user asks.
- Record provenance for each source:
  - the path or URL;
  - title, authors and date or version;
  - a stable identifier (arXiv ID, DOI) if there is one;
  - the SHA-256 hash of the file (`shasum -a 256`);
  - who supplied it and when.
- Ask before committing third-party files to the repository. User-supplied briefs have so far
  been kept under `gpt/`. Otherwise cite by path or URL and hash.
- If a source is long, read all of it anyway, in parts. Do not assess a document from its abstract
  or summary. Note unreadable parts (scanned pages, missing figures) as gaps.

## 2. Extract the claims

For each source, build an extraction table (it becomes part of the assessment note):

| # | Claim (in your words) | Locator | Kind | Model, hypotheses, units | Relevance |
| --- | --- | --- | --- | --- | --- |

- **Locator:** theorem, equation, section or page.
- **Kind:** exactly one of:
  - published theorem with proof;
  - proof sketch;
  - formal asymptotic calculation;
  - numerical observation;
  - empirical fit;
  - definition or model;
  - proposal or plan;
  - open question;
  - Lean declaration (from elsewhere, uncompiled here).
- **Model, hypotheses, units:** the domain, regularity, quantifiers, boundary conditions, units
  and parameter ranges the claim actually needs. Hidden hypotheses are the most common source
  of error.
- **Relevance:** which contract clauses C1–C5 and which `G-*`, `Q-*`, `N-*` it touches, or "none".

Separate what the source proves from what it cites, conjectures or assigns as future work. Record
the source's own caveats.

## 3. Check the claims against the project

For each relevant claim:

1. **Against compiled Lean.** Search `PlasmaLean/` for the corresponding declarations (`rg`). The
   possible outcomes are:
   - it is already proved here: cite the declaration name and its build status, default or on
     demand;
   - it is consistent with our code;
   - it **contradicts** a compiled theorem. Then the source, our model or the translation between
     them differs: find which hypothesis or convention differs before recording anything. A
     compiled theorem is not overruled by a source; a mismatch may expose a modelling defect, which
     then gets an audit item.
2. **Against the notes.** Find the notes that already cover the topic, including refuted claims,
   recorded barriers and failed approaches. A source repeating a refuted route is recorded as such.
3. **Re-derive explicit content when cheap:** formulas, numbers, small examples, sign conventions.
   Use sympy or exact arithmetic in `.venv-ws`, with the scripts kept in `scripts/<family>/`.
   Record each check and its result; mark what was not checked.
4. **Assess, honestly:**
   - correct, incorrect (with the counterexample or error), or unverified;
   - useful for which question;
   - lean-ready or not;
   - novelty only as far as is known; do not overstate it.

## 4. Plan the note changes

Always create a **source-assessment note** (Kind: `source assessment`), one per source or per
coherent batch. It contains:
- the provenance;
- a short summary of the source;
- the extraction table;
- the checks and their results;
- a verdict per section or claim;
- the resulting changes to the graph.

Then decide, for every affected existing note, where each change goes, exactly as in
`plasmalean-modify-notes` §1–§3:

- classify each note with `python3 scripts/notes/implementation_status.py <files>` and by reading
  it;
- a note with **no implementation** is updated in place, citing the source with its locator;
- a **wholly or partially implemented** note gets bookkeeping only. A new **method note** records
  an approach the source proposes. A new **patch note** records a correction or change the source
  implies for the implemented note, with its effect on the existing declarations;
- a genuinely new question becomes a new `Q-*`, and a new goal is proposed only with the user's
  agreement.

For more than a couple of changes, show the user the plan before editing. The plan is a table with
these columns: source item, affected note, class, change, destination (in place, method note, patch
note, new question).

## 5. Apply, register and publish

1. Write the assessment note and the other new notes from `notes/note-template.md`. Every claim
   taken from a source keeps its kind and locator; nothing from a source is marked verified unless
   a compiled declaration here says so.
2. Make the in-place edits and the bookkeeping edits.
3. Register and cross-link as in `plasmalean-add-note` §3:
   - RG.3 rows, with dependency edges to the assessment note;
   - RG.1 and RG.2 updates;
   - the §13 log entry;
   - index lines;
   - pointers in the related notes;
   - audit items for defects found.
4. Publish as in `plasmalean-add-note` §4: README and slides if a headline changes, regenerate and
   check the site, commit with explicit paths, `git pull --rebase`, `git push`.

## Report

Give, per source:
- the provenance line;
- a two- or three-sentence verdict;
- the numbers of claims extracted, checked, correct, incorrect and unverified.

Then give the change table:

| Source item | Note | Class | Result |
| --- | --- | --- | --- |

The Result column is one of: edited in place, method note `N-…`, patch note `N-…`, new `Q-…`, or no
change (with the reason).

Finish with the commit hash and the ready next choices that the sources opened.

## Checklist

- [ ] sources acquired safely; provenance and hashes recorded; nothing executed
- [ ] every source read in full; extraction table with kind and locator per claim
- [ ] claims checked against compiled Lean, notes and audits; explicit content re-derived where
      cheap; contradictions investigated
- [ ] source-assessment note created
- [ ] affected notes classified; in place only without implementation; method or patch notes
      otherwise
- [ ] registration, §13, index, audit items; site checked; committed with explicit paths and pushed
