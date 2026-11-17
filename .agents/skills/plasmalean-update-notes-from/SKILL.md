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

### Use the reasoning tools

Analyse each substantive theorem, proof, conjecture or example with the discovery skills, rather
than only summarizing it:

- **Source study.** Follow `../plasmalean-reasoning-loop/phases/03-source-study.md` for each
  important result: map which hypothesis justifies which step of the proof, find what breaks when
  a key hypothesis is dropped, ask whether hypotheses can be weakened, state the core idea in one
  to three sentences, and list the source's examples and counterexamples with the hypothesis each
  tests.
- **Techniques.** Identify the proof technique of each argument with
  `plasmalean-proof-techniques`, and record it in the assessment note so that later proof attempts
  can reuse it. If the source relies on a reusable technique missing from the registry, propose
  adding it.
- **Examples and counterexamples.** Use `plasmalean-examples-counterexamples` to check the
  source's examples against the project's exact definitions and conventions (units, Fourier and
  flux conventions, current orientation), and to test stated results on degenerate and boundary
  cases before mapping them onto existing claims.
- **Stress tests.** For a conjecture, a proof sketch, or a result whose hypotheses look incomplete
  or differ from the project's model, run
  `../plasmalean-reasoning-loop/phases/10-conjecture-stress-test.md` and record its
  classification: `plausible`, `refuted`, `needs_extra_hypotheses`, `known_or_near_known` or
  `open`.

Keep this analysis in a task folder `notes/reasoning/<YYYY-MM-DD>-source-<slug>/`, with a
`README.md` task card listing the sources, `02_literature_review.md`, and `02_examples.md` or
`04_research_trace.md` when examples or stress tests were run, following the layout in
`plasmalean-reasoning-loop`. The source-assessment note summarizes the conclusions and links to
this folder for the detailed analysis. For a short source with only one or two claims, the
analysis may go directly in the assessment note instead.

Do not run full proof attempts or explorations as part of this workflow. When a source claim
needs a proof, a repaired statement or further exploration, record it and offer it as a next
choice: `plasmalean-try-to-prove` for a precise claim, `plasmalean-explore-mathematics` for an
open direction.

## 4. Plan the note changes

Always create a **source-assessment note** (Kind: `source assessment`), one per source or per
coherent batch. It contains:
- the provenance;
- a short summary of the source;
- the extraction table;
- the checks and their results;
- the proof techniques, examples and stress-test classifications from the reasoning tools, with a
  link to the analysis folder under `notes/reasoning/` when there is one;
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

Finish with the commit hash, the analysis folder, unresolved source gaps or disagreements, and the
ready next choices that the sources opened, including suggested `plasmalean-try-to-prove` or
`plasmalean-explore-mathematics` tasks. If the sources add nothing new, report that without
manufacturing edits.

## Checklist

- [ ] sources acquired safely; provenance and hashes recorded; nothing executed
- [ ] every source read in full; extraction table with kind and locator per claim
- [ ] claims checked against compiled Lean, notes and audits; explicit content re-derived where
      cheap; contradictions investigated
- [ ] source study, techniques, examples and stress tests for substantive claims; analysis folder
      under `notes/reasoning/` linked
- [ ] source-assessment note created
- [ ] affected notes classified; in place only without implementation; method or patch notes
      otherwise
- [ ] registration, §13, index, audit items; site checked; committed with explicit paths and pushed
