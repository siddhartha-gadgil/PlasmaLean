# Research note template

Copy this template for each substantial unit of PlasmaLean theory development. Use stable `N-*`,
`G-*` and `Q-*` identifiers from the "Research graph" part of `notes/implementation-plan.md`.
Remove guidance text after filling it in.

Discovery notes live in `notes/theory/` (kebab-case file names, indexed in
`notes/theory/README.md`); formalization specifications live in `notes/formalization/`. New notes
use this template. Existing notes keep their status tags (**published**, **formal asymptotic**,
**proved informally**, **conjectured**, **refuted**, **lead**, or **[Lean]**/**[num]**/**[todo]**)
and get the metadata table below when they are next substantially edited.

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-...` |
| Title | ‹short descriptive title› |
| Kind | ‹source synthesis / definition / conjecture / research approach / proof / counterexample / computation / formalization / certificate / design› |
| Addresses | ‹`G-*`, `Q-*`; plan track (T1–T10), rung (M0–M6) or gate (E0–E8) if relevant› |
| Depends on | ‹note IDs and Lean declaration names› |
| Dependency requirement | ‹what exact statement/status is needed from each dependency› |
| Produces | ‹claims, definitions, data, declarations, new notes or registry updates› |
| Difficulty | ‹routine / moderate / hard / research; explain the main source of difficulty› |
| Status | ‹exploratory / stated / proof-ready / lean-ready / verified / blocked / refuted / superseded› |
| Lean evidence | ‹module and declaration names (default build or on-demand), or `none`› |
| Audit evidence | ‹audited commit and finding IDs, or `not audited`› |
| Last updated | ‹date and summary› |

## Purpose and scope

State the problem, why it matters for the stellarator goals, the intended output and what is
outside scope. Give all models (vacuum, ideal MHD, Littlejohn guiding centre, radial transport,
...), domains, units (SI or model units), conventions, quantifiers and parameter ranges needed to
understand the claim.

## Dependencies

For each dependency, state whether it is a compiled theorem, a supplied model law or empirical
assumption (a kernel typeclass instance), a sourced but unformalized result, or a conjecture. An
unverified dependency may guide conditional exploration but may not be used as an established
premise.

## Sources and prior work

Give stable source identifiers (arXiv ID, DOI) and theorem/equation/page locators, following the
extraction protocol of `notes/formalization/09-literature.md`. Distinguish published theorems,
formal asymptotic calculations, numerical observations and empirical fits. Record
user-contributed ideas and their provenance without attributing more than is known.

## Theory development

Record definitions, conjectures, proof attempts, calculations, counterexample searches and
refinements. Preserve failed approaches when they identify a reusable barrier. Keep untrusted
numerics reproducible: scripts in the repository (`scripts/<family>/`), not only in `/tmp`.

## Claims and evidence

List each claim separately with one status: conjecture, proof sketch, complete mathematical proof,
numerical observation, sourced theorem or compiled Lean theorem. For a compiled theorem, give the
declaration name, its assumptions (law instances, supplied solutions or reductions) and whether
its module is in the default build or on demand.

## Difficulty, barriers and readiness

Explain the mathematical difficulty, missing theory, missing source, model ambiguity, library gap
or computational cost (CPU, memory per process, olean size). Say whether the note can generate Lean
now. If not, name the smallest next step that would change its readiness.

## Outputs and next dependencies

Record changes to goals and questions, new notes, declarations, counterexamples and suggested next
work. Identify which downstream notes become ready, if any, and update the plan's registries.
