# Skills

Agent skills for PlasmaLean, a theory-development and verification project for stellarator design
(`.claude` is a symlink to `.agents`, so these are also the Claude Code skills). The entry point is
`plasmalean-develop-theory`: it interprets `start`, `work status` / `summarise work`, `work on …` and `keep working`
(exact phrases, treated as explicit invocations), keeps the research graph (`G-*`, `Q-*`, `N-*` in
`notes/implementation-plan.md`) and routes work to the other skills. The workflow follows the
[LeanTheory](https://github.com/siddhartha-gadgil/LeanTheory) template; see
[docs/GettingStarted.md](../../docs/GettingStarted.md). Each skill may have an `agents/openai.yaml`
with its display name and default prompt.

| Skill | Use when |
| --- | --- |
| `plasmalean-develop-theory` | **Entry point.** `start` (strict audit first), `work status`, `summarise work`/`summarize work`, `work on …`, discussion, `keep working`; maintaining goals, questions and notes; sub-agent coordination (file ownership, serialized heavy builds, verifying reports); autonomous work selection |
| `plasmalean-audit-domain` | strictly auditing existing and new code, especially every kernel declaration (no grandfathering); model choice and changes; reviewing a confinement or stability claim; red-team checklist, sanity triad plus risk-specific adversarial checks, regression theorems, audit record in the plan |
| `plasmalean-discover-theory` | existing results do not give the needed margin, bound, equilibrium or design condition: conjecture, proof, counterexample, refinement |
| `plasmalean-formalize-theory` | formalizing a sourced result (paper, book, complete proof) as reusable Lean theory above the kernel |
| `plasmalean-certify-numerics` | turning a numerical candidate into a kernel-checked certificate (exact arithmetic, validated enclosures, remainder bounds, KAM hypotheses, quadrature) |
| `plasmalean-design-stellarator` | advancing a stellarator candidate through verified gates with composed certificates; coil or boundary optimization, tradeoffs, tolerance studies |
| `plasmalean-model-materials` | coils, tape strain, quench, thermal and mechanical loads, plasma-facing materials, neutronics, lifetime and maintenance constraints |
| `plasmalean-lean-proofs` | writing or repairing any Lean code: tactic choice, concrete checks with `kernel_fact`/`bool_cert`/`eval_cert`/`fiv_cert` and the Kronecker certificates, the SubsetSum proof-term pattern, memory rules; no `decide` of any kind in new code |
| `plasmalean-add-note` | recording a note after a discussion, result, failure, source assessment or design decision ("add a note", "make a note", "record this"): new vs update, template, ID, registration in the research graph and index, publish |
| `plasmalean-modify-notes` | changing what notes say ("update notes", "modify notes", "add notes"): surveys notes and their metadata (`scripts/notes/implementation_status.py`), edits in place only notes with no Lean implementation, and records changes to wholly or partially implemented notes as new method or patch notes |
| `plasmalean-update-notes-from` | "update notes from <files>": analysing given theory sources (papers, briefs, drafts, external Lean files) claim by claim, checking them against compiled Lean and the notes, writing a source-assessment note, then updating notes as in `plasmalean-modify-notes` |
| `plasmalean-workstation-update` | fetching, re-checking, merging and recording workstation runs (`workstation/*` branches; `Workstation.md`) |

Shared rules: Lean declarations are the validity gate (only compiled declarations count as
established; on-demand modules are spot-checked under the workstation policy); at most 12 GB of
Lean memory at a time (heavy modules alone, up to 3 light ones at once; stale dependencies by
frontier, never through one `lake build Top`); heavy numerics on the workstation; update the
notes and the plan after every work unit, including failures.

Worked references: `PlasmaLean/Kernel/Equilibrium.lean` with `PlasmaLean/Sanity/Equilibrium.lean`
(kernel and sanity), `PlasmaLean/Bridge/Contracts.lean` (common-witness composition),
`PlasmaLean/Certificates/README.md` (certificate formats and tactics), `PlasmaLean/SubsetSum.lean`
(proof-term pattern).
