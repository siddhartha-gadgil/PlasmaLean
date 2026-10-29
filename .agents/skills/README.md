# Skills

Agent skills for PlasmaLean, a theory-development and verification project for stellarator design
(`.claude` is a symlink to `.agents`, so these are also the Claude Code skills). The entry point is
`plasmalean-develop-theory`: it interprets `start`, `status`, `work on …` and `keep working`, keeps
the research graph (`G-*`, `Q-*`, `N-*` in `notes/implementation-plan.md`) and routes work to the
other skills.

| Skill | Use when |
| --- | --- |
| `plasmalean-develop-theory` | **Entry point.** `start` (strict audit first), `status`, `work on …`, discussion, `keep working`; maintaining goals, questions and notes; sub-agent coordination (file ownership, serialized heavy builds, verifying reports); autonomous work selection |
| `plasmalean-audit-domain` | strictly auditing existing and new code, especially every kernel declaration (no grandfathering); model choice and changes; reviewing a confinement or stability claim; red-team checklist, sanity triad plus risk-specific adversarial checks, regression theorems, audit record in the plan |
| `plasmalean-discover-theory` | existing results do not give the needed margin, bound, equilibrium or design condition: conjecture, proof, counterexample, refinement |
| `plasmalean-formalize-theory` | formalizing a sourced result (paper, book, complete proof) as reusable Lean theory above the kernel |
| `plasmalean-certify-numerics` | turning a numerical candidate into a kernel-checked certificate (exact arithmetic, validated enclosures, remainder bounds, KAM hypotheses, quadrature) |
| `plasmalean-design-stellarator` | advancing a stellarator candidate through verified gates with composed certificates; coil or boundary optimization, tradeoffs, tolerance studies |
| `plasmalean-model-materials` | coils, tape strain, quench, thermal and mechanical loads, plasma-facing materials, neutronics, lifetime and maintenance constraints |
| `plasmalean-lean-proofs` | writing or repairing any Lean code: tactic choice, concrete checks with `kernel_fact`/`bool_cert`/`eval_cert`/`fiv_cert` and the Kronecker certificates, the SubsetSum proof-term pattern, memory rules; no `decide` of any kind in new code |
| `plasmalean-workstation-update` | fetching, re-checking, merging and recording workstation runs (`workstation/*` branches; `Workstation.md`) |

Shared rules: Lean declarations are the validity gate (only compiled declarations count as
established; on-demand modules are spot-checked under the workstation policy); ≤ 6 GB per Lean
process and stale dependencies built one at a time; heavy numerics on the workstation; update the
notes and the plan after every work unit, including failures.

Worked references: `PlasmaLean/Kernel/Equilibrium.lean` with `PlasmaLean/Sanity/Equilibrium.lean`
(kernel and sanity), `PlasmaLean/Bridge/Contracts.lean` (common-witness composition),
`PlasmaLean/Certificates/README.md` (certificate formats and tactics), `PlasmaLean/SubsetSum.lean`
(proof-term pattern).
