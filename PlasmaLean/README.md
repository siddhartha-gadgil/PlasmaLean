# PlasmaLean/

The Lean library: the checked layer of a theory-development workspace for stellarator design.
Research may begin in `notes/`, but a result becomes an established prerequisite only when its
Lean declaration compiles with the standard axioms. The root [`PlasmaLean.lean`](../PlasmaLean.lean)
imports the **default build** (about 670 modules, audited by `scripts/check_axioms.lean`); heavy
certificate families are **on-demand top modules** in `Design/` (audited by
`scripts/check_axioms_heavy.lean`).

The trusted chain is **Kernel → Theory → Bridge → Certificates → Design**, with `Sanity` guarding
the kernel:

| Folder | Content | Start with |
| --- | --- | --- |
| [`Kernel/`](Kernel/README.md) | Domain model: definitions and laws as typeclasses, no axioms | `Kernel/Equilibrium.lean` |
| [`Sanity/`](Sanity/README.md) | Degenerate cases, concrete instances, counterexamples | `Sanity/Equilibrium.lean`, `Sanity/ProbeEscape.lean` |
| [`Theory/`](Theory/README.md) | Reusable mathematics: fields, KAM, kinetics, stability, transport | `Theory/Fields/TorusTrapping.lean` |
| [`Bridge/`](Bridge/README.md) | Common-witness composition of separate contracts | `Bridge/Contracts.lean` |
| [`Certificates/`](Certificates/README.md) | Certificate formats, soundness theorems, proof-term builders and tactics | `Certificates/KernelFact.lean`, `Certificates/EvalCert.lean` |
| [`Design/`](Design/README.md) | Concrete candidates and their certificates; on-demand top modules | `Design/RationalStellaratorFieldLines.lean` |
| [`SubsetSum.lean`](SubsetSum.lean) | Reference pattern for building large proofs as explicit proof terms | — |
| `Basic.lean` | Starter declaration retained from the scaffold (no domain claim) | — |

The untrusted, natively compiled proof builders are in [`../PlasmaLeanMeta/`](../PlasmaLeanMeta/README.md).

Conventions: files start with `module`; the API is `public`/`@[expose]`; `meta` imports only for
proof builders; every module, definition and theorem has a docstring; no `sorry`, `axiom` or
`native_decide`, and no `decide` of any kind in new code (legacy `decide +kernel` lines are being
migrated, plan Phase 16); zero warnings; ≤ 6 GB peak memory per module. See the skills in
`.agents/skills/` (entry point `plasmalean-develop-theory`) and `notes/domain-libraries.md`.
