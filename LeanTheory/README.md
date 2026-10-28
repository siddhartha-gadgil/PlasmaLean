# LeanTheory/

The Lean library. Every module is imported by the root [`LeanTheory.lean`](../LeanTheory.lean)
(the default build) and audited by `scripts/check_axioms.lean`.

| Folder | Content | Start with |
| --- | --- | --- |
| [`Kernel/`](Kernel/README.md) | Domain model: definitions and laws as typeclasses, no axioms | `Kernel/Example.lean` |
| [`Sanity/`](Sanity/README.md) | Degenerate cases, concrete instances, counterexamples | `Sanity/Example.lean` |
| [`Bridge/`](Bridge/README.md) | Composition theorems between laws, theory and certificates | `Bridge/Example.lean` |
| [`Theory/`](Theory/README.md) | General, domain-independent mathematics | `Theory/KAM/KamSequence.lean` |
| [`Certificates/`](Certificates/README.md) | Certificate formats, soundness theorems, proof-term builders | `Certificates/Example.lean` |
| [`Design/`](Design/README.md) | Concrete certified candidates (empty in the template) | — |
| [`SubsetSum.lean`](SubsetSum.lean) | Reference pattern for building large proofs as explicit proof terms | — |

Conventions: files start with `module`; the API is `public`/`@[expose]`; `meta` imports only for
proof builders; every module, definition and theorem has a docstring; no `decide` of any kind,
no `sorry`/`axiom`; zero warnings (100-character lines).
