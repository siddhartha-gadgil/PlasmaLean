# notes/goals/

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-22` |
| Title | Goal proposals of 24 October 2026: model adequacy and probabilistic goals (overview, probabilistic, deterministic, milestones) |
| Kind | goal proposals (research approach) |
| Addresses | `G-3`; plan §12; supports `G-1`, `G-2`, `G-8` |
| Depends on | plan §0, §11, §12; N-19 (evolution gates) for the N1 error bounds |
| Dependency requirement | none compiled; the cross-references "§12 D0–D4, K0–K6" point to a plan version that was not supplied and remain unresolved |
| Produces | probabilistic goals P1–P4, deterministic goals N1–N3, implementation milestones and stopping criteria (local labels, not roadmap gates or `N-*` IDs) |
| Difficulty | research (N1 needs a finite-time observable error bound on a named model; P1 a certified loss fraction) |
| Status | stated (proposals); D/K cross-references unresolved; no Lean results |
| Lean evidence | none. Planned, not present: `ObservableErrorBound`, `ProjectedModelDefect`, `ModifiedEnergyBound`, `DecisionMarginCertificate`, `ErrorRadiusBound`, `EvolutionResidualBound` |
| Audit evidence | not audited |
| Last updated | 3 November 2026: metadata added |

**Current state (3 November 2026).** These proposals use the legacy goal meanings. Since the stellarator contract of 30 October, G-1 is current-free confinement (C1 + C4), stability is G-4 (C3), omnigeneity G-10 (C2) and thermal performance G-2 (C5); "G1: confinement and stability" below should be read accordingly. G-3 remains proposed with no Lean evidence; the next step is to choose one N1 observable on a contract candidate.

- [`method.md`](method.md): how to choose and state goals: outputs before methods, kinds of
  uncertainty, propagating omitted effects, checkable obligations, shared scenario records,
  conservative decisions and activation rules (generic guidance from the LeanTheory template, with
  PlasmaLean examples).

Proposals of 24 October 2026 for goal G-3 (model adequacy and probabilistic goals; plan §12). They
report no Lean results. G-1 (confinement and stability) and G-2 (thermal performance) remain the
core.

- [`plasmalean-goals-overview.md`](plasmalean-goals-overview.md): the decision and priorities.
- [`probabilistic-goals-and-techniques.md`](probabilistic-goals-and-techniques.md): P1–P4
  (finite-time loss under a birth distribution, justified input uncertainty, certified Monte Carlo).
- [`deterministic-goals-and-techniques.md`](deterministic-goals-and-techniques.md): N1–N3 (one
  omitted effect on a design observable, a minimal activated correction, decision infrastructure)
  and transferable techniques.
- [`implementation-milestones.md`](implementation-milestones.md): reviewable outputs.

P1–P4 and N1–N3 are local labels: not the roadmap gates P0–P9 and not research-note IDs `N-*`. The
references to "§12 D0–D4, K0–K6" point to a plan version that was not supplied and remain
unresolved.
