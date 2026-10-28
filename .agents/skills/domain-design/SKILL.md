---
name: domain-design
description: Advance a candidate design in the user's domain, for a LeanTheory-based formalization, from a mathematical specification toward a constructible design with composed proof certificates. Use for parameter or shape optimization, design tradeoffs, operating envelopes, tolerance and uncertainty studies, or deciding which verified milestone a candidate has reached.
---

# Advance a design against explicit contracts

Read `notes/formalization/00-model-contracts.md`, `notes/implementation-plan.md` and the relevant notes in `notes/goals/`. Inspect the implemented kernel, theory, bridge and certificate modules before describing a capability as available. Designs live in `LeanTheory/Design/` (empty in the template: one subdirectory or module per design family).

Slots marked ‹replace: …› are to be filled in for your domain, ideally once in `notes/implementation-plan.md`, and then reused.

## 1. Freeze a design specification

Record, with units and sources:

- the system class and its parameters ‹replace: e.g. geometry, materials, operating point›;
- the operating envelope and the perturbation class ‹replace: ranges of each parameter, time horizon›;
- the target properties, each as a separate predicate ‹replace: e.g. existence, invariance, a quantitative bound, stability, feasibility›;
- manufacturing and measurement tolerances ‹replace: the uncertainty set›;
- external data and their validity envelopes ‹replace: measured constants, empirical laws›.

Source numerical requirements from a named study, standard or measurement. Use a symbolic envelope until such data exist; do not inherit illustrative constants from one source as universal limits.

## 2. The milestone ladder (verification levels)

Name the level a candidate has reached precisely; never round up. A generic ladder, to be specialized:

| Level | Meaning | Evidence |
| --- | --- | --- |
| L0 Specification | the design problem is stated as Lean predicates on decoded parameters | `Design/` definitions with docstrings, sanity triad for the laws used |
| L1 Candidate | a concrete candidate exists with exact (rational) data and provenance | data `def`s, source commit/solver/version, data hash |
| L2 Pointwise certificate | the target properties hold at the nominal candidate | kernel-checked certificates (`certify-numerics`) |
| L3 Envelope certificate | they hold for every state in the operating envelope / every member of a family | coverage + between-sample bounds, or a family certificate |
| L4 Robust certificate | they hold with margins over the whole tolerance set | margins propagated through every certificate, same uncertainty parameters |
| L5 Composed design theorem | one theorem in `Design/` concludes all target predicates for the candidate from the stated law instances only | `#print axioms` clean, listed in `scripts/check_axioms.lean` |

‹replace: your milestone ladder (domain-specific gates between and beyond these levels)›

## 3. Explore, then certify

1. Choose the next achievable level for the candidate.
2. Parameterize the design with explicit units and symmetry conventions.
3. Use theory to reduce the search space and derive sufficient conditions (`discover-theory`, `formalize-theory`). Use external solvers or optimizers ‹replace: your solvers› only as candidate generators; record version-specific conventions.
4. Optimize meaningful objectives but keep hard constraints separate: an objective penalty or its optimum is not a proof of feasibility.
5. Generate the exact certificates needed for the level (`certify-numerics`, `lean-proofs`); generators validate every emitted bound in exact arithmetic.
6. Propagate tolerances through margins. Recompute every dependent certificate after any change of data, parameters or model.

Do not require global optimality to certify one useful feasible design. Claim an optimum only with a separate optimality certificate.

## 4. Compose certificates across the layers

The trusted chain is **Kernel → Theory → Bridge → Certificates → Design**:

- **Kernel**: the model law as a typeclass hypothesis (never an axiom).
- **Theory**: general consequences of the law (conservation, estimates, existence).
- **Bridge**: theorems turning finite, checkable data into the semantic statement ("certificate ⇒ property for every trajectory / parameter in the box").
- **Certificates**: the concrete checks, closed by `kernel_fact`, `bool_cert`, `eval_cert`/`fiv_cert`, family certificates or a SubsetSum-pattern predicate; no `decide`.
- **Design**: the composed theorem about the candidate.

Rules:

- All certificates must refer to the same decoded data, parameters, operating interval and uncertainty variables; preserve correlations between inputs.
- Compose only when one theorem's conclusion supplies the next one's hypotheses in the same norm and on the same domain.
- Do not change quantifiers: `∀ parameter, ∃ state` is not `∃ state, ∀ parameter`. A pointwise certificate is not an envelope certificate.
- Keep a design record of the exact predicates proved and their evidence instead of one ambiguous `Good` flag.

## 5. Tradeoff and tolerance studies

- State tradeoffs as families: a certified bound as a function of the design parameter, certified on boxes covering the range, rather than a few sampled points.
- For tolerances, certify the property on the whole uncertainty box and report the margin; report the largest box you could certify, not the one you hoped for.
- A failure to certify is an open item, not evidence that the design fails; an exact counterexample is.

## 6. When to use the workstation

Use the workstation (`Workstation.md`, `scripts/workstation/run.sh`, task scripts from `scripts/workstation/tasks/TEMPLATE.sh`) when a step needs heavy numerics, emits large generated Lean files, or a first build would exceed the laptop budget (6 GB per Lean process, small groups of heavy modules). Bring results back with `workstation-update`; on-demand design families can be separate top modules not imported by `LeanTheory.lean`.

## 7. Definition of done per milestone

A milestone is done when:

- the level's evidence (table in §2) is compiled with zero warnings, no `sorry`/axiom/`decide`, and only standard axioms (`#print axioms`, `scripts/check_axioms.lean`);
- accepted and rejected fixtures show the certificate is not vacuous;
- an assumption ledger and scope statement exist (`audit-domain`);
- `notes/implementation-plan.md` has a dated entry: level reached, declaration names, margins, cost of the build, remaining missing certificates and the next target.

## Worked illustration: the oscillator template

Milestone (L3 for a toy "design"): **a certified amplitude bound for a family of initial states.**

- **Specification**: oscillator `params23` (`m = 2`, `k = 3`), family `initialStates` of 21 rational states; target predicate "`3 x(t)² ≤ 1` for all `t`".
- **Kernel**: `LeanTheory/Kernel/Example.lean`: the law `OscillatorLaw p x v` and `energy_conserved`, `potential_le_energy`. Sanity triad in `LeanTheory/Sanity/Example.lean`.
- **Bridge**: `LeanTheory/Bridge/Example.lean`, `amplitude_bound`: initial energy at most `E` implies `k x(t)² ≤ 2E` for all `t` (conservation composed with `potential_le_energy`).
- **Certificate**: `LeanTheory/Certificates/Example.lean`, `initialStates_energy_le` (by `kernel_fact`, one rational comparison per state), with `energyQ_cast` linking exact and real energy.
- **Composed theorem**: `amplitude_cert`: every trajectory obeying the law and starting in the family satisfies the bound. Rejected fixture `initialStates_not_le_small` shows the bound is not vacuous.
- **Ledger**: the only assumption is the law instance `[OscillatorLaw params23 x v]`; scope: this family, this parameter pair, all time.

Moving it to L4 would mean certifying the same bound on a box of parameters `(m, k)` and initial states around the family, with a reported margin.

## Deliver

Candidate data and provenance, the level reached, compiled declaration names, quantitative margins, remaining law assumptions, missing certificates, model-validity evidence, and the next theoretical or experimental target.
