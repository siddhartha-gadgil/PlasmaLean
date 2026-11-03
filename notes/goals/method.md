# Goals and method: how to choose and state goals

Guidance for stating goals (`G-*`) and questions (`Q-*`) in PlasmaLean. It follows the generic
method of the LeanTheory template, which was distilled from this project's goal notes, with
PlasmaLean examples. The domain content itself lives in the plan,
[notes/implementation-plan.md](../implementation-plan.md): the stellarator contract and the
registries RG.1–RG.3. This file is part of the note group N-22.

Maintain several goals and questions when the domain requires them. Give each a stable identifier,
record parent and support relationships, and introduce auxiliary questions rather than forcing every
line of work into one top-level goal. Example: G-1 (confinement and stability) and G-2 (thermal
performance) are both core goals; Q-16 (a quasisymmetric solution) supports both.

1. **Specify the output before choosing a method.** Write the target as a contract: model, object,
   quantifiers, observable and tolerance. Choose the technique (energy method, comparison
   principle, certificate, perturbation theorem) only afterwards.
   - *Example:* the stellarator contract C1–C5 was fixed before any candidate was chosen.
   - *Example:* Q-16's vacuum criterion (an off-QA Boozer defect at most a stated multiple of |ι| on
     nested certified tori) was decided before the Dommaschk certificate was designed.
2. **Separate the meanings of uncertainty.** Each kind needs a different kind of statement; never
   let a sample stand in for a uniform bound.
   - (a) arithmetic and discretization error: certificates with remainders;
   - (b) uncertain parameters ranging over a set: statements for every B₀R₀ in an interval;
   - (c) genuinely stochastic models: the probabilistic goals P1–P4;
   - (d) model discrepancy: supplied laws named in every scope statement.
3. **Propagate omitted effects into the actual output.** When a model leaves out an effect, prove a
   template theorem "reference output + bound on the omitted term ⇒ bound on the real output", with
   every input of the bound produced by a theorem or a certificate.
   - *Example:* the per-bounce defect bound `approxOmnigenousOn_of_defect_le` turns a certified QA
     defect into approximate omnigeneity.
4. **Prefer methods whose obligations are checkable.** Modified energies with cross terms, relative
   entropies and comparison principles reduce global claims to finitely many inequalities that
   certificates can discharge. Keep a negative fixture showing that the naive version fails.
   - *Example:* the counterexample in N-2 shows that the uncorrected relative-entropy identity fails.
5. **Shared scenario record.** All claims about one candidate refer to one record (parameters,
   witness, envelopes), so that their conjunction is meaningful.
   - *Example:* all Dommaschk results refer to `DommaschkQA2R.field DommaschkQA2R.candidate`.
   - *Example:* the composition lemmas in `PlasmaLean/Bridge/Contracts.lean` require a common
     witness.
6. **Conservative decision statements.** A decision ("the candidate meets the requirement") is
   stated with all assumptions listed and the margin it relies on. If the margin depends on an
   unproved input, say so.
   - *Example:* the README's "Against the contract, honestly" list states, for each clause, what is
     proved and what is not.
7. **Activation rules.** Postpone ambitious goals explicitly, and record the condition (a proved
   theorem, a certificate, a measured datum) that reactivates each of them.
   - *Example:* Q-1 (trapped alphas) is parked until the per-bounce remainders of N-17 exist.
