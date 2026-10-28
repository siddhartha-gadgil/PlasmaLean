# Goals and method: generic guidance

How to choose and state goals for a LeanTheory project, distilled from the original project's goal
notes. Domain content belongs in `notes/implementation-plan.md` §0.

1. **Specify the output before choosing a method.** Write the target as a contract: model,
   object, quantifiers, observable and tolerance. Choose the technique (energy method,
   comparison principle, certificate, perturbation theorem) only afterwards.
2. **Separate the meanings of uncertainty.** Distinguish (a) arithmetic and discretization error,
   (b) uncertain parameters ranging over a set, (c) genuinely stochastic models, and (d) model
   discrepancy. Each needs a different kind of statement; never let a sample stand in for a
   uniform bound.
3. **Propagate omitted effects into the actual output.** When a model leaves out an effect, prove
   a template theorem "reference output + bound on the omitted term ⇒ bound on the real output",
   with every input of the bound produced by a theorem or a certificate.
4. **Prefer methods whose obligations are checkable.** Modified energies with cross terms,
   relative entropies and comparison principles reduce global claims to finitely many inequalities
   that certificates can discharge. Keep a negative fixture showing that the naive version fails.
5. **Shared scenario record.** All claims about one candidate refer to one record (parameters,
   witness, envelopes) so that their conjunction is meaningful.
6. **Conservative decision statements.** A decision ("the candidate meets the requirement")
   is stated with all assumptions listed and the margin it relies on; if the margin depends on an
   unproved input, say so.
7. **Activation rules.** Postpone ambitious goals explicitly, and record the condition (a proved
   theorem, a certificate, a measured datum) that reactivates each of them.
