# Skill: Composition of Contracts on a Common Witness

**Pre-condition:** The claim combines several separately proved properties of a design
(equilibrium, stability, transport or confinement, engineering components) into one design
statement, possibly over an operating range or uncertainty set. Use it in Bridge-level proofs
and whenever a result is assembled from theorems proved in different modules.

**Goal:** Prove that a single object (the same equilibrium state, for each parameter in the set)
satisfies every contract clause at once, so the composed claim is not a conjunction of statements
about different objects.

**Instructions:**
1. **Name the witness.** Fix the design `d`, the parameter set `U` and a branch `θ ↦ e(θ)` of
   states. Every clause is a predicate on `(d, θ, e(θ))`.
2. **Check that each component theorem is about that witness**, with compatible definitions,
   units, normalizations, boundary conditions and parameter ranges. A stability theorem for one
   equilibrium and a transport theorem for another do not compose.
3. **Quantifier order.** The claim is `∃ branch, ∀ θ ∈ U, all clauses`, not
   `∀ clause, ∃ state`. Separate existence proofs give different witnesses unless uniqueness is
   proved (`compose_of_unique`).
4. **Compose:** with all clauses proved on the branch, `compose_branch` gives
   `RobustDesign C d U`. Restrict to smaller sets with `robust_mono`.
5. **Test with an incompatible pair:** a fixture where each clause has some witness but no
   common one shows that the common-witness requirement has content (`incompatible_witnesses`).
6. **Record which clauses are supplied** (hypotheses, external reductions) and which are proved; a
   composed result is only as strong as its weakest clause.

**Lean:** `PlasmaLean/Bridge/Contracts.lean`; contract clauses C1–C5 in
`notes/formalization/00-model-contracts.md`; skill `plasmalean-design-stellarator` for the gates.
