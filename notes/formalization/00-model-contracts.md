# Model contracts and the meaning of a design proof

A formalization can prove precise implications from mathematical models and data envelopes. A
practical claim needs several such implications, plus evidence that the models and envelopes
apply to the intended regime. Lean checks the implications; validation supplies the evidence
about the regime. This note fixes how claims are stated so that the two are never confused.

## Contracts

Use separate predicates with explicit parameters instead of one unqualified `Good : Prop`. Each
contract states the model, the object, the quantifiers and what is controlled. A template:

| Predicate | Required content |
| --- | --- |
| `SolutionExists` | Solution space, equations, boundary conditions, constraints, distance from a numerical candidate |
| `Invariant` / `Barrier` | The set, the dynamics, the time interval, and whether existence of solutions is proved or assumed |
| `BoundedUntil` | Dynamics (full or reduced), initial set, region, time horizon, reduction error |
| `LinearStable` | Reference state, admissible perturbation space, boundary model, norm or observable, definition of stability |
| `NonlinearStable` | Evolution model, solution class, initial neighbourhood, norm (modulo symmetries), interval of existence |
| `ComponentFeasible` | Geometry, loads, constitutive data, tolerances, degradation |
| `DesignFeasible` | Explicit conjunction of the required contracts for the same candidate and operating states |

‹replace: the contracts of your domain›. In the worked example the contract is "every trajectory
obeying `OscillatorLaw params23` and starting in `initialStates` satisfies `3 x(t)² ≤ 1` for all
`t`" (`Certificates/Example.amplitude_cert`): model, initial set, quantifiers and conclusion are
all explicit.

Record each assumption's origin: mathematical theorem; chosen model law; measured datum or
empirical fit; requirement; or unresolved research hypothesis. Keep arithmetic error,
discretization error, parameter uncertainty and model discrepancy separate.

## Architecture

The domain kernel is a set of definitions and law interfaces, distinct from Lean's logical kernel.

| Group | Purpose |
| --- | --- |
| `Kernel` | Domain objects, constants, model predicates, laws as typeclasses |
| `Sanity` | Witnesses, limits, symmetry, conservation, counterexamples to overbroad definitions |
| `Theory` | Derived, domain-independent mathematics |
| `Certificates` | Exact data, enclosures, checkers and proved checker soundness |
| `Bridge` | Reductions, certified reconstruction, composition between models and results |
| `Design` | Specifications and concrete certified candidates |

Do not introduce project axioms. Put laws in structures/typeclasses and take them as hypotheses.
Do not manufacture universal instances for empirical laws; prove simple consistent instances to
guard against vacuity. For each theorem record: declaration, source locator, hypotheses, units,
boundary and regularity conditions, norm, quantifiers, model, computational errors, empirical
inputs and remaining gaps. No result becomes established merely by appearing in a typeclass field.

## Corrections before formalizing

Starting notes often contain statements that are true only under unstated hypotheses. Before
formalizing, list each such claim with its precise replacement (‹replace: your corrections›).
Typical patterns:

| Loose claim | Precise replacement |
| --- | --- |
| "A positive lowest discretized eigenvalue proves stability" | For a conforming trial space the minimum Rayleigh quotient bounds the continuum infimum from *above*; certify omitted modes and errors before claiming a lower bound |
| "Strict coercivity is the goal" | Neutral modes and symmetries may preclude it; choose the quotient or observable the model supports |
| "Perturbation theory preserves the structure" | State which objects persist, under which quantitative non-resonance and smallness hypotheses |
| "The radii polynomial needs a negative root" | Require an admissible positive radius where the polynomial is negative, plus contraction and domain conditions |

## The model hierarchy

Select the model by the phenomenon being certified (‹replace: your model ladder›). Every model
is a model: reduction arrows between levels require quantified theorems or explicitly supplied
error envelopes.

## Certificate composition

Let `a` describe the candidate and `θ ∈ U` the uncertain parameters. The useful robust statement
is typically `∀ θ ∈ U, ∃ e_θ, P₁(a, θ, e_θ) ∧ P₂(e_θ, θ) ∧ …` with the **same witness** `e_θ` in
every part: independent proofs of `∃ e, P₁ e ∧ P₂ e` and `∃ e, P₁ e ∧ P₃ e` do not give a common
witness. Prefer a unique (gauge-fixed) branch where possible, or carry the witness through
dependent certificate records.

If a reference form `q_{θ₀}` has margin `c > 0` and a theorem gives
`|q_θ(ξ) − q_{θ₀}(ξ)| ≤ L ‖θ − θ₀‖ ‖ξ‖²` with `‖θ − θ₀‖ ≤ R` on `U`, then `L R < c` yields the
robust margin `c − L R`. Such a perturbation estimate is a theorem to prove, not a consequence of
continuity.

## First implementation targets

1. A small kernel interface with one law and its sanity triad (as in `Kernel/Example`).
2. A certificate/assumption record without any domain-specific global theorem.
3. Exact interval containment and one useful bound, certified end to end (as in
   `Certificates/Example`).
4. An abstract energy or comparison theorem (`Theory/Stability/AbstractEnergy`,
   `RiccatiComparison`) before the continuum bridge.
