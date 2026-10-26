# PlasmaLean: probabilistic goals, deterministic additions and priorities

**Decision note — 24 October 2026.** This is a proposed extension of the current PlasmaLean implementation plan, especially §§0, 11 and 12. It does not report new Lean implementations or new mathematical results. The priority judgments below are recommendations for this project, not universal rankings of plasma physics.

## 1. The decision

Continue the original deterministic goals **G1: confinement and stability** and **G2: thermal performance**. Add a targeted programme **G3: model adequacy and useful refinements**, and develop statistical performance criteria when they answer a practical design question.

The immediate probabilistic work should concern finite-time particle loss and deposition, justified uncertainty in inputs, and reliable computation of these quantities. A new stochastic physical equation is conditional work. The immediate deterministic addition should quantify the effect of a selected omitted term on a design observable. Modified energies and driven relative entropy are methods that can improve the existing G1/G2 programme as well as this addition.

A complete microscopic particle-to-MHD derivation is outside the active and expected later roadmap. A particular estimate from that literature remains eligible when it resolves a named problem.

### Companion notes

| File | Purpose |
| --- | --- |
| [probabilistic-goals-and-techniques.md](probabilistic-goals-and-techniques.md) | P1–P4, practical value, probability laws, theorem contracts and numerical methods. |
| [deterministic-goals-and-techniques.md](deterministic-goals-and-techniques.md) | N1–N3 and methods serving both the original deterministic goals and the new adequacy work. |
| [implementation-milestones.md](implementation-milestones.md) | First deliverables, proof obligations, meaningful fixtures, dependencies and stopping criteria. |

Keep these four notes together when adding them to the repository. P1–P4 are local probabilistic-goal labels, distinct from the older formalization roadmap's P0–P9 gates. The P and N identifiers below classify deliverables; they do not replace the D0–D4 and K0–K6 work-package identifiers of the plan version these notes were written against.

> **Editorial note (26 October 2026).** The identifiers "§12 D0–D4", "§12 K0–K6" and "§12.10" refer to a version of the implementation plan that was not supplied; they do not exist in [the current plan](../implementation-plan.md). The nearest current equivalents are the evidence gates E0–E8 (plan §11.2), the deterministic additions N1–N3 and probabilistic items P1–P4 (plan §12), and the phases of plan §10. No mapping of individual D/K items to these is implied; the D/K labels below are kept only as written.

## 2. What “probabilistic” means here

Four distinct choices can introduce probability:

1. **A population or launch distribution.** Individual orbits can be deterministic while the proportion that reaches a wall is a probability under a specified birth distribution.
2. **Uncertain inputs.** Coil errors, profiles or parameters can be assigned a justified probability law. Without such a law, a deterministic uncertainty set is preferable.
3. **A randomized algorithm.** Monte Carlo can estimate an integral defined entirely by deterministic dynamics.
4. **A stochastic physical approximation.** A collision or fluctuation model can describe random paths, subject to its own applicability and calibration requirements.

A deterministic kinetic PDE for a density is also compatible with several of these interpretations. Adding velocity variables or a Landau collision operator is not, by itself, adding physical randomness. No part of this programme assumes a universal Gaussian correction centred on an MHD solution.

Law et al.'s stellarator study is a direct example of the distinction: randomized estimation and variance reduction are applied to collisionless orbit calculations [R1].

## 3. Probabilistic goals and practical priority

| ID | Concrete deliverable | Practical importance | Scheduling decision |
| --- | --- | --- | --- |
| **P1 — Finite-time population performance** | Bounds on loss probability, energy retained/deposited, confinement-time statistics or a specified wall-load observable for a declared launch law. | High when energetic-particle heating or loss is relevant to the selected candidate. Count loss, energy loss and local wall loading are different quantities. | First probabilistic application, using the simplest justified dynamics. |
| **P2 — Uncertainty in a design decision** | Bounds on the chance of violating a specified requirement under defensible input distributions; or robust deterministic bounds when distributions are unavailable. | High for practical confidence in a candidate. A nominal calculation alone does not answer sensitivity to operating or construction errors. | Record uncertainties immediately; add probabilistic propagation where data justify it. |
| **P3 — Reliable randomized computation** | An estimator with a valid finite-sample guarantee and a complete error budget; a demonstrated cost reduction is a separate success criterion. | Potentially high when repeatedly estimating expensive observables. It is an algorithm objective, not extra plasma physics. | Benchmark alongside P1 or P2, without waiting for a new stochastic model. |
| **P4 — A justified stochastic refinement** | A selected stochastic collision/fluctuation model whose effects and remaining discrepancy are assessed for the target observable. | Potentially essential in a relevant regime, but no general necessity has been established for the present candidate. | Activate only after a consequential omission is identified. |

P1 adds an ensemble performance criterion; it does not silently weaken G1's existing all-orbit statements. Expected deposited energy alone also does not imply a high-probability lower bound on the entire temperature history. That stronger claim needs a spatial/temporal source model and a thermal evolution argument.

For P2, **uncertainty assessment** and **stochastic optimization** are different commitments. The latter need not improve a design. In one studied class of coil perturbations, Wechsung et al. found substantially more benefit from a posteriori adjustment than from stochastic optimization [R2]. The proposed priority is therefore to understand the uncertainty first.

P3 can be useful even if P4 is never activated. Conversely, an important missing effect may be better represented by a deterministic kinetic equation than by a stochastic closure.

## 4. New deterministic deliverables

| ID | Deliverable | What is new | Priority |
| --- | --- | --- | --- |
| **N1 — Observable error from omitted effects** | A finite-time bound transferring a justified closure/model defect to the quantity used in a decision. | G1/G2 certify the chosen equations; N1 connects a specified model difference to a decision margin. | Highest priority among the modelling additions. |
| **N2 — The smallest adequate deterministic correction** | A targeted fluid closure, kinetic species, orbit correction or hybrid response that resolves the identified discrepancy. | Additional physics or state variables, still governed by deterministic equations if appropriate. | Conditional on N1/diagnostic evidence or unresolved consequential uncertainty. |
| **N3 — Decision certificates and validity diagnostics** | A traceable composition of numerical, input and model allowances, with a conclusion of certified, conditional, inconclusive or inadequate. | A shared decision layer supporting G1/G2, N1/N2 and P1–P4; not another independent physical objective. | Immediate, lightweight. |

For example, suppose a proposed heat-flux closure has a quantified defect. N1 asks how that defect changes a thermal bound over the chosen burn interval. N2 asks whether one improved closure is enough when the allowance is too large or unresolved. N3 records whether the resulting bound actually establishes the stated requirement and on what evidence.

If a theorem's hypotheses fail, or its error bound exceeds the design margin, the certificate is inconclusive. That is not proof that the physical approximation fails. A controlled, consequential discrepancy is a different kind of evidence. Verification and empirical validation remain separate [R3].

## 5. Technique map

| Technique | Probabilistic use | Existing deterministic G1/G2 use | New deterministic N1/N2 use | Disposition |
| --- | --- | --- | --- | --- |
| Modified energy and hypocoercivity | Control an appropriate kinetic density/semigroup or estimator correlation time when hypotheses hold. | Sharper stability and residual propagation for a selected actual operator. | Propagate a model defect with less amplification. | Priority pilot, D1. |
| Driven relative entropy | Compare suitable density laws; supply an observable bound with the required inequalities. | Stability around a driven hot profile, including heating and boundary terms. | Compare a chosen refined model with a reference state. | Priority pilot, D2. |
| Deterministic barriers, stopped-process barriers and backward equations | Finite-time hitting probabilities or path rewards. | Existing invariance/comparison methods remain useful; generator changes require a new theorem. | Bound the effect of a selected correction on a loss observable. | Start with P1's simplest justified dynamics. |
| Residual and observable-error estimates | Separate solver bias from sampling uncertainty. | Verified evolution and thermal bands. | Closure defect → evolution error → observable error. | Shared early work, K3. |
| Control variates, multifidelity estimation and importance sampling | Lower variance/cost while preserving the target and valid confidence. | Faster integration of an observable of a deterministic model. | Cheaper comparison of a baseline with a targeted refinement. | Benchmark under K5; no promised generic speedup. |
| Moment methods, micro–macro decompositions and kinetic closures | May support a stochastic representation or population model. | No automatic improvement to unchanged MHD. | Develop a specific deterministic correction or estimate. | On demand. |
| Phase mixing and adapted norms | Possible kinetic density/observable control. | Useful only when the chosen transport actually couples the relevant modes. | Analyse a selected kinetic response. | Scoped D4 study, not a universal damping claim. |
| Cumulants, collision histories and propagation of chaos | Potentially useful for an interacting-particle approximation requiring dependence control. | Direct benefit for fixed-model MHD remains unestablished. | A specific comparison estimate may be useful. | Reference only until a concrete need is demonstrated. |

Villani's hypocoercivity provides relevant deterministic tools [R4]. These tools must be adapted to the chosen operator, domain, invariant modes and forcing. An energy functional cannot manufacture decay of a real neutral mode.

Deng–Hani–Ma provide hard-sphere correlation/derivation techniques [R5, R6]. Independent sampling of prescribed-field trajectories does not require that machinery. Their derivations are neither reactor MHD theorems nor a prerequisite for the first P1–P3 or N1 deliverables.

## 6. First work and activation rules

1. **Record one concrete decision.** Candidate, time horizon, total field, domain, observable, threshold and uncertainty evidence.
2. **Continue a deterministic pilot.** D1 for a selected stability estimate or D2 for a selected thermal estimate; ordinary G1/G2 work remains the core.
3. **Build N1/N3 around one consequential omission.** Derive and bound its defect in the norm the stability theorem actually uses, then produce a decision-level allowance.
4. **Start P1/P3 together.** A finite-time deterministic-orbit loss problem with a specified launch distribution is a suitable first target when loss is relevant. Certify numerical bias as well as sampling error.
5. **Use P2 where input distributions are supported.** Otherwise retain deterministic robust bounds. Measure whether a stochastic optimizer adds value before committing to it.
6. **Activate N2/P4 only if the decision warrants it.** Select one needed correction; success may mean keeping the original model with an adequate allowance.

These are dependencies and priorities, not a claim that every item belongs in the next development cycle. Concrete gates are in [implementation-milestones.md](implementation-milestones.md).

## 7. Global well-posedness and the role of foundations

Global well-posedness would settle existence, uniqueness and the relevant continuous-dependence question for a specified equation and data class. It would not establish the adequacy of that equation for the selected plasma, useful numerical constants, good confinement, a sufficient temperature history or a small probability of violating an operating requirement. The new goals retain their purpose even after such a theorem.

A full microscopic derivation can be a major foundational achievement. Its techniques can also yield useful isolated estimates. For PlasmaLean, however, the next useful result should be stated in the form **“this omitted effect changes this observable by at most this amount over this interval”**, or **“this new estimate makes this existing certificate useful.”** That is the criterion for taking a foundational technique into the active programme.

## References

- **R1.** Law, Cerfon, Peherstorfer and Wechsung, *Meta variance reduction for Monte Carlo estimation of energetic particle confinement during stellarator optimization*: [paper](https://arxiv.org/abs/2301.07280).
- **R2.** Wechsung et al., *Stochastic and a posteriori optimization to mitigate coil manufacturing errors in stellarator design*: [paper](https://arxiv.org/abs/2203.10164).
- **R3.** Terry et al., *Validation in Fusion Research: Towards Guidelines and Best Practices*: [paper](https://arxiv.org/abs/0801.2787).
- **R4.** Villani, *Hypocoercivity*: [monograph](https://arxiv.org/abs/math/0609050).
- **R5.** Deng, Hani and Ma, *Long time derivation of the Boltzmann equation from hard sphere dynamics*: [paper](https://arxiv.org/abs/2408.07818).
- **R6.** Deng, Hani and Ma, *Hilbert's Sixth Problem: derivation of fluid equations via Boltzmann's kinetic theory*: [paper](https://arxiv.org/abs/2503.01800).
