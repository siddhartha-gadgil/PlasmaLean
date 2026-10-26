# PlasmaLean: implementation milestones for the additional goals

**Proposed work — 24 October 2026.** This note specifies reviewable outputs for the companion [overview](plasmalean-goals-overview.md), [probabilistic goals](probabilistic-goals-and-techniques.md) and [deterministic additions](deterministic-goals-and-techniques.md). It reports no completed Lean code, new solver benchmarks or established reactor predictions.

The existing G1/G2 programme remains the core. P1–P4 are local labels for the new probabilistic work, not the older formalization roadmap's P0–P9 gates. N1/N2 are deterministic modelling additions; N3 is shared decision infrastructure. References to D/K below mean work packages of a plan version that was not supplied; they do not exist in the current [implementation plan](../implementation-plan.md), whose nearest equivalents are the gates E0–E8 (§11.2), N1–N3 (§12) and the phases of §10.

## 1. First selection

The next extension should combine **one useful deterministic estimate** with **one concrete observable**. A reasonable first pair is:

- A D1 modified-energy estimate or D2 driven thermal estimate for a model already selected by G1/G2.
- An N1/N3 bound on one consequential omitted effect, or a P1/P3 finite-time orbit-loss estimate if a suitable orbit model is already available.

Choose the pair from the current bottleneck. Do not make a constant-field kinetic sandbox, a particle limit, a stochastic MHD model or a full kinetic reactor simulation prerequisites. A sandbox is appropriate only if it develops a named lemma/checker needed by the chosen application.

The ordinary cycle's thermal commitment remains. A probability extension is not a reason to postpone the existing thermal work indefinitely.

## 2. A shared scenario record

Create a small human-readable scenario record before introducing new formal interfaces. Suggested contents are:

| Field | Required information |
| --- | --- |
| Candidate | Geometry, operating point and the identity/version of supplied data. |
| Model | Actual equations, species, coefficients, prescribed/self-consistent fields, initial and boundary conditions. |
| Total field | Distinguish external and plasma contributions, with consistent units and normalization. |
| Interval | Operating horizon, launch times, and any stopping/exit rule. |
| Observable | Exact functional, units, spatial localization and time dependence; distinguish a wall proxy from a wall impact. |
| Decision | Threshold, permitted loss/risk where relevant, and the remaining margin. |
| Uncertainty | Numerical, input and model components; dependencies and possible double counting. |
| Evidence | Proved, verified numerically, empirically supported, assumed or unresolved. |
| Probability | Which law is being used: launch, uncertain parameters, physical process or algorithmic sampling. |
| Confidence | A separate numerical/statistical confidence level and its sampling/selection protocol. |
| Missing effect | The selected possible omission and why it could change the conclusion. |

An undefined probability law or an unknown model discrepancy is recorded as unresolved, not filled with a convenient distribution or zero. This record is N3/K0 work. Its importance is preventing incompatible claims from being composed; the scientific work remains producing the estimates.

## 3. Work items and completion gates

| Item | First output | Completion evidence | Expansion rule |
| --- | --- | --- | --- |
| **W0 — Scenario and applicability** | One completed record from §2. | A named decision and uncertainty that a proposed calculation can resolve. | Stop broad literature work once an actionable lemma or comparison has been selected. |
| **W1 — D1 or D2 method pilot** | A modified-energy or driven-entropy estimate for the selected deterministic model. | Improvement over its baseline in certified horizon, perturbation size, error width or checking cost. | Toy fixtures alone do not activate a larger programme. |
| **W2 — N1 defect-to-output bridge** | A derived defect equation, a produced defect bound and a finite-time observable allowance. | Correct domains, derivatives, constraints, initial/boundary terms and observable continuity. | Use the weakest sufficient model comparison; no preceding microscopic limit is required. |
| **W3 — P1/P3 orbit-population pilot** | A finite-time loss interval under a specified launch law, with numerical and sampling errors separated. | A nontrivial interval on an actual selected orbit problem; preserved G1 claims. | Add deposition only with a supplied energy-transfer law. |
| **W4 — P3 algorithm comparison** | One variance-reduction estimator and a matched comparator. | Same quantity, model, bias budget, accuracy/confidence and end-to-end cost. | Continue only if the decision or cost improves. |
| **W5 — P2 robustness/uncertainty** | Propagate a small uncertainty set; use a law only when justified. | A robust bound or a well-defined chance constraint with input-law uncertainty distinguished from sampling error. | Stochastic optimization requires its own demonstrated benefit. |
| **W6 — N2/P4 targeted correction** | One corrected closure, kinetic component or stochastic process. | Evidence of improved adequacy for the selected observable and regime, including remaining uncertainty. | Activate only after a named inadequacy or unresolved consequential uncertainty. |

W1, W2 and W3 can proceed independently when their input models exist. W4 depends on a fixed quantity and comparator, not on W6. W6 is not the inevitable final stage.

## 4. Contract A: a deterministic defect and residual certificate

The selected baseline equation is

$$
U_t=F(U).
$$

For a chosen richer description, derive a reconstruction into the same admissible state space with

$$
V_t=F(V)+d.
$$

Let the numerical reconstruction satisfy

$$
(U_a)_t=F(U_a)+r_{\rm num}.
$$

Then the exact error equation is

$$
e_t=F(V)-F(U_a)+d-r_{\rm num},\qquad e=V-U_a.
$$

An implementation target is a comparison theorem that, under produced stability estimates, gives

$$
D^+\|e\|\le a(t)\|e\|+c(t)\|e\|^2
  +\delta_{\rm model}(t)+\epsilon_{\rm num}(t),
$$

and bounds this by a nonnegative scalar supersolution \(R\) satisfying

$$
R'\ge a(t)R+c(t)R^2+\delta_{\rm model}(t)+\epsilon_{\rm num}(t),
\qquad R(0)\ge\|V(0)-U_a(0)\|.
$$

Use the appropriate scalar comparison theorem with its regularity hypotheses. Allow a growth coefficient \(a(t)\); do not require strict decay when the model does not supply it. The norm, regularity, solution existence and continuation region must be explicit.

Possible interfaces are `ProjectedModelDefect`, `EvolutionResidualBound`, `ErrorRadiusBound` and `ObservableErrorBound`. These names are proposals. Before implementing them, check the current repository interfaces to avoid duplicate abstractions.

### Required producers

1. The equation supplies the exact projected defect, including constraint and boundary-lifting errors.
2. Analysis or a validated computation supplies a bound in the forcing norm required by the evolution estimate.
3. The stability theorem supplies \(a,c\) on the region actually reached by the comparison radius.
4. The observable theorem translates the state error into the needed output error.
5. A numerical checker verifies the finite data with a proved soundness theorem.

If a constitutive stress enters through its divergence, its amplitude bound alone is insufficient. If an output is pointwise or lies on a boundary, an integrated state norm alone is insufficient. If a comparison envelope is empirical, the theorem remains conditional on that envelope and the evidence record must say so.

### Meaningful fixtures

- **Positive:** the selected finite-dimensional or PDE case produces a useful output bound using a nonzero, explicitly bounded defect.
- **Negative:** a small-amplitude rapidly varying stress cannot be substituted for a small stress-divergence bound.
- **Negative:** an incompatible kinetic moment projection is rejected as an incompressible MHD state unless the missing projection/constraint terms are accounted for.
- **Decision fixture:** widening a model allowance can change a certificate from established to inconclusive without declaring the physical model false.

The positive fixture should connect to the destination model before the interface is counted as a completed modelling contribution.

## 5. Contract B: a useful deterministic energy or entropy method

### D1 modified energy

Seek a positive quadratic form \(E(e)=\langle e,Pe\rangle\) equivalent to the stated norm. Produce a dissipative or controlled-growth form inequality on the actual operator domain. Include \(\dot P\) for a moving form, boundary terms, invariant subspaces and an infinite-mode/tail argument when a matrix calculation is only a discretization.

A small initial sanity case is

$$
x'=y,\qquad y'=-x-y,\qquad
E=\tfrac12(x^2+y^2+xy),\qquad E'=-E.
$$

The corresponding negative case is an undamped stationary mode in the intended MHD linearization. No positive equivalent norm can prove strict decay of that mode. This test prevents a certificate from hiding an unjustified spectral gap.

**Acceptance:** show how the estimate improves one existing deterministic certificate. A semidefinite feasibility calculation without a PDE bridge is a finite-dimensional result only. Villani's framework is a source of methods, not a replacement for these obligations [R1].

### D2 driven relative entropy

Derive the relative-entropy balance against the selected hot profile using the actual source, loss, transport and boundary terms. Use a nonnegative integration weight and a convex entropy on the admissible state region; prove whatever coercivity is needed. Include the residual of a time-dependent or approximate reference.

**Acceptance:** a correctly signed estimate in a declared norm and an explicit contribution to a thermal bound. Retain pointwise temperature comparison or supply a separate argument that obtains it. A mean or integrated entropy estimate is not automatically a burn-temperature certificate.

These are mathematical producer tasks. No equilibrium relaxation theorem should be imported into an open heated system with its source and wall terms omitted.

## 6. Contract C: certified probability under deterministic orbits

Let \(Z\sim\rho_0\) be the declared launch state and let

$$
Y(Z)=\mathbf1_{\{\tau(Z)\le T\}},\qquad p=\mathbb E_{\rho_0}Y.
$$

The dynamics and \(\tau\) can be fully deterministic. One first result can integrate a certified cell partition against \(\rho_0\), avoiding random sampling altogether.

For a Monte Carlo version, use independent launches \(Z_1,\ldots,Z_n\) at a fixed sample size and target confidence. Fix the candidate/dynamics, launch law, loss set and horizon independently of the certification sample; otherwise use a selection-aware or simultaneous guarantee. Suppose trajectory validation supplies

$$
0\le\ell_i\le Y(Z_i)\le u_i\le1.
$$

An unresolved trajectory may use \(\ell_i=0,u_i=1\). For \(0<\delta<1\), define

$$
\varepsilon_n=\sqrt{\frac{\log(2/\delta)}{2n}}.
$$

The independent bounded-observation concentration theorem and the pointwise enclosures yield, with probability at least \(1-\delta\),

$$
\max\left(0,\frac1n\sum_i\ell_i-\varepsilon_n\right)
\le p\le
\min\left(1,\frac1n\sum_i u_i+\varepsilon_n\right).
$$

This is an elementary proposed composition lemma, not a newly established theorem of the repository. The sample size must be positive; the sampling law and independence require their own mathematical specification. A pseudorandom implementation also needs an explicit relationship to that specification. The trajectory enclosures must be sound, not confidence intervals silently treated as deterministic bounds.

The construction exposes a useful practical choice: if the interval is wide because many trajectories are unresolved, improve orbit validation; if the sampling term dominates, use more samples or better estimation. It does not conceal one error inside the other.

### Fixtures and completion

- A deterministically confined launch cell has exact loss contribution zero; a proved crossing cell has exact contribution equal to its launch mass.
- An unresolved cell or trajectory contributes conservatively to the upper bound.
- Zero observed losses do not imply zero true loss probability.
- A collisionless model produces a collisionless population statement. A deposition claim is rejected until an energy-transfer law is present.
- Loss at a chosen flux surface is labelled a proxy unless the relation to the wall is established.

**Completion:** one nontrivial finite-time probability interval for the chosen candidate/model, accompanied by its launch distribution and all error components. It supplements existing all-orbit confinement results.

## 7. Contract D: variance reduction without changing the target

Choose one method first: a control variate or multifidelity correction is a reasonable initial candidate. For an integrable output \(Y\), a cheap control \(Z\) with known expectation \(m_Z\), and a fixed coefficient \(a\),

$$
\mathbb E[Y-a(Z-m_Z)]=\mathbb E Y.
$$

Use an independent training/pilot sample to choose \(a\) in the first implementation. If \(m_Z\) is estimated, include its error and dependence. Confidence bounds must apply to the corrected observation's actual range/tails, which need not be \([0,1]\).

Record the costs of the expensive solver, cheap solver, training, validation, bias control and checker. Compare against both plain Monte Carlo and a deterministic alternative when the latter is viable. A fair gain is either less total work for the same valid bound or a tighter valid bound at the same total work. A lower empirical sample variance alone is not a certified speedup.

Law et al. provide a relevant stellarator example of combined variance-reduction methods [R2]. Their numerical gain motivates a benchmark; it does not determine the gain for PlasmaLean.

If interacting particles or adaptive branching are introduced, reassess dependence before applying an independent-sample theorem. A pair-covariance estimate controls a variance term but does not automatically establish an exponential confidence bound. Consult Deng-style correlation machinery only if such a selected interacting approximation actually needs an applicable estimate.

## 8. Contract E: a conservative decision statement

For a scalar upper-limit decision, a possible interface is

$$
Q_{\rm computed}+\Delta_{\rm num}+\Delta_{\rm input}
  +\Delta_{\rm model}\le Q_{\max}.
$$

Every allowance must refer to the same observable, scenario and horizon. Its definition must make the sum valid without double counting. A lower-bound requirement has the corresponding subtraction. For distributional or pathwise requirements, state a different contract rather than applying scalar mean arithmetic silently.

If several constituent error bounds hold on events of probability at least \(1-\delta_j\), their intersection has probability at least \(1-\sum_j\delta_j\) by the union bound; independence is not needed for this conservative rule. This is meaningful only if the events and probability space are specified. In particular, numerical confidence cannot be added to physical loss risk as though the two were the same event.

Record one of four outcomes:

1. **Established under stated mathematical assumptions:** the bounds are produced and the margin closes.
2. **Conditional on supplied evidence:** the implication is proved but an input envelope or law has empirical/assumed status.
3. **Inconclusive:** the estimate, evidence or margin is insufficient.
4. **Evidence of inadequacy:** a controlled discrepancy is consequential for the selected decision.

A failed sufficient condition or an overly large upper bound belongs in outcome 3, not automatically outcome 4. This separation is consistent with fusion verification/validation practice [R3].

## 9. What to postpone, and what reactivates it

| Deferred direction | Reactivation condition |
| --- | --- |
| Physical stochastic forcing or a stochastic MHD closure | A named mechanism, defensible law and evidence that it changes the target observable; simpler deterministic corrections insufficient. |
| General interacting-particle/chaos theory | An actual solver or model needs dependence/finite-particle control that available simpler estimates do not provide. |
| Full kinetic implementation | A selected output needs kinetic information not captured adequately by the smaller model. |
| A hypocoercive toy-model library | A specific destination proof/checker needs the missing lemma; transfer is assessed before expansion. |
| A full microscopic particle-to-MHD derivation | A separately scoped foundational project. It is not the presumed last stage of these milestones. |

No reactivation follows solely from a famous theorem, a failed proof attempt or the general fact that microscopic physics is richer. The trigger is a useful result the project can name and assess.

## References

- **R1.** Villani, [Hypocoercivity](https://arxiv.org/abs/math/0609050).
- **R2.** Law, Cerfon, Peherstorfer and Wechsung, [Meta variance reduction for Monte Carlo estimation of energetic particle confinement during stellarator optimization](https://arxiv.org/abs/2301.07280).
- **R3.** Terry et al., [Validation in Fusion Research: Towards Guidelines and Best Practices](https://arxiv.org/abs/0801.2787).

The two technical companion notes give additional primary references and narrower theorem scopes. The contracts and priorities in this note are proposed PlasmaLean applications, with proof obligations stated explicitly.
