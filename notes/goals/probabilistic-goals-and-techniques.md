# PlasmaLean: probabilistic goals and techniques

**Status: proposed research and implementation targets, 24 October 2026.** This note
expands the practical scope decision in section 12 of the implementation plan. No
new result or Lean implementation is claimed here. The existing deterministic
confinement and thermal goals continue independently.
The labels P1–P4 below identify this note's probabilistic goals, not the
pre-existing formalization roadmap's gates P0–P9.

## 1. The decision

Add a small probabilistic programme aimed at useful observables and trustworthy
computations. Its immediate purpose is to quantify populations, uncertainty and
computational error. Introducing random physical forcing is an optional modelling
choice requiring a separate adequacy argument.

| Goal | Practical importance | Present decision |
| --- | --- | --- |
| **P1 — Finite-time loss, deposition and path observables.** Bound lost-particle fractions, deposited energy and energy delivered to specified wall patches for a stated initial or birth distribution. | High when energetic-particle retention or deposition limits a candidate. A selected population average can be more relevant than proving confinement of every conceivable initial orbit. | First physical-statistical pilot, once a suitable deterministic orbit model and observable are fixed. |
| **P2 — Uncertain inputs and decision confidence.** Determine whether a design conclusion survives uncertainty in profiles, transport coefficients, coils, heating and other declared inputs. | High when input uncertainty can consume the stability, burn or wall-load margin. Probability is useful only if its input law is defensible. | Begin with explicit uncertainty records; use deterministic sets when a probability law is unsupported. |
| **P3 — Certified randomized computation.** Estimate P1/P2 quantities or deterministic integrals more cheaply while retaining stated error/confidence guarantees. | Potentially high for expensive integration and repeated design comparisons; no universal speed advantage. | Benchmark one variance-reduction method against a matched baseline. |
| **P4 — Adequate stochastic reduced models.** Introduce and assess a specific stochastic collision, transport or fluctuation model when it resolves an identified missing effect. | Conditional. It can be important for a selected effect, but is not a prerequisite for all confinement or thermal analysis. | Activate only after a decision-specific adequacy test. |

Finite-particle fluctuation limits, propagation of chaos for new interacting particle
systems, and a stochastic field around MHD are **not default work packages**.
A complete microscopic derivation of MHD remains outside the active and presumed
future programme. A particular estimate can be commissioned when one of P1–P4
actually needs it.

These priorities are planning judgments, not claims that every stellarator has the
same limiting uncertainty. The pilot must name the candidate and its unresolved margin.
P1 adds a finite-time population criterion; it does not replace or weaken an existing
all-orbit G1 theorem or silently change a design requirement that calls for one.

## 2. Four different meanings of probability

| Meaning | Mathematical object | What it does not establish |
| --- | --- | --- |
| A distribution of initial states or births | A probability measure transported by deterministic trajectories | That the underlying trajectory equation contains random forces |
| Uncertainty about model inputs | A stated law on parameters, profiles or initial data | That an arbitrary prior or fitted distribution is physically correct |
| A stochastic physical/reduced model | A process law, with a generator or other specified dynamics | That this law accurately represents the omitted plasma physics |
| A randomized numerical algorithm | Random samples used to approximate a fixed mathematical quantity | That the physical model has changed |

The Boltzmann, Landau and Fokker–Planck equations evolve densities deterministically
when their data and coefficients are fixed. A stochastic representation can be a
different way to calculate the same quantity. A probability density is not evidence
that an additional stochastic physical term has been introduced.

Keep two probability levels separate. A physical/model event may satisfy

$$
p_{\rm loss}=\mathbb P_{\rho_0}(\tau_{\rm loss}\le T)\le p_*.
$$

A randomized computation may instead guarantee

$$
\mathbb P_{\rm algorithm}\{p_{\rm loss}\le\widehat p_{\rm upper}\}
\ge 1-\delta.
$$

Here \(p_*\) is an allowed event probability and \(\delta\) is a failure probability
for the numerical confidence statement. Neither is the probability that the chosen
physical model is correct. Formal verification, sensitivity analysis and comparison
with experiments have distinct roles [R1].

## 3. P1: finite-time loss and deposition

### 3.1 Specify the output before choosing a process

Let \(X_t\) be the selected phase-space trajectory, deterministic or stochastic,
with normalized initial law \(\rho_0\). Define the loss time \(\tau\) using an
explicit wall or other loss set. Useful quantities include

$$
p_{\rm loss}(T)=\mathbb P_{\rho_0}(\tau\le T),
\qquad
E_{\rm dep}(T)=
\mathbb E_{\rho_0}\!\left[\int_0^{T\wedge\tau}P_{\rm dep}(t,X_t)\,dt\right],
$$

and, for a wall patch \(A\),

$$
E_A(T)=
\mathbb E_{\rho_0}
\left[E_{\rm exit}\,\mathbf 1_{\{\tau\le T,\ \operatorname{position}(X_\tau)\in A\}}\right].
$$

The energy law defining \(P_{\rm dep}\) and \(E_{\rm exit}\) must be supplied and
checked. A birth-rate integral converts a per-particle quantity into a total source
or load; it is not an automatic change of units. Include species, launch energy,
birth position, pitch, fields, collisions, time horizon and wall geometry.
Crossing a selected flux surface may be a useful loss proxy, but it is not
automatically a vessel-wall impact. A uniform test-launch distribution is not
automatically the profile- and reactivity-dependent fusion birth distribution.

Total lost energy does not bound the peak wall heat flux. Patch size, arrival times,
surface measure and any trace/density estimate needed for a local flux must appear
in that separate claim. Likewise, a small expected loss fraction does not give the
joint probability of a collective loss event without information about dependence.
Expected deposited energy can feed a mean thermal-source model; by itself it does
not certify the probability of staying above a burn temperature throughout an
interval. That further goal needs the thermal dynamics and the appropriate
time-dependent or pathwise source bound.

The first pilot should use deterministic orbit dynamics with a stated initial
distribution. That isolates the new statistical output from additional collision or
fluctuation assumptions. Add a richer trajectory model only if an adequacy check
identifies a consequential omission.
If the pilot is collisionless, label the result accordingly: it does not include
slowing-down, collisions or wave-induced loss merely because its launch measure is
probabilistic.

### 3.2 First technique: deterministic orbit enclosures plus integration

For every initial point in a covered cell, an existing orbit certificate can classify
the cell as retained, lost or unresolved over the interval. Integrating certified
lower and upper loss indicators against the stated initial density gives a loss
probability interval. The unresolved mass contributes to the interval width.
Any uncovered part of the initial support must also be counted as unresolved.

This is a direct connection to the old deterministic goal: all-orbit certificates
become components of population certificates. It requires neither a stochastic
differential equation nor independent physical particles. Validated quadrature can
be preferable to Monte Carlo for a small, smooth parameter space.

**Completion evidence:** one actual orbit family, an explicit normalized measure,
certified cell classifications and a nontrivial probability interval. A theorem
which assumes the desired classification everywhere is only an interface.

### 3.3 Second technique: stopped-process barriers

For an Itô diffusion

$$
dX_t=b(t,X_t)\,dt+\sigma(t,X_t)\,dW_t,
\qquad
\mathcal L_t V=b\cdot\nabla V+
\tfrac12(\sigma\sigma^\top):\nabla^2 V,
$$

a useful finite-horizon proof target is a nonnegative \(V\in C^{1,2}\) satisfying

$$
V(t,x)\ge1 \ \text{on the loss boundary},\qquad
(\partial_t+\mathcal L_t)V(t,x)\le r(t)
$$

before loss, where \(r\ge0\) is integrable. With a well-defined nonexplosive process,
the appropriate stopped Itô/Dynkin formula and justified expectation/localization
steps, and \(\rho_0\) supported in the initial safe domain, one obtains

$$
\mathbb P_{\rho_0}(\tau\le T)
\le
\int V(0,x)\,\rho_0(dx)+\int_0^T r(t)\,dt.
$$

The right side may be capped at one. A bound above one is valid but uninformative.
If there is initially lost mass, include it separately or extend the barrier
statement to cover loss at time zero.
For jumps, reflection, killing or nonstandard walls, the generator, exit condition
and formula must match that process. For deterministic trajectories, set
\(\sigma=0\) and prove the corresponding trajectory inequality directly.

Barrier certificates for stochastic reachability are an established methodology
[R2]. The PlasmaLean contribution would be a sound producer/checker for the chosen
plasma model: propose \(V\) numerically, check positivity and generator inequalities
with certified arithmetic, and connect those checks to the stopped-process theorem.
Checking sampled points alone does not certify an inequality on the whole domain.

**First milestone:** a bounded, explicitly specified model with positive and negative
fixtures. Then transfer to one actual orbit-loss question. Do not start with an
unbounded, singular, self-consistent reactor process.

### 3.4 Path events need a path theorem

One-time distributions generally do not determine first-passage probabilities.
For example, Brownian motion \(W_t\) and \(Y_t=\sqrt t\,Z\), \(Z\sim N(0,1)\),
have the same marginal law at each time. For \(a>0\),

$$
\mathbb P\!\left(\sup_{t\le T}W_t\ge a\right)
=2\mathbb P(Z\ge a/\sqrt T),\qquad
\mathbb P\!\left(\sup_{t\le T}Y_t\ge a\right)
=\mathbb P(Z\ge a/\sqrt T).
$$

Thus a theorem about a density at time \(T\) cannot silently become a wall-hitting
theorem. Use an appropriate coupling, stopped-process argument, killed equation or
path-space discrepancy estimate.
A small state-norm or Wasserstein error also does not directly bound a discontinuous
exit indicator. One possible bridge combines a path coupling with a buffered loss
set and a bound on the probability of paths near the boundary; a suitable
path-law total-variation bound is another.

## 4. P2: uncertain inputs and design decisions

Let \(\theta\) represent declared uncertain inputs and \(Q(\theta)\) the selected
output. Two different useful targets are

$$
Q(\theta)\le Q_{\max}\quad\text{for every }\theta\in\Theta
$$

and

$$
\mathbb P_{\theta\sim\mu}\{Q(\theta)>Q_{\max}\}\le\alpha.
$$

The first is a deterministic robustness statement; the second is a chance
constraint under the specified law \(\mu\). A chance constraint should not replace
a justified robust bound merely because a convenient distribution is available.

For every input, record whether uncertainty is a measured distribution, a modelling
judgment, an interval bound or unresolved. Preserve dependence: shared calibration
errors and profile correlations cannot automatically be sampled independently.
If a law is estimated from finite data, its estimation uncertainty is separate
from the sampling error of the subsequent numerical calculation.

Useful techniques are sensitivity bounds, interval propagation, adjoint estimates
for a selected output, and concentration or distributional bounds where their
hypotheses are justified. Sensitivity helps choose which input merits better data
or a finer model; it does not by itself establish the input law.

**First milestone:** take one thermal or confinement certificate and propagate a
small declared uncertainty set through it. Then add a probability law only if that
law makes a relevant, defensible decision possible. A result may legitimately be
“the margin is robust on this set” with no probabilistic refinement.

When a candidate is selected after inspecting many random estimates, its final
confidence statement must account for that selection. A fixed prespecified final
test, simultaneous bounds over the compared candidates, or an appropriate sequential
method can address this. A confidence interval for one prespecified candidate
cannot automatically certify the winner of an unrestricted adaptive search.

## 5. P3: algorithms that may be easier

### 5.1 What the computational objective is

Choose one fixed model, observable, error tolerance and confidence level. Compare
total cost, including training, evaluation, bias control and formal checking.
Randomization is useful when estimating a small set of expectations avoids resolving
an entire high-dimensional density. It can be ineffective when the event is rare,
the estimator variance is high, or the desired answer is a uniform trajectory
guarantee rather than an average.

Law, Cerfon, Peherstorfer and Wechsung combine control variates, importance sampling
and information reuse for energetic-particle confinement during stellarator
optimization. Their examples report approximately two orders of magnitude of
speedup over ordinary Monte Carlo [R3]. This is a relevant practical precedent,
not a universal complexity result or a certificate for a PlasmaLean candidate.

### 5.2 Prioritized methods

| Method | Intended gain | Obligation before claiming a gain |
| --- | --- | --- |
| Control variates or multifidelity correction | Use a cheap correlated model to reduce expensive-sample variance. | Preserve the exact correction identity; know or separately estimate the control mean; include training and low-fidelity costs. |
| Importance sampling | Sample loss-relevant regions more often. | The proposal must cover the target contribution, weights must be correct, and their variance/tails must be controlled. |
| Stratification and validated partitioning | Concentrate work near unresolved orbit or input cells. | Account for every cell and its probability mass; retain conservative treatment of unresolved cells. |
| Multilevel estimators | Combine cheap and expensive discretizations. | Prove or bound discretization bias and variance/cost of coupled level differences. |
| Backward equations and adjoints | Target a particular expectation or exit probability directly. | Match terminal and boundary conditions and certify the equation/residual; a backward solve can also be expensive. |
| Rare-event splitting | Spend samples near pathways leading to a rare event. | Account for branching dependence and estimator normalization; do not use an independent-Bernoulli bound on dependent descendants. |

For a control variate \(Z\) with known mean \(m_Z\), the identity

$$
\mathbb E Y=\mathbb E[Y-a(Z-m_Z)]
$$

holds whenever the quantities are integrable. For square-integrable variables and
\(\operatorname{Var}Z>0\), the variance-minimizing fixed coefficient is
\(a=\operatorname{Cov}(Y,Z)/\operatorname{Var}Z\). Estimating or adapting that
coefficient from the same observations needs its own analysis; an independent
pilot/final-sample split is a simple first implementation.

For normalized target and proposal densities \(p,q\), importance sampling uses
\(\mathbb E_p g=\mathbb E_q[g\,p/q]\), provided \(q>0\) wherever \(g p\ne0\)
and the integral exists. Unbiasedness alone supplies no finite useful variance.
A self-normalized estimator has a different bias analysis.

### 5.3 Certification has several error terms

For independent samples \(Y_i\in[0,1]\) of the exact selected observable, a
fixed-sample bounded-variable concentration target is

$$
\mathbb P\!\left(
|\widehat Q_N-\mathbb E Y|
>\sqrt{\frac{\log(2/\delta)}{2N}}
\right)\le\delta.
$$

The sampling theorem needs a proof or a verified library theorem. In a simulation,
the observations usually approximate \(Y_i\). Add an independently justified
discretization/trajectory error and any model discrepancy. A narrow Monte Carlo
interval cannot remove systematic numerical or physical-model bias.
An importance-weighted or control-variate observation is not automatically in
\([0,1]\); use its actual proved range or a suitable tail/variance theorem.

For zero observed losses among \(N\) independent exact Bernoulli trials, the
one-sided upper endpoint is \(1-\delta^{1/N}\) at confidence \(1-\delta\), from
\(\mathbb P_p(\text{zero losses})=(1-p)^N\). It is not zero. Repeatedly inspecting
the data and stopping at a favorable fixed-sample interval requires a different
sequential guarantee.

For fixed \(N\ge2\) exchangeable square-integrable variables,

$$
\operatorname{Var}\!\left(\frac1N\sum_{i=1}^N Y_i\right)
=\frac{\operatorname{Var}Y_1}{N}
+\frac{N-1}{N}\operatorname{Cov}(Y_1,Y_2).
$$

This algebra explains when correlation estimates matter. Independent sample
trajectories with prescribed fields do not require a microscopic propagation-of-chaos
theorem. An interacting particle solver can have dependence, particle-number bias
and discretization bias; its markers are not automatically independent physical
particles. A pair-covariance estimate helps control variance but does not alone
give every desired exponential tail bound.

**First milestone:** one unbiased control-variate estimator for the same P1
quantity as an ordinary Monte Carlo baseline, with fixed-sample confidence,
trajectory-bias allowance and total-cost comparison. Advance only if the result
improves the actual decision or the cost of resolving it.

## 6. P4: selected stochastic models and their adequacy

The activation question is concrete: “Does this omitted collision or fluctuation
mechanism change this loss, deposition or transport conclusion over this interval?”
Choose the smallest model that can answer it. The choice might be a deterministic
kinetic PDE, a stochastic representation of that PDE, a deterministic fluid closure,
or a stochastic reduced process.

A completed P4 record includes the mechanism and regime; the coefficients and their
provenance; conservation, positivity and boundary checks; comparison with an adequate
reference or observations; the relevant error or uncertainty allowance; and its
effect on the design margin. An empirical envelope supports a mathematical statement
conditional on that envelope. It is not a derivation from first principles.

For a smooth linear observable, density or weak-error bounds may suffice. Wall
hitting needs stronger path/boundary information; peak loads need localization;
nonlinear reaction rates need suitable moments or norms. Matching a few moments,
an equilibrium or a mean damping rate need not settle any of these outputs.

**Stop rule:** retain the existing model when the adequacy evidence and propagated
margin support it. A failed sufficient theorem or a large upper bound is
inconclusive, not proof that random physics is needed. Do not add a stochastic
term solely to regularize an otherwise difficult equation and then claim that
the regularized system proves the original model's behavior.

## 7. What Deng and Villani contribute

| Source or technique family | Use for P1–P4 | Priority |
| --- | --- | --- |
| Villani-style modified energies, entropy and hypocoercivity | Stability/relaxation bounds for a chosen density equation; residual control; possible control-variate structure. The operator, invariant modes and boundary conditions remain essential. | Active method source when a selected estimate needs it. |
| Alexandre–Villani grazing-collision analysis | A source for a specific Boltzmann-to-Landau modelling question, including Coulomb-type singularities. The cited finite-time framework does not supply a general quantitative reactor error bound. | Conditional reference. |
| Mouhot–Villani phase mixing | A source for selected deterministic kinetic response or mixing estimates. Landau damping is not the Landau collision operator. | Conditional; not a general stochastic-model recipe. |
| Deng–Hani–Ma cumulants and collision histories | Potential ideas for a needed correlation or long-time approximation estimate. Their hard-sphere derivation is not a ready-made Coulomb-plasma solver. | Reference-only unless a specific interacting-system estimate is missing. |
| Landau particle-system limits | Closer reference when validating a particular interacting stochastic collision solver. Feng–Wang treat a spatially homogeneous conservative particle system, including Coulomb interactions. | Conditional; retain the homogeneous/model restrictions. |

Villani's hypocoercivity programme studies quantitative convergence for suitable
degenerate dissipative equations using Lyapunov functionals [R4]. Its techniques
also serve deterministic goals; no physical randomness is required. The
Alexandre–Villani result [R5], Mouhot–Villani damping theorem [R6], Deng–Hani–Ma
derivation [R7] and Feng–Wang particle limit [R8] address different equations,
limits and assumptions. None is a universal theorem covering driven stellarator
geometry, realistic walls and self-consistent Coulomb electromagnetic dynamics.

The criterion for adopting a difficult technique is a useful bound, justified
comparison or measured computational improvement for the selected task. Completing
a foundational derivation is not the success criterion.

## 8. First deliverables and completion gates

1. **Setup record:** candidate, model, observable, time, measure/uncertainty set,
   threshold, numerical tolerance and confidence level. Keep physical assumptions
   separate from theorems and measured evidence.
2. **P1 population certificate:** reuse deterministic orbit information on one
   explicit launch distribution, including unresolved mass.
3. **P2 margin assessment:** propagate one consequential input uncertainty through
   an existing confinement or thermal certificate.
4. **P3 matched estimator pilot:** control variates or stratification, with the
   baseline and error/confidence accounting fixed before comparison.
5. **P4 only if activated:** one identified missing effect, a suitable comparison
   and a decision to retain, refine, change the candidate or remain unresolved.

For each item require a nontrivial producer, an independent review, a positive
fixture and a failure case exposing a relevant missing hypothesis. A generic
probability inequality is useful infrastructure, but completion also requires
connecting it to the selected PlasmaLean observable.

## References

- **[R1]** P. W. Terry et al., [Validation in Fusion Research: Towards Guidelines
  and Best Practices](https://arxiv.org/abs/0801.2787), Physics of Plasmas 15 (2008),
  062503.
- **[R2]** S. Prajna, A. Jadbabaie and G. J. Pappas, [A Framework for Worst-Case
  and Stochastic Safety Verification Using Barrier
  Certificates](https://authors.library.caltech.edu/records/z9p8b-wd557), IEEE
  Transactions on Automatic Control 52 (2007), 1415–1428.
- **[R3]** F. Law, A. Cerfon, B. Peherstorfer and F. Wechsung, [Meta variance
  reduction for Monte Carlo estimation of energetic particle confinement during
  stellarator optimization](https://arxiv.org/abs/2301.07280).
- **[R4]** C. Villani, [Hypocoercivity](https://arxiv.org/abs/math/0609050),
  Memoirs of the AMS 202 (2009), no. 950.
- **[R5]** R. Alexandre and C. Villani, [On the Landau approximation in plasma
  physics](https://www.numdam.org/article/AIHPC_2004__21_1_61_0.pdf), Annales de
  l'Institut Henri Poincaré C 21 (2004), 61–95.
- **[R6]** C. Mouhot and C. Villani, [On Landau
  damping](https://arxiv.org/abs/0904.2760), Acta Mathematica 207 (2011), 29–201.
- **[R7]** Y. Deng, Z. Hani and X. Ma, [Long time derivation of the Boltzmann
  equation from hard sphere dynamics](https://arxiv.org/abs/2408.07818), v3,
  18 July 2025; and [Hilbert's sixth problem: derivation of fluid equations via
  Boltzmann's kinetic theory](https://arxiv.org/html/2503.01800v1). Preserve the
  hard-sphere setting, scaling and regularity hypotheses.
- **[R8]** X. Feng and Z. Wang, [Kac's Program for the Landau
  Equation](https://arxiv.org/abs/2506.14309), v2, 18 August 2025.
