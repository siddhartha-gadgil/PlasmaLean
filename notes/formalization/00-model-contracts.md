# PlasmaLean: model contracts and the meaning of a design proof

Prepared 10 October 2026 from [PlasmaLean](https://github.com/siddhartha-gadgil/PlasmaLean), commit `466920416e97561e4669759ab4077b9a23281ebd`, [domain-libraries.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/466920416e97561e4669759ab4077b9a23281ebd/notes/domain-libraries.md), [Stellerator.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/466920416e97561e4669759ab4077b9a23281ebd/notes/Stellerator.md), and the [website](https://siddhartha-gadgil.github.io/PlasmaLean/index.html). The checked source has starter Lean code and pins Lean/Mathlib `v4.34.1`. These notes propose new mathematics and implementation; they do not report completed formalizations.

## Contents

- [Contracts](#contracts)
- [Architecture](#architecture)
- [Corrections to the starting notes](#corrections-to-the-starting-notes)
- [The model hierarchy](#the-model-hierarchy)
- [Certificate composition](#certificate-composition)
- [First implementation targets](#first-implementation-targets)

## Contracts

The project can prove precise implications from mathematical models and data envelopes. A practical design needs several such implications, plus evidence that the models and supplied envelopes apply to its operating regime. Lean checks the implications; experimental validation supplies evidence about the regime.

Use separate predicates, with explicit parameters:

| Predicate | Required content |
| --- | --- |
| `EquilibriumExists` | Solution space, equations, boundary conditions, constraints, and distance from a numerical candidate |
| `FieldLineBarrier` | Embedded invariant separating surface for the stated magnetic field |
| `ParticleConfinedUntil` | Full-orbit or reduced dynamics, initial set, spatial region, time horizon, and reduction error |
| `LinearMHDStable` | Equilibrium, admissible displacement space, boundary/wall model, controlled norm or observable, and stability definition |
| `NonlinearStable` | Evolution model, solution class, initial neighborhood, norm/modulo symmetries, and interval of existence |
| `TransportBound` | Species, collision/turbulence model, profiles, heat/particle flux, and averaging interval |
| `ComponentFeasible` | Geometry, loads, constitutive data, tolerances, temperatures, degradation, and duty cycle |
| `DesignFeasible` | Explicit conjunction of the required contracts for the same candidate and operating states |

Avoid an unqualified `Stable : Prop` encompassing all these meanings. In particular, linearly stable ideal MHD is compatible with kinetic microinstabilities and poor confinement.

Record each assumption's origin: mathematical theorem; chosen model law; measured datum or empirical fit; machine requirement; or unresolved research hypothesis. Keep arithmetic error, discretization error, parameter/data uncertainty, and model discrepancy separate.

## Architecture

Preserve the existing kernel → sanity checks → verified library architecture. The domain kernel is a set of definitions and law interfaces, distinct from Lean's logical kernel.

Suggested module groups, all initially inside the existing `PlasmaLean` library:

| Group | Purpose |
| --- | --- |
| `Kernel` | Euclidean domains, fields, species, physical constants, boundaries, model predicates, material-law interfaces |
| `Sanity` | Witnesses, limits, units, symmetry, conservation, and counterexamples to overbroad definitions |
| `Theory.Geometry / Equilibrium / Stability / Kinetic` | Derived mathematics |
| `Theory.Engineering` | Thermal, mechanical, electromagnetic, irradiation, and lifetime consequences |
| `Certificates` | Exact data, enclosures, checkers, and proved checker soundness |
| `Bridge` | Import conventions, reductions, certified reconstruction, and composition between models |
| `Design` | Operating specifications and concrete certified candidates |

Do not introduce additional project axioms. Put physical laws in structures/typeclasses and invoke them as hypotheses. Do not manufacture universal instances for empirical material laws. Prove simple consistent instances and existence witnesses to guard against vacuity. Allow the usual logical axioms already used by Lean/Mathlib; “no new domain axioms” is the relevant architectural restriction.

For each theorem record: declaration; source locator; hypotheses; units; boundary and regularity; norm; quantifiers; model; computational errors; empirical inputs; and remaining gaps. No scientific result becomes established merely by appearing in a typeclass field.

## Corrections to the starting notes

The original notes provide valuable directions, but the following refinements are necessary before formalization.

| Starting claim or suggestion | Precise replacement |
| --- | --- |
| Pressure surfaces “must be nested tori” | Force balance implies tangency. A connected, compact, orientable regular level surface carrying a nonvanishing tangent field has Euler characteristic zero, hence genus one. Compactness, absence of boundary, nonvanishing field, and connectedness must be checked. This does not produce a global nested foliation. |
| Global nonsingular Boozer coordinates | Use a flux annulus and circle-valued angles; treat the magnetic axis and any separatrix separately. Existence and regularity of the chart are theorem obligations. |
| `p = 0` is the vacuum limit | Zero pressure implies force-free balance `J × B = 0`. Vacuum additionally requires `J = 0`. A multiply connected vacuum region can carry nontrivial circulation without a single-valued scalar potential. |
| Exact quasisymmetry universally impossible in an asymmetric device | Extract the actual Garren–Boozer compatibility/overdetermination result for its chosen expansion and hypotheses. Counting equations alone is not a general impossibility proof. Distinguish different definitions of quasisymmetry. See [Garren–Boozer and Burby et al.](09-literature.md#geometry-equilibrium-and-symmetry). |
| Mercier positivity certifies plasma stability | State the exact local/asymptotic interchange criterion and sign convention. It does not cover every global, free-boundary, resistive, or kinetic mode. |
| A positive lowest discretized eigenvalue proves continuum stability | For a conforming trial space the minimum Rayleigh quotient is an upper bound on the continuum infimum. Certify omitted modes, cross terms, coefficients, boundary terms, and equilibrium error before claiming a lower bound. |
| `δW > 0` for every nonzero displacement is the automatic goal | Neutral/relabeling modes and continuous spectrum may preclude strict coercivity. Choose the quotient, observable, or nonnegative-energy conclusion supported by the model. |
| KAM ensures absolute persistence of nested surfaces | Appropriate KAM theorems preserve selected sufficiently nonresonant invariant tori under quantitative hypotheses. They do not fill the region with tori or guarantee particle confinement. |
| A radii polynomial needs a “negative root” | Require an admissible positive radius at which the appropriate polynomial is negative, plus contraction, domain, and fixed-point-to-equation conditions. |
| Filament curvature and example clearances ensure construction | Include finite winding packs, ribbon strain, forces, supports, heat, irradiation, ports, and tolerances. Source limits from the chosen material and machine. |
| Stellarators are immune to current-driven disruptions | They do not require a large inductive plasma current for confinement. Finite plasma currents and multiple instability mechanisms remain possible. |

The [BFKK paper](09-literature.md#stability-and-kinetic-theory) includes interface and vacuum terms; reproduce the appropriate full boundary formulation before extending a fixed-boundary result.

## The model hierarchy

Select a model by the phenomenon being certified, rather than making ideal MHD explain every effect.

| Model | Principal use | Additional obligations |
| --- | --- | --- |
| Magnetostatics with specified currents | Coil fields, forces, vacuum geometry | Finite conductor corrections, boundary/circulation data |
| Static isotropic MHD | Pressure/current equilibrium and large-scale stability | Domain, boundary, pressure/current profiles, regularity, model-validity regime |
| Resistive/two-fluid/anisotropic MHD | Reconnection, diffusion, pressure anisotropy, flows | Closure, dissipation, singular perturbation and wall models |
| Guiding-centre dynamics | Drift-orbit and energetic-particle confinement | Small gyroradius ordering, nonvanishing field, reduction error |
| Drift-kinetic/Fokker–Planck | Neoclassical transport, bootstrap current, ambipolar electric field | Collision operator, boundary conditions, conservation, profiles |
| Gyrokinetic dynamics | Microinstability and turbulent transport | Ordering, field equations, energy/free energy, nonlinear closure |
| Vlasov–Maxwell with specified collisions/sources | Higher-fidelity kinetic reference | Well-posedness, high-dimensional analysis, reduction theorems |
| Heat/elasticity/circuit/neutron transport | Component and reactor feasibility | Empirical constitutive laws, coupled source envelopes, life history |

Full-orbit Newton–Lorentz dynamics and Vlasov–Maxwell are also models; do not call one an exact statement of all physical reality. Reduction arrows require quantified theorems or explicit supplied error envelopes.

## Certificate composition

Let `a` describe coil/plasma/component geometry; let `θ ∈ U` collect correlated operating, manufacturing, and material parameters. The useful robust statement is typically

$$
\forall\theta\in U,\quad
\exists e_\theta,\quad
\operatorname{Equilibrium}(a,\theta,e_\theta)
\land \operatorname{Stability}(e_\theta,\theta)
\land \operatorname{Transport}(e_\theta,\theta)
\land \operatorname{Components}(a,e_\theta,\theta).
$$

All parts must use the same witness `eθ`. Independent proofs of `∃ e, Equilibrium e ∧ Stable e` and `∃ e, Equilibrium e ∧ Transport e` do not guarantee a common witness. Prefer a unique gauge-fixed equilibrium branch where possible, or carry the witness through dependent certificate records.

Suppose a proved reference form `qθ₀` has margin `c>0` in norm `V`. Identify all forms on the same admissible space, using a proved pullback when domains change. If a second theorem proves, for `L≥0`,

$$
|q_\theta(\xi)-q_{\theta_0}(\xi)|\le L\|\theta-\theta_0\|\|\xi\|_V^2,
$$

and `‖θ-θ₀‖≤R` for every `θ∈U`, then `LR<c` yields the robust margin `c-LR>0`. A diameter bound is an alternative only when `U` is bounded and `θ₀∈U`. The existence of such a norm-compatible perturbation estimate is a mathematical target, not an automatic consequence of continuity.

## First implementation targets

1. Define a small algebraic equilibrium interface with `μ₀ > 0` and exact force balance; prove field/current tangency.
2. Construct uniform-field, constant-pressure witnesses and a nonzero-current force-free example.
3. Define the certificate/assumption record without any physics-specific global theorem.
4. Formalize exact interval containment and one useful geometric or thermal bound.
5. Define an abstract symmetric energy form and prove the elementary conservation/coercivity theorem before implementing the continuum MHD bridge.

Continue through [08-roadmap.md](08-roadmap.md). Consult [09-literature.md](09-literature.md) for primary sources and an extraction protocol.
