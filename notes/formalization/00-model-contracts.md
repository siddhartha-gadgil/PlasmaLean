# PlasmaLean: model contracts and the meaning of a design proof

Prepared 10 October 2026 from [PlasmaLean](https://github.com/siddhartha-gadgil/PlasmaLean), commit `466920416e97561e4669759ab4077b9a23281ebd`, [domain-libraries.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/466920416e97561e4669759ab4077b9a23281ebd/notes/domain-libraries.md), [Stellerator.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/466920416e97561e4669759ab4077b9a23281ebd/notes/Stellerator.md), and the [website](https://siddhartha-gadgil.github.io/PlasmaLean/index.html). The checked source has starter Lean code and pins Lean/Mathlib `v4.34.1`. These notes propose new mathematics and implementation; they do not report completed formalizations.

## Contents

- [Contracts](#contracts)
- [Architecture](#architecture)
- [Stellarator contract: C1, C2 and C5](#stellarator-contract-c1-c2-and-c5)
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
| `CurrentFreeTransform` (C1, partly in Lean: `Contract.CurrentFreeTransform`, `netToroidalCurrent`, `IotaOnTorus` in `Theory/Contract/StellaratorContract`) | Toroidal domain, field, family of invariant tori, net toroidal plasma current bound I_max, lower bound ι_min > 0 on the rotational transform; see [stellarator contract](#stellarator-contract-c1-c2-and-c5) |
| `BounceAveragedDrift`, `Omnigenous`, `EffectiveRippleBound` (C2, partly in Lean: `Contract.OmnigeneityContract` over `Kinetic.Boozer.OmnigenousOn`/`ApproxOmnigenousOn`, Boozer guiding-centre model; `EffectiveRippleBound` not in Lean) | Field, certified surfaces, guiding-centre model, species (thermal ions and electrons), energy and pitch ranges, trapped-orbit class, drift or ε_eff bound; see [stellarator contract](#stellarator-contract-c1-c2-and-c5) |
| `ThermalPerformance` (C5, not yet in Lean as a contract predicate) | The same candidate as C1–C4, operating interval, power balance (Bosch–Hale alpha heating, bremsstrahlung, transport losses), neoclassical losses from C2, supplied anomalous scaling, burn threshold and wall limits; see [stellarator contract](#stellarator-contract-c1-c2-and-c5) |

Avoid an unqualified `Stable : Prop` encompassing all these meanings. In particular, linearly stable ideal MHD is compatible with kinetic microinstabilities and poor confinement.

Record each assumption's origin: mathematical theorem; chosen model law; measured datum or empirical fit; machine requirement; or unresolved research hypothesis. Keep arithmetic error, discretization error, parameter/data uncertainty, and model discrepancy separate.

## Stellarator contract: C1, C2 and C5

Added 30 October 2026 with the user-approved restructuring of the plan around the stellarator
contract (`notes/implementation-plan.md`, section "The stellarator contract"): C1 current-free
rotational transform, C2 omnigeneity or small neoclassical transport for thermal particles, C3
finite-β MHD stability, C4 existence, C5 thermal performance on the same candidate. C3 and C4 use the existing predicates `LinearMHDStable` and
`EquilibriumExists`/`FieldLineBarrier`. The entries below for C1, C2 and C5 are **normative
specifications** (plan question Q-21, goal G-11); C1 and C2 are partly in Lean (status below), C5 is
not yet in Lean. A Lean definition that
implements them must reproduce the listed content and pass the sanity triad before any claim uses it.

**Lean status (30 October 2026, Q-21, Q-18): C1 and C2 partly in Lean** (default build, standard
axioms only). Module `PlasmaLean/Theory/Contract/StellaratorContract.lean`, namespace
`PlasmaLean.Contract`:

- C1 net current: `ampereCurrent μ₀ B` (`(∇ × B)/μ₀` of the same field), `netToroidalCurrent μ₀ B X
  ζ₀ k₀` (flux of that current through the section `ζ = ζ₀`, `0 ≤ k ≤ k₀`, of a toroidal
  coordinate map `X`), `NetCurrentBound`, `CurrentFree`; vacuum gives zero
  (`netToroidalCurrent_eq_zero_of_vacuum`, `currentFree_of_vacuum`); degenerate
  `netToroidalCurrent_zero_field`; counterexample `netToroidalCurrent_rotation` (`4πk₀/μ₀` for
  `B = e_z × x`), `rotation_not_currentFree`.
- C1 transform: `FieldTorus B R z ι` (torus in cylindrical form, field-line flow conjugate to the
  linear flow of slope ι), `PoloidalAngle` (angle convention about a fixed reference circle; without
  it ι is defined only modulo integers), `IotaOnTorus`; `IotaOnTorus.tendsto` (ι is the asymptotic
  poloidal advance per toroidal radian along field lines). Tokamak exclusion:
  `iota_eq_zero_of_purelyToroidal` (purely toroidal field, e.g. vacuum axisymmetric
  `B = (μ₀I/2πR) e_φ` ⇒ ι = 0) and `not_currentFreeTransform_of_purelyToroidal`.
- C1 predicate: `SurfaceData`, `SurfaceData.Spans` (section spans the poloidal loop of the torus),
  `CurrentFreeTransform μ₀ B S I_max ι_min`; `currentFreeTransform_of_vacuum`,
  `not_currentFreeTransform_of_current`, `CurrentFreeTransform.mono`.
- C2: `OmnigeneityContract F c κ_max` (`ApproxOmnigenousOn` of `Theory/Kinetic/Omnigeneity`; `κ_max
  = 0` is `OmnigenousOn`, `omnigeneityContract_zero_iff`), scope: the vacuum Boozer guiding-centre
  model (supplied), all species, μ and energies. `BoozerAxisymmetric`; axisymmetric ⇒ omnigenous
  (`omnigenousOn_of_axisymmetric`, ι ≥ ι_min > 0; `omnigenousOn_of_axisymmetric_iota_zero`, ι = 0,
  vacuously); `constField_omnigeneityContract`; counterexample
  `driftMirror_not_omnigeneityContract`.
- Instances (`Design/RationalStellaratorContract`): **C1 witness**
  `rationalStellarator_currentFreeTransform` (`field (1/4)`, `I_max = 0`, ι_min = ι_A =
  (75 + √5)/562 on the exact KAM torus near torus A; `ExactTorus.iotaOnTorus`); tokamak exclusion
  for `∇φ`: `toroidal_not_currentFreeTransform`, with `circTorus_iotaOnTorus` (ι = 0 attained) and
  `toroidal_circ_current_zero` (it passes the current clause). (`Design/LandremanNetCurrent`, Q-18):
  `torCurrent_eq_netToroidalCurrent` (rfl), `family2_net_current_pos` (I_tor > 0 for μ₀ > 0,
  λ > 0, 0 < k₀ < 19/20), `family2_net_current_ge` (λ-independent lower bound 2π `curInf`/μ₀),
  `family2_not_currentFree`, `family2_not_currentFreeTransform` (fail the section-flux clause for
  I_max < I_tor(k₀)). **Audit AR-H1 (31 October 2026):** the section-flux clause is vacuous with
  degenerate sections (`Sanity/AuditRefreshContract`), so this does not establish that family 2
  fails C1. The clause is being restated as the circulation of B around the torus's poloidal loop.
- Still open: ε_eff (`EffectiveRippleBound`) and the 1/ν link; a generic 3-D field with an
  explicit trapped orbit and nonzero drift beyond the Boozer model fixture `driftMirror`; the
  theorem "axisymmetric, current-free, nested surfaces ⇒ purely toroidal" (maximum principle for
  Δ*ψ = 0); section-independence of the net current (the contract fixes a spanning section);
  moving reference curves for the poloidal angle; a nested family of certified tori with
  ι ≥ ι_min for the rational stellarator (only one exact torus); family 1's net current; the
  identification of the Boozer model with a Cartesian field.

### C1: `CurrentFreeTransform` (net toroidal current; ι from the field)

| Component | Required content |
| --- | --- |
| Domain and section | A toroidal domain Ω (open, solid-torus-like) and an oriented cross-section Σ ⊂ Ω (a surface bounded by a poloidal loop on ∂Ω, or the part of a section inside a flux surface S). The definition must state which surface is used; the value is section-independent when ∇·J = 0 and J·n = 0 on the flux surfaces (a theorem obligation, not an assumption) |
| Net toroidal current | I_tor(S) = ∫_Σ J·n dA with J = (∇ × B)/μ₀, the Ampère current of the same field (not a separately supplied J). Equivalently, by Stokes, μ₀ I_tor = ∮ B·dl around a poloidal loop on S, minus nothing (no external conductor threads the poloidal loop inside Ω). Units: A |
| Current bound | ‖I_tor(S)‖ ≤ I_max for every confining surface S, with I_max a stated number and its origin recorded (bootstrap-level estimate, a machine requirement, or 0). Vacuum (J = 0 on Ω, the kernel `VacuumField`) implies I_tor = 0 and is the limiting case |
| Rotational transform | A family of invariant tori (certified, e.g. KAM tori with explicit parametrizations) on which the field-line flow is conjugate to a linear flow with rotation number ι(S), or ι(S) = dψ_p/dψ_t from flux labels; the definition fixes the angle conventions and the orientation |
| Transform bound | ι(S) ≥ ι_min > 0 for every confining surface S, with ι_min stated |
| Provenance clause | The contract is `I_tor bound ∧ ι bound` on the same field and surfaces; "provided by the field" means precisely the current bound, so no further clause is needed |
| Sanity triad | (1) witness: the exact rational stellarator vacuum field with its certified torus (I_tor = 0, ι ≈ 0.137); (2) **current-free axisymmetric ⇒ ι = 0**: an axisymmetric field with I_tor = 0 on every surface has zero poloidal field on the surfaces, hence ι = 0, so it fails C1 for every ι_min > 0 (no confining transform); (3) a tokamak-like field (Solov'ev, or Landreman family 2 with I_tor > 0) violates the current bound for small I_max |
| Not covered | Current profiles inside S (only the net current), surface currents of stepped-pressure equilibria (to be included via a measure-valued J or a jump condition), external conductors threading the domain |

### C2: `BounceAveragedDrift`, `Omnigenous`, `EffectiveRippleBound`

| Component | Required content |
| --- | --- |
| Model | A guiding-centre model named as a hypothesis (Littlejohn or a Boozer-coordinate drift model), species (charge, mass), energy E and magnetic moment μ (or pitch λ) ranges; the flux label ψ and field-line label α on certified surfaces with a chart (Boozer or other straight-field-line angles) whose existence is proved |
| Trapped orbits | For fixed (ψ, α, E, μ), a bounce interval between consecutive turning points where v∥ = 0 on the field line, with v∥ ≠ 0 inside; nondegeneracy of the turning points (B·∇B ≠ 0 there) stated or the degenerate (marginally trapped) set excluded |
| Bounce-averaged radial drift | ⟨ψ̇⟩_b = (∮ v_d·∇ψ dl/v∥) / (∮ dl/v∥), with v_d the drift velocity of the stated model; equivalently, in terms of the second adiabatic invariant J = ∮ m v∥ dl, ⟨ψ̇⟩_b is proportional to ∂J/∂α. The proportionality must be a theorem in the chosen model |
| `Omnigenous` | ⟨ψ̇⟩_b = 0 for every trapped orbit in the stated class on every confining surface (equivalently J independent of α). Quasisymmetry (‖B‖ depends on ψ and one helical angle) and quasi-isodynamicity (poloidally closed ‖B‖ contours) are sufficient conditions, to be proved as theorems |
| Bounded drift | The quantitative form: sup ‖⟨ψ̇⟩_b‖ ≤ D over the class, with D and its units stated, for thermal ions and electrons at stated temperatures (not only 3.5 MeV alphas) |
| `EffectiveRippleBound` | ε_eff(ψ) ≤ ε_max on the confining surfaces, with ε_eff defined exactly as in Nemov–Kasilov–Kernbichler–Heyn (Phys. Plasmas 6, 4622, 1999), including the field-line length and the normalization (reference field B₀, major radius R₀); a certified value needs enclosures of the bounce integrals, not samples. The link to a 1/ν-regime diffusivity (χ ∝ ε_eff^{3/2}) is a supplied model law, used only in G-2 (Q-22) |
| Sanity triad | (1) **axisymmetric ⇒ omnigenous**: in an axisymmetric field ⟨ψ̇⟩_b = 0 for every trapped orbit (canonical momentum conservation), so ε_eff = 0; (2) consistency with C1: an axisymmetric field passes C2 but fails C1 when current-free (ι = 0), so C1 ∧ C2 excludes tokamaks and trivial fields; (3) a generic 3-D field is not omnigenous: an explicit field (for example a field with a single-harmonic helical ripple on a torus) with a trapped orbit class and ⟨ψ̇⟩_b ≠ 0 |
| Not covered | Collisions, the radial electric field (E × B drift, which matters in stellarators and must be added as a separate clause), finite orbit width, and turbulence; C2 alone is not a transport bound (`TransportBound` remains separate) |

### C5: `ThermalPerformance` (temperature on the same candidate)

| Component | Required content |
| --- | --- |
| Candidate | The **same** decoded field, equilibrium and surfaces that satisfy C1–C4 (common witness), with the flux-surface geometry of that equilibrium (volumes, ⟨‖∇ψ‖²⟩) used in the transport model |
| Requirement | Core temperature T(0, t) ≥ T_burn (e.g. 10 keV) for t in the operating interval [0, T_op] (or all t ≥ 0), and temperature and heat flux at the edge and wall below stated wall and material limits |
| Power balance | Alpha heating from Bosch–Hale reactivity (enclosure supplied as a named law), bremsstrahlung with the Z_eff of a quasineutral composition (`PhysicalPlasma.composition`), auxiliary heating if any, and transport losses |
| Transport losses | Neoclassical part derived from C2 (an ε_eff or bounce-averaged-drift bound turned into χ bounds for thermal ions and electrons through a stated neoclassical law, e.g. 1/ν regime χ ∝ ε_eff^{3/2}); anomalous (turbulent) part a stated, supplied scaling (ISS04 with its renormalization factor, or an available-energy Â bound). Never hidden in a free constant |
| Solution | The transport solution either constructed (existence proved) or explicitly supplied as a hypothesis, stated in the scope of every claim; pressure equal to (not only bounded by) the force-balance pressure for a full consistency claim |
| Coupling | C2 couples into C5: poor omnigeneity means large 1/ν losses, which can make burn inaccessible (compare the proved Stellaris obstructions at measured renormalization factors) |
| Sanity | (1) witness: the Solov'ev budget results (`solovev_one_plasma_actual`), which satisfy the temperature clause for a **tokamak model** with a supplied transport solution, hence not C5 for a stellarator candidate; (2) obstruction: with the measured ISS04 renormalization the 0-D steady state is inaccessible (`stellaris_measured_fren_no_access_steady`); (3) monotonicity: increasing the loss (larger ε_eff or χ) cannot turn an inaccessible burn into an accessible one |
| Not covered | Profile control, impurity accumulation, alpha ash, density limits and exhaust, unless added as separate clauses |

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
