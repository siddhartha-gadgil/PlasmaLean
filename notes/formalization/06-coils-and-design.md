# Coil fields, optimization, and constructible stellarator geometry

This note supplies the geometric and electromagnetic bridge from mathematical fields to hardware. Material/thermal constraints are in [07](07-materials-and-engineering.md); continuous checker methods are in [05](05-verified-numerics.md).

The chapter was written on 12 October 2026 as a specification. Its exposition still states the target mathematics. A status layer, last revised on 30 October 2026, records what has since been compiled, what is assumed, what is open and what was corrected. Sources: the [implementation plan](implementation-plan.md) (the stellarator contract, the research graph and the §13 log), the [30 October progress report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md) and the [repository audit](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-repository-audit.md). "Default build" means the module is imported by `PlasmaLean.lean`. "On demand" means a separate top module, built and axiom-checked on the workstation and spot-checked on the laptop.

## Contents

- [Status in PlasmaLean and the stellarator contract](#status-in-plasmalean-and-the-stellarator-contract)
- [Filament fields](#filament-fields)
- [Finite conductors and plasma coupling](#finite-conductors-and-plasma-coupling)
- [Inverse coil design](#inverse-coil-design)
- [Geometry and manufacturing](#geometry-and-manufacturing)
- [Robust design specifications](#robust-design-specifications)
- [The Dommaschk QA route (Q-16)](#the-dommaschk-qa-route-q-16)
- [A complete candidate workflow](#a-complete-candidate-workflow)
- [Design gates under the contract](#design-gates-under-the-contract)
- [Theorem backlog](#theorem-backlog)

## Status in PlasmaLean and the stellarator contract

Under the [stellarator contract](implementation-plan.md#the-stellarator-contract-30-october-2026), coils are how C1 is met in practice. C1 asks for a rotational transform ι ≥ ι_min > 0 provided by the external field (3-D shaping or helical coils), not by plasma current. An axisymmetric current-free field has ι = 0, so a C1 field cannot be axisymmetric. Non-axisymmetric coils are therefore a consequence of C1, not a design goal in themselves. Coils also have to reproduce a field that satisfies C2 (omnigeneity for thermal particles) and C4 (nested surfaces), and leave room for the engineering contracts of [07](07-materials-and-engineering.md).

| Topic | Compiled evidence (module) | Build | Scope, assumptions, open items |
| --- | --- | --- | --- |
| Filament algebra and bounds | `filamentField_add_current`, `filamentField_reverse`, `filamentField_bound` (`Theory/Fields/BiotSavart`); `filamentField_contDiffOn` (`Theory/Fields/FilamentSmooth`); `inverseCube_derivative_bound` (`Theory/Fields/InverseCube`) | default | Away from the source; higher-derivative constants pending |
| Source-free Maxwell identities | `filamentField_divergence`, `filamentField_curl`, `filamentField_vacuum_maxwell` (`Theory/Fields/Maxwell`) | default | div B = 0 for any filament; curl B = 0 for closed filaments |
| Circular loop | `circularCoil_axis_field` (`Theory/Fields/CircularLoop`) | default | Exact on-axis field |
| Perturbation | `filamentField_perturbation`, `filamentField_sub_current` (`Theory/Fields/CoilPerturbation`); `fieldLine_confined_of_perturbation` (`Theory/Fields/DefectConfinement`) | default | C⁰ field error from position, tangent and current errors; C^k bounds open |
| Vacuum demonstrator | `robust_probe_field`, `combined_field_error`, `manufactured_tube_clearance` (`Design/VacuumTolerance`); `coil_clearance` (`Design/VacuumPair`) | default | Two-loop calibration fixture with invented tolerances; not a confinement design |
| Polygonal coil set | `coil_stellarator_confined_concrete_N` (`Design/PolygonCoilCubicCover`) | default | 52 transits; field-line existence assumed; return conductor idealized at 10⁶ R₀ |
| Coil-field KAM | `CoilKamCert` | on demand | Vacuous residual bound; all-time coil confinement blocked (Q-2) |
| Inverse design, finite conductors, plasma coupling, forces | none | — | Open; design scripts are untrusted generators |

## Filament fields

Let `c:[0,2π]→ℝ³` be a regular closed parametrized curve and `I` its oriented current. At points away from the curve define

$$
B_c(x)=\frac{\mu_0 I}{4\pi}
\int_0^{2\pi}
\frac{c'(t)\times(x-c(t))}{|x-c(t)|^3}\,dt.
$$

Define multi-coil fields by finite sums. Prove:

- linearity in current and superposition;
- reparametrization invariance;
- reversal of curve orientation/current and their sign effects;
- smoothness away from sources;
- `div B=0` and `curl B=0` in a current-free region;
- the chosen Ampère circulation/flux properties with their topological hypotheses.

For `dist(x,c)≥d>0` and curve length `L`, direct kernel estimates give

$$
|B_c(x)|\le\frac{\mu_0|I|L}{4\pi d^2},\qquad
\|DB_c(x)\|\le\frac{2\mu_0|I|L}{4\pi d^3}.
$$

The derivative bound uses the operator norm of `D(r/|r|³)`, whose largest absolute eigenvalue is `2/|r|³`. Derive higher derivative constants when needed. These are useful for interval quadrature, orbit error, and tolerance propagation.

Prove the circular-loop field on its axis as a sanity example:

$$
B_z(z)=\frac{\mu_0 I R^2}{2(R^2+z^2)^{3/2}}.
$$

Keep direction determined by the actual current orientation.

**Status in PlasmaLean.** Most of this section is compiled in the default build:

- **Algebra.** Linearity in the current, zero current and orientation reversal: `filamentField_add_current`, `filamentField_zero_current`, `filamentField_reverse` (`Theory/Fields/BiotSavart`).
- **Bounds and smoothness.** The direct bound `filamentField_bound` assumes a source distance. Smoothness away from the source is `filamentField_contDiffOn` (`Theory/Fields/FilamentSmooth`). The kernel derivative bound with the factor 2/‖r‖³ is `inverseCube_derivative_bound` (`Theory/Fields/InverseCube`).
- **Maxwell identities.** Away from the curve, div B = 0 for any filament and curl B = 0 for a closed filament (`filamentField_divergence`, `filamentField_curl`, `filamentField_vacuum_maxwell` in `Theory/Fields/Maxwell`). An open filament has a curl term (`filamentField_curl_open`).
- **Circular loop.** The on-axis field is exact (`circularCoil_axis_field`, `Theory/Fields/CircularLoop`).
- **Complex extension.** `Theory/Fields/BiotSavartComplex` extends the field to complex arguments for the coil-KAM work.

Not done: reparametrization invariance as a named theorem, higher-derivative constants, and the Ampère circulation properties.

## Finite conductors and plasma coupling

A filament field is singular on its source and cannot supply its own peak conductor field or self-force. Introduce a finite conductor `Ω_c` with vector current density `J_cond`:

$$
B_c(x)=\frac{\mu_0}{4\pi}\int_{\Omega_c}
\frac{J_{\rm cond}(y)\times(x-y)}{|x-y|^3}\,dy,
$$

under adequate integrability/current closure conditions. Handle points in or near the conductor through the appropriate regularity/PDE theory and quadrature, not by evaluating a singular filament formula there.

Prove a far-field/finite-width comparison between a specified winding-pack distribution and its centreline approximation, with distance and current-moment bounds. Use the finite-conductor field for critical-current and load certificates.

At finite plasma pressure the equilibrium field is not merely the vacuum field generated by coils:

$$
B_{\rm total}=B_{\rm coils}+B_{\rm plasma}
$$

with interface/boundary conditions and self-consistent plasma currents. A virtual-casing calculation can propose the external field to reproduce a fixed-boundary equilibrium, but needs a sound reconstruction/error theorem before certification.

For a conductor in an external field the force density is `J_cond×B`. Include self-consistent finite-width electromagnetic stress/self-force appropriately. Distinguish the magnetic pressure scale `B²/(2μ₀)` from a universal support-stress formula. The structural model must transmit the actual distributed loads.

**Status in PlasmaLean.** Nothing in this section is compiled. All coil results are filament results, and enclosing a filament in a tube (`Theory/Geometry/CoilTube`) does not create a finite-conductor electromagnetic model. All field results are vacuum results, so there is no B_plasma, no virtual-casing theorem and no force or stress model. Under the contract this coupling becomes necessary at finite β: a current-free finite-β equilibrium (Q-20, via Q-14) must be matched to coils.

## Inverse coil design

Use [SIMSOPT, DESC, REGCOIL, and coil-design papers](09-literature.md#design-algorithms-and-software) as candidate generators. Record software version and conventions, particularly field periods, stellarator symmetry, Fourier signs, currents, and units.

For a winding surface `S_w` a surface-current potential has the form

$$
K=n\times\nabla_s\Phi,
$$

with periodic and prescribed multivalued/circulation components as required by the chosen topology. Prove surface-current conservation and the field representation. Single-valued `Φ` alone omits possible net current periods.

The inverse problem may minimize

$$
\|B\cdot n_{\rm target}\|^2_{L^2(S_p)}
+\lambda\|K\|^2_{L^2(S_w)}
$$

or optimize explicit curves. The achieved objective is evidence about that objective. It is not by itself a proof of a nearby exact equilibrium, invariant tori, robust confinement, or coil feasibility.

For practical bounds, prove how a field or normal-field residual in a declared norm controls the next physical quantity. An `L²` boundary residual does not imply a pointwise residual without extra regularity/inverse estimates.

For quasisymmetry define the intended residual precisely, including radial weights, angle measure, normalization, and omitted modes. Prove its zero characterization within the chosen function class. Compare near-axis, global-boundary, and simultaneous coil/plasma design formulations without identifying their objectives.

**Status in PlasmaLean.** No inverse-design theorem is compiled. The coil geometries in the library come from untrusted design scripts (`scripts/rational_stellarator_coils/`), and only the Lean certificate about the resulting field is trusted.

- **Polygonal coil set (default build).** `coil_stellarator_confined_concrete_N` (`Design/PolygonCoilCubicCover`) covers the field `tfField + polyCoilFieldC`: 8 closed polygonal helical filaments with 192 straight segments, plus a toroidal-field filament. Every field line starting in a start tube stays in the confinement tube over [0, 8·52], and its toroidal angle advances by at least 2π·52, so it makes **52 transits**. The certified winding error on the frontier is about 3.221·10⁻⁶, which is a 0.016 % margin against the 52-transit budget. An earlier one-transit version with 128 segments had zero margin (`coil_stellarator_confined_concrete`, `Design/PolygonCoilConfined`). Two scope caveats, both recorded by audit L-5:
  - the field line is **assumed** to solve the field-line equation; its existence is not proved;
  - the toroidal-field filament `tfField` is a rectangle with a central post and a **return conductor idealized at 10⁶ R₀**, which is not constructible.
- **Coil-field KAM is blocked (Q-2).** The on-demand certificate `CoilKamCert` proves only a vacuous residual bound: about 10⁹, against about 10⁻³⁰ needed. The barriers are:
  - a sharp, cancellation-aware complex sup bound for the coil field;
  - a torus-adapted neighbourhood and anisotropic strips;
  - a high-precision refit, estimated at about 4 CPU-days.

  All-time confinement in a coil-produced field (G-5) is therefore open research (see the [coil-KAM status](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/coil-kam-status.md)).
- **Quasisymmetry residuals.** The precise residual this paragraph asks for exists as `qsDefect` in `Theory/Fields/WeakQuasisymmetry`. Its zero characterization is `qsDefect_eq_zero_iff`, and it is a pointwise sup, not an L² objective. No optimization objective has been related to it.

## Geometry and manufacturing

Represent each physical coil by its centreline, a material frame, cross-section, casing, insulation, supports, and assembly state. Use an oriented ribbon or winding-pack model for tape; curvature of the centreline alone does not determine hard-way bending or torsional strain.

Required continuous properties include:

| Constraint | Mathematical statement |
| --- | --- |
| Regular coil | `‖c′‖≥v_*>0` and periodic smoothness |
| Nonintersecting pack | Embedded swept solid with positive Jacobian and nonlocal separation |
| Curvature/strain | Pointwise limits everywhere along every turn and across the pack |
| Coil–coil clearance | Separation of physical swept solids including casings/tolerances |
| Plasma–coil budget | Space for vacuum gap, wall, blanket, shielding, supports, and allowable motion |
| Ports and divertor access | Exclusion/clearance constraints for concrete service volumes |
| Manufacturable winding | Material frame and allowed bend/twist/length constraints |
| Maintainability | A continuous collision-free removal/installation path for selected components |

Prove continuous bounds via [05](05-verified-numerics.md). Avoid self-distance checks that reject adjacent points on the same coil simply because parameter values differ.

The distances `0.52 m`, `0.83 m`, and `1.4 m` in the starting note are not established universal limits. Select a machine/material source and an engineering budget. Scaling a geometry by `s` scales length and clearances by `s` and curvature by `1/s`; required current and component forces have additional scaling laws to derive, so geometric scale invariance does not imply equal feasibility.

Intentional edge islands can serve an island divertor. Distinguish the confinement core from the exhaust region instead of forbidding every magnetic island. See [W7-X divertor studies](09-literature.md#engineering-materials-and-experiment).

**Status in PlasmaLean.**

- **Compiled (default build).**
  - Placed circles in arbitrary 3-D position stay closed, C¹ and simple, with a position-error bound (`placedCircle_C1`, `placedCircle_periodic`, `placedCircle_injective_on_turn`, `placedCircle_position_error` in `Theory/Geometry/PlacedCircle`).
  - Tube envelopes with clearance, disjointness and transfer of manufacturing margins (`tube_clearance`, `tubes_disjoint`, `perturbed_tube_subset` in `Theory/Geometry/CoilTube`).
  - The Lipschitz-cover clearance lemma of [05](05-verified-numerics.md#continuous-geometry-and-quadrature).
- **Vacuum demonstrator.** Its fixture certifies tube-to-tube clearance of at least 0.388 m including centreline errors (`manufactured_tube_clearance`).
- **Not done.** Embedded winding packs, self-clearance with reach, material frames and strain, ports, the plasma–coil space budget, and removal paths.

## Robust design specifications

Let `a` be nominal design coefficients and `θ∈U` manufacturing/operating variations. Include coil displacements, current calibration, pressure/current-profile changes, thermal expansion, and material degradation.

Prove field perturbation bounds in the norms needed downstream, for example

$$
\|B(a,\theta)-B(a,\theta_0)\|_{C^k(\Omega)}
\le L_k\|\theta-\theta_0\|,
$$

with a common positive conductor-distance margin. A symmetry-breaking or normal-field scalar objective does not automatically yield this bound.

Translate downstream margins into tolerance budgets. Clearance margins use finite-solid displacement bounds. Stability margins require form perturbation bounds. Orbit margins require field derivatives and a time-dependent comparison. Magnet margins require field orientation, temperature, and strain.

Prove robust feasibility for a useful candidate before attempting global optimality. Keep objectives and hard certified constraints separate; a penalty term does not turn a violation into a theorem.

**Status in PlasmaLean.** The C⁰ part of the perturbation bound is compiled:

- `filamentField_perturbation`: a field error from full-parameter position and tangent errors at a common source-distance margin.
- `filamentField_sub_current`: the effect of a current error.
- `fieldLine_confined_of_perturbation` (`Theory/Fields/DefectConfinement`): a field perturbation is turned into finite-time field-line confinement.

The [vacuum demonstrator](../design/vacuum-demonstrator.md) composes these into a tolerance-aware fixture (`Design/VacuumPair`, `Design/VacuumTolerance`). It uses position and tangent errors of 1/1000, current errors of 1 %, a field-error budget over the whole observation ball (`combined_field_error`) and a robust probe field (`robust_probe_field`). The tolerances are invented exact test inputs, and the fixture is a two-loop calibration device, not a toroidal confinement design. Its role under the contract is a technique demonstrator. The C1 witness in vacuum is the rational stellarator field (`RationalStellarator.field_vacuum`, `rationalStellarator_confined_forever_exists`), which is a field, not a coil set.

Open: C^k bounds, stability margins under perturbation, and orbit margins under perturbation.

## The Dommaschk QA route (Q-16)

This section was added on 30 October 2026. Under the contract the first design priority is a field that satisfies C1 and C2 together (RG.5 item 1, Q-16 route (ii) of the [quasisymmetric-solution note](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/quasisymmetric-solution.md)). The route is chosen so that the hard steps become certificates of kinds already in the library:

1. **Field.** Take B = B₀R₀∇φ + ∇h, where h is a finite sum of Dommaschk potentials with rational coefficients from an untrusted least-squares fit to a quasi-axisymmetric target. Each potential is exactly harmonic, so B is a vacuum field by an algebraic identity. That gives J = 0 and hence zero net toroidal current (C1, current part), checkable by polynomial normalization as for `RationalStellarator`.
2. **Tori and ι.** Certify invariant tori with the a posteriori KAM pipeline already used for torus A (`torusA_exact`). Each torus carries a Diophantine ι_j, giving ι ≥ ι_min on a nested family (C1, transform part; C4 in vacuum).
3. **Boozer angles.** On each torus, Boozer angles follow from one more cohomological equation with the same small divisor (`cohSol_estimate`, `Theory/KAM/Cohomological`).
4. **QS defect.** Bound the non-QA Fourier part of ‖B‖ in ℓ¹ on each torus, reported relative to ι. This is the decided vacuum criterion of Q-16.
5. **C2.** Turn the certified QS defect into a bound on the bounce-averaged radial drift through the quasisymmetry ⇒ omnigeneity bridge (Q-23, in progress). For thermal particles this is the route to C2.

The coils that produce this field are **not** part of the claim; producing them is a separate question, Q-2 and G-5. The main risks are:

- fit quality against QS quality (B1);
- low magnetic shear, which weakens the KAM twist constant (B2), with a finite-time fallback through `fieldLine_confined_of_defect`;
- narrow analyticity strips for strongly shaped surfaces (B3).

Status: **nothing compiled yet**. The fit generator and the torus certificate are next. Strong quasisymmetry in a volume is open mathematics (Q-24); the design route does not depend on it.

## A complete candidate workflow

1. Specify the machine class and operating/material envelope.
2. Propose an axis/surface/coil/current parameterization from theory.
3. Search candidate geometries and choose a useful finite representation.
4. Certify embeddings, regularity, swept-solid clearances, and fields.
5. Validate a model-consistent equilibrium and its boundary conditions.
6. Certify the chosen MHD stability property on its full admissible space.
7. Certify particle loss/transport/exhaust quantities at the required level.
8. Bound heat, mechanical, magnet, irradiation, and lifetime constraints.
9. Propagate common uncertainties and compose the contracts for one candidate.
10. Record remaining model-validity evidence and the next physical validation step.

Separate proofs for different equilibria or operating profiles cannot be combined into one design certificate without a common-witness theorem.

The common-witness framework exists (`Bridge/Contracts`) but is not instantiated for any candidate (audit L-12).

## Design gates under the contract

This section was added on 30 October 2026. The contract reorders the workflow above. A candidate is filtered first by C1 (current-free ι from the field) and C2 (omnigeneity for thermal ions and electrons), then by C4, C3 and C5, and only then by coils and engineering. G-8 is the integrated candidate that satisfies C1–C5 with common witnesses. **No candidate passes all gates.**

| Candidate | C1 | C2 | C3 | C4 | C5 | Coils |
| --- | --- | --- | --- | --- | --- | --- |
| Rational vacuum field `RationalStellarator.field (1/4)` | Vacuum: J = 0 (`field_vacuum`); KAM torus with ι ≈ 0.137 | Unknown (Q-19); not optimized for omnigeneity | Vacuum only (β = 0) | Inside one certified torus (`rationalStellarator_confined_forever_exists`) | None | Polygonal approximation, 52 transits, existence assumed; all-time blocked (Q-2) |
| Dommaschk QA field (planned) | By construction (vacuum); ι from certified tori | Through the QS defect and Q-23 | Needs finite β (Q-20) | Certified tori | None | Not part of the claim |
| Landreman families 1 and 2 | **Fail**: family 2 carries a positive net toroidal current (`torCurrent_eq`; Q-18) | Not weakly quasisymmetric (`family1_not_weakQS`, `family2_not_weakQS`) | Family 2 Mercier band (`family2_mercier_stable_derived`), a test bed | Force balance at finite β | None | None |
| Solov'ev reactor field | **Fail**: axisymmetric and current-carrying (a tokamak model) | Axisymmetric, so trivially omnigenous in the model sense | Tokamak results | Exact | `solovev_one_plasma_actual` (tokamak model, supplied transport solution) | None |

Under the contract the gate order is:

1. C1 and C4 in vacuum: the rational field, then the Dommaschk QA field.
2. C2 on the same field (Q-23, Q-19, Q-16).
3. A finite-β current-free equilibrium (Q-20, via Q-14) with C3 on it.
4. C5 with C2-derived neoclassical losses (Q-22).
5. Coils that reproduce the field (Q-2) and the engineering contracts of [07](07-materials-and-engineering.md).

## Theorem backlog

| ID | Target | Main dependency |
| --- | --- | --- |
| D1 | Biot–Savart algebra, smoothness, and field/derivative bounds | Integration and source separation |
| D2 | Circular-loop and orientation sanity cases | Exact integration |
| D3 | Continuous curve/surface/solid geometric certificate | Interval coverage, embedding/reach |
| D4 | Finite-width-to-filament error and conductor field | Current distributions and magnetostatics |
| D5 | Coil perturbation bounds in `C^k` norms | D1/D4 and quantified geometric perturbations |
| D6 | Certified inverse field reconstruction | Boundary/inverse estimates and regularization |
| D7 | Free-boundary plasma/coil consistency | [02](02-plasma-models-and-equilibrium.md) and [03](03-mhd-stability.md) |
| D8 | Robust physics–engineering candidate | All contracts; major development/research |
| D9 | Removal paths and robust manufacturing margins | Configuration-space geometry |

The progress column is generated from `progress/status.json`; the status sections above give the reading of 30 October 2026. In short:

- D1 and D2 are largely compiled.
- D3 and D5 are partial: placed circles and tubes, C⁰ perturbation bounds, and the 52-transit polygonal coil set with field-line existence assumed.
- D4 and D6–D9 are open.
- All-time coil confinement is blocked (Q-2).
