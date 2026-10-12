# Vacuum demonstrator: from a calibration fixture to a stellarator

## What we are building

The selected first product is a small vacuum-field demonstrator, not a fusion reactor. The present Lean-certified geometry is a two-loop **calibration fixture**. It checks continuous field calculations, differentiation, metrology budgets and finite-thickness clearance envelopes. It is not a toroidal confinement design.

The next stellarator configuration to investigate is a four-circular-coil arrangement inspired by the Columbia Non-neutral Torus (CNT): two interlinked coils and two poloidal-field coils. This is a sourced reference architecture, not an assertion that CNT has been reproduced or that shrinking it preserves its operating margins. Arbitrarily oriented circles are now supported by the library; a complete, sourced four-coil placement/current dataset still needs to be frozen.

## Exact fixture and checked margins

All lengths below are in metres, fields in tesla for consistent SI inputs, and the angle parameter is in radians. Permeability μ₀ and reference current I remain positive symbolic parameters. No obsolete exact numerical value for μ₀ is assumed.

| Quantity | Specification or proved consequence |
| --- | --- |
| Nominal coils | Radius 1/10, planes z=±1/5; counterclockwise viewed from positive z |
| Full observation region | Euclidean ball of radius 1/20 about the origin |
| Actual-coil assumptions | Closed C¹ curves; continuous actual derivatives; common angular parameter |
| Position error | At most 1/1000 everywhere along each coil |
| Tangent error | At most 1/1000 m/radian everywhere; a separate requirement from position error |
| Actual tangent speed | Between 99/1000 and 101/1000 m/radian |
| Current error | Each actual current independently differs from I by at most I/100 |
| Field-error budget | Norm of actual minus nominal field at most μ₀I/4 throughout the full observation ball |
| Probe region | Entire ball of radius 1/1000, not just its centre or a sample grid |
| Probe field direction | Actual axial component at least μ₀I/4; hence actual field is nonzero |
| Spatial derivative | Actual Fréchet derivative exists throughout the observation ball; its norm is at most (25250/343)(abs(μ₀J₁)+abs(μ₀J₂)) |
| Finite-thickness envelopes | Radius 1/200 about each actual centreline |
| Envelope-to-envelope clearance | At least 97/250 = 0.388 m, including both centreline errors |

These tolerances and envelope radii are invented exact test inputs. They have **not** been derived from a supplier, metrology campaign, conductor specification or stress/thermal model. The field remains a filament field: enclosing it in a tube does not establish a finite-conductor electromagnetic model. Individual tube self-embedding and actual-coil simplicity under deformation are not yet certified.

## Why this fixture is not confinement

A positive field at the centre is not an invariant torus. The new sanity theorem goes further: for any classical field line satisfying γ′(s)=B(γ(s)), if the entire line segment stays in the 1 mm probe ball for s∈[0,T], then Tμ₀I≤1/125 under the same manufacturing/current assumptions. Thus the probe certificate cannot justify indefinitely trapped field lines in that ball.

The field-line parameter s has SI units m/T, not seconds. This is not a particle residence-time calculation. It does not rule out confinement elsewhere, and it does not assert trajectory existence. The fixture is useful for calibration; a different field geometry and a separate barrier/orbit theorem are needed for a stellarator.

## Reusable proof interfaces

The complete elementary perturbation argument is:

1. Let the nominal source distance be at least d+ε, with position error ε and d>0. The whole interpolation ball is then separated by d.
2. The inverse-cube mean-value bound gives a radial-kernel change of at most 4ε/d³.
3. With reference tangent norm at most V and tangent error η, bilinearity gives a Biot–Savart kernel error at most η/d²+4Vε/d³.
4. Integrating over the whole angle interval and multiplying by abs(μ₀I/(4π)) gives the field error. Linearity handles current calibration separately.
5. The actual field's derivative is obtained by dominated differentiation on one common source-separated spatial neighbourhood. The derivative norm is bounded before integration; it is not a finite-difference estimate.

For a circular coil in a rigid pose, centre displacement ε and pose-operator error α give position error at most ε+α abs(R) and tangent error at most α abs(R). Pose error is an operator norm, not an angle in degrees. The representation allows reflections; no incorrect rotation-only magnetic transformation law is assumed.

Principal compiled declarations, with common prefix `PlasmaLean.`:

| Module | Entry points |
| --- | --- |
| `Theory/Fields/CoilPerturbation.lean` | `Fields.filamentField_perturbation`, `filamentField_sub_current` |
| `Theory/Fields/FieldDerivative.lean` | `Fields.filamentField_derivative`, `filamentField_derivative_bound` |
| `Theory/Geometry/CoilTube.lean` | `Geometry.tube_clearance`, `tubes_disjoint`, `perturbed_tube_subset` |
| `Theory/Geometry/PlacedCircle.lean` | `Geometry.placedCircle_derivative`, `placedCircle_injective_on_turn`, `placedCircle_position_error`, `placedCircle_tangent_error` |
| `Design/VacuumTolerance.lean` | `Design.VacuumPair.placed_circle_within_tolerance`, `combined_field_error`, `robust_probe_field`, `manufactured_tube_clearance` |
| `Design/VacuumDerivative.lean` | `Design.VacuumPair.actual_speed_bounds`, `manufactured_field_derivative`, `zero_current_derivative` |
| `Sanity/ProbeEscape.lean` | `Sanity.bounded_observable_duration`, `probe_fieldLine_duration`, `no_forever_probe_fieldLine` |

## Primary reference and its limits

Kremer, Pedersen, Pomphrey, Reiersen and Dahlgren, *The Status of the Design and Construction of the Columbia Non-neutral Torus* (2003), DOI 10.1063/1.1635192: the author manuscript's “Present design specifications,” PDF pp. 2–3, gives IL radius 0.405 m, PF radius 1.08 m, nominal major/minor scales 0.3/0.1 m and field range 0.05–0.2 T. “Computational studies,” pp. 3–5, uses distributed thin-wire representations and numerical field-line studies. These are historical design inputs and simulations, not guaranteed intervals or a Lean confinement theorem. [PPPL-hosted full manuscript](https://w3.pppl.gov/theory/bin/PAPERS/paper2003a.pdf).

Hammond et al., *Experimental and numerical study of error fields in the CNT stellarator*, Plasma Physics and Controlled Fusion 58, 074002 (2016), arXiv:1602.04867v2, §§2–5: measured and ideal-geometry predictions disagreed in the 78° configuration; metrology and inferred coil offsets improved agreement. This motivates keeping measured geometry and field validation separate from nominal certificates. [Versioned full text](https://arxiv.org/html/1602.04867v2).

Both full-text sources were retrieved on 12 October 2026. Neither supplies a completed hardware qualification dataset for our proposed demonstrator. No theorem from either paper has been imported as a Lean assumption. The reusable results above have complete elementary proofs using pinned Mathlib v4.34.1.

## Work packages and progress

| ID | Work package | Acceptance evidence |
| --- | --- | --- |
| VD1 | Freeze a nonaxisymmetric reference candidate | Four coil centres, oriented frames, radii, turns/current conventions, leads, source version and exact coefficient interpretation |
| VD2 | Certify continuous geometry and fields | Full-domain bounds, actual spatial derivatives, source-free Maxwell identities and geometry-specific clearance |
| VD3 | Model finite conductors | Embedded winding packs, closed current distribution, finite-width field error, self-field and load estimates |
| VD4 | Establish the declared confinement property | Invariant separating surface or finite-time orbit bundle, initial set, existence interval and model/reduction errors |
| VD5 | Qualify physical operation | Conductor and insulation data; current, voltage, duty cycle, cooling, supports, stored energy, protection and metrology envelopes |

## Construction release boundary

No component purchase or energization specification follows from these proofs. Plasma species, pressure/density/temperature profiles, heating and exhaust are outside the selected vacuum-field stage. A later electron-beam or plasma experiment will need its own explicit operating and safety model.

Before a physical release, the same decoded candidate must carry the finite-conductor, electrical/thermal/mechanical and measurement certificates. Current, field range, conductor gauge, supply voltage, pulse duration and cooling remain unspecified for our device. A plausible historical machine value is not a substitute for those missing requirements.

The immediate proof target is the source-free divergence/curl identity for closed C¹ filaments. The immediate device-data target is a versioned four-coil placement/current dataset. Neither is supplied by the new derivative or probe-direction theorem. See the [model contracts](../formalization/00-model-contracts.md) and [evidence gates](../formalization/08-roadmap.md) for the stronger claims still required.
