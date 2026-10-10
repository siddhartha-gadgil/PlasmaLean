---
name: plasmalean-design-stellarator
description: Advance a PlasmaLean stellarator candidate from a mathematical specification toward a constructible design with composed proof certificates. Use for coil or boundary optimization, design tradeoffs, operating envelopes, tolerance studies, or deciding which verified milestone a candidate has reached.
---

# Design against explicit contracts

Read `notes/formalization/00-model-contracts.md`, `06-coils-and-design.md`, `07-materials-and-engineering.md`, and `08-roadmap.md`. Inspect the actual implemented certificates before describing a capability as available.

## Freeze a design specification

Record the intended machine class, plasma species, major/minor scale, pressure/density/temperature profiles, magnetic-field range, heating and exhaust, duty cycle, perturbation class, manufacturing tolerances, and component data. Source numerical requirements from a named experiment, reactor study, or material characterization. Use a symbolic envelope until such data exist; do not inherit the illustrative distances in `notes/Stellerator.md` as universal limits.

Record fixed/free plasma boundary, conducting/resistive wall, coil-current model, finite conductor geometry, maintenance access, and shielding/blanket budget. Treat transport and stability targets separately. Permit quasi-isodynamic/omnigenous designs as well as quasisymmetric designs.

## Explore, then certify

1. Choose the next achievable gate in `08-roadmap.md`.
2. Parameterize axis, surfaces, coils, currents, tape orientation, and operating profiles with explicit units and symmetry conventions.
3. Use theory to reduce the search space and derive sufficient conditions. Use SIMSOPT, DESC, VMEC, SPEC, or another documented solver as a candidate generator appropriate to the model.
4. Check implementation/version-specific conventions. Keep nested-surface and island/stepped-pressure models distinct; supply the finite-pressure plasma-current field when mapping coils to equilibrium.
5. Optimize physically meaningful objectives and retain hard constraints separately. An objective penalty or its optimum is not a proof of feasibility.
6. Generate and check the exact geometric, equilibrium, stability, orbit, thermal, stress, magnet, and lifetime certificates needed at the selected gate.
7. Propagate manufacturing and operating uncertainty through margins. Recompute dependent certificates after any geometry, profile, data, or model change.

Do not require a proof of global optimality to certify one useful feasible design. Claim an optimum only with a separate optimality certificate.

## Compose results without changing quantifiers

Ensure all certificates refer to the same decoded geometry, fields, profiles, material state, operating interval, and uncertainty parameters. Preserve correlations between inputs. Compose implications only when one theorem's conclusion supplies the next theorem's hypotheses in the correct norm.

Distinguish `∀ parameter, ∃ nearby equilibrium` from one state valid for every parameter. Distinguish fixed-boundary linear stability from free-boundary stability and from nonlinear or kinetic claims. Use a design record containing the exact predicates proved and their evidence rather than a single ambiguous `Stable` flag.

## Deliver a usable milestone

Provide the candidate coefficients and provenance, compiled declaration names, quantitative margins, remaining physical-law assumptions, missing certificates, model-validity evidence, and the next experiment or theoretical target. For a reactor-scale design also account for blanket/tritium, neutron damage, cryogenics, quench, power balance, and maintenance. Name the achieved gate accurately; a vacuum-field demonstration is a useful first gate.
