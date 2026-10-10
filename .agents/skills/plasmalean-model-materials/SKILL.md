---
name: plasmalean-model-materials
description: Build mathematical models and verified engineering constraints for PlasmaLean components. Use for superconducting coils, tape strain, quench, thermal transport, mechanical support, plasma-facing materials, neutron damage, shielding, tritium, cooling, fatigue, or maintenance constraints.
---

# Model materials and component constraints

Read `notes/formalization/07-materials-and-engineering.md`, `06-coils-and-design.md`, and the relevant literature entries. Keep coil, coolant, wall, blanket, and plasma domains distinct and couple them through explicit interface data.

## Source the constitutive data

Identify material composition, grade, processing, irradiation history, temperature, field orientation, strain, cycle history, and experiment. Record units, source/version, measurement/fit uncertainty, and interpolation domain. Use an explicit law bundle containing conservative envelopes for conductivity, heat capacity, elastic response, critical current, allowable stress/strain, fatigue, erosion, and irradiation degradation as needed.

Pass these laws as hypotheses. Prove consistent toy instances and zero-load limits. Do not assign universal properties to “tungsten”, “steel”, or “REBCO”; do not extrapolate a fit beyond its supported envelope. Keep statistical confidence statements distinct from deterministic interval hypotheses.

## Choose a model appropriate to the question

- Use a slab or thermal network for an initial heat-margin theorem; then a PDE with interface resistance and cooling boundaries.
- Use a supported elastic beam or small-strain elastic body for an initial stress bound; introduce plasticity, anisotropy, contact, fracture, and fatigue only with explicit laws.
- Use a ribbon/material frame for REBCO tape strain. Include hard-way bending, torsion, winding-pack offsets, and critical-current dependence on field direction.
- Use a coupled electric/thermal model for quench and dump-energy bounds; distinguish ideal filament fields from finite conductor self-field and force.
- Use transport and inventory equations with sourced nuclear data for shielding, breeding, activation, and damage. Treat Monte Carlo means/error bars as estimates until a statistical theorem or deterministic enclosure supplies the needed statement.
- Use a declared erosion and fatigue model for service life; carry its applicability and uncertainty into the conclusion.

Read the exact equations and first theorem targets in the topic note before implementing them.

## Turn a limit into a theorem

Define the operating/load set and the component state. Prove a bound holding everywhere in the relevant component and throughout the specified operating interval. Compare upper load bounds against lower allowable-property bounds. Include geometric tolerances and degradation. Produce a positive margin where possible, rather than a sampled pass/fail plot.

Prove unit consistency, nonnegative dissipation, zero-source behavior, material-frame invariance, and monotonicity in a simplified case. Validate source interpolation through explicit enclosure lemmas. Formalize reference properties of the model rather than tests that merely duplicate an implementation.

## Integrate with the design

Connect certified plasma/particle heat and neutron sources to thermal bounds, thermal and electromagnetic loads to stress/strain, strain and field to magnet margin, and degradation to lifetime. State exactly which couplings are proved and which remain supplied envelopes. Deliver declarations, data provenance, margins, model-validity conditions, and the next higher-fidelity target.
