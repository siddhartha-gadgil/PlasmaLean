# Continuous field-line families across the upper action bracket

Let $u$ range over $[0.470,0.478]$. Fix a launch phase $|\phi|\le2^{-19}$ and form the linear interpolation of the two certified torus positions at that phase. For each $u$, choose any physical solution through its interpolated birth, with the true toroidal angle as independent variable. Let $b=331/64$, $h=h_U$ and $J_*$ be the archived target action. The following implication is proved in Lean on the same embedded tori as the absolute endpoint comparison.

Assume every chosen solution exists throughout $[-b,b]$, obeys the original QA2R angle ODE and stays in $7/8\le R\le1$, $|z|\le5/64$. Assume its field strength is below $h$ at zero and above $h$ at both caps. Then either

1. Some strictly interior radius has a first accessible well with physical arclength action exactly $J_*$.
2. At some radius a first mirror is a local maximum of the field strength along its line.

When both first contacts at every radius have nonzero angle derivative, the first conclusion follows. The field-strength and arclength data are those of the actual Cartesian field line. The proof allows the interpolating lines and previously archived endpoint lines to be chosen independently. [Physical theorems](../../PlasmaLean/Design/DommaschkRadialFamilyContinuity.lean) · [Concrete two-torus attachment](../../scripts/dommaschk_kam/templates/radial_field_line_continuation.lean.tpl)

## Why continuity follows

For a smooth autonomous vector field on a compact set containing all the solutions, choose a uniform Lipschitz constant $K$ there. Comparing two trajectories whose positions at time $c$ are $p$ and $q$ gives the two-sided bound
$$d(x(t),y(t))\le e^{K|t-c|}d(p,q).$$
The reverse-time comparison covers $t<c$. Continuous birth positions now give joint continuity in the label and time. The compact set can be nonconvex. For the QA2R application it is the Cartesian image of the closed cylindrical box through the chosen azimuths. Smoothness of the original Cartesian angle velocity there gives continuity of its norm, the arclength density. [Two-sided trajectory theorem](../../PlasmaLean/Theory/Fields/TrajectoryFamilyContinuity.lean)

For equal birth positions the distance bound gives equality on the common time window. The independent endpoint archives cover both first wells on $[-327/64,327/64]$. This suffices to transport their wells and integrals to the interpolating family even though the proposed common caps lie farther away. The original strict action inequalities at the two endpoints then give the alternative by connectedness. [Two endpoint actions](upper-height-radial-action-secant.md) · [First-well continuation](../../PlasmaLean/Theory/Kinetic/FirstWellContinuation.lean)

## Evidence and remaining work

The concrete theorem `DommaschkRadialFlowOn391_328_48_16_48_16_8_5.from_nested_tori` compiles against the authenticated endpoint-action proof `60e4464aad8a4b797c7c006fc20736f20defd348a3a39d2f5310fef75ee41d46`. Its receipt is `3e0dc892ec8288711f16918a67cecc9e581ca2c1bdc9fce1aa5aad2828289542`. The remaining field-specific obligations are signed through-going solutions over the full family and the strength and derivative signs along them. N-169 supplies the original entries and cap signs on the prescribed tubes. [Four entry balls and cap signs](upper-radial-ribbon-entry-and-caps.md)

```sh
lake build PlasmaLean.Design.DommaschkRadialFamilyContinuity PlasmaLean.Design.DommaschkRadialRibbonEntry
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_action_alternative.py \
  --through-ode --top /tmp/plasma-n162-upper-secants.json --output /tmp/plasma-n171-flow.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-171 |
| Kind | Reusable two-sided ODE theorem and application to the actual upper action bracket |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-162, N-167, N-169 |
| Dependency requirement | Original strict endpoint action inequalities at the common upper height and common torus birth data. |
| Produces | Joint continuity, uniqueness on overlap, transfer of the endpoint wells, and an original-field target-or-grazing implication. |
| Status | Lean-verified implication. The all-radius long-path and simple-contact inputs are open. |
| Lean evidence | `TrajectoryFamily.continuousOn_of_enclosed`, `DommaschkRadialFamilyContinuity.alternative_of_passages`, `.prescribed_of_regular` and generated `.from_nested_tori`. |
| Audit evidence | The generic, physical and generated declarations use only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
