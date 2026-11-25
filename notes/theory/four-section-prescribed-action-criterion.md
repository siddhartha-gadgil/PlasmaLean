# Four section checks suffice for an original birth at the prescribed action

Take the original QA2R candidate, the two nested embedded invariant tori in the verified endpoint comparison, and the upper mirror height $h=5300546391395933/5000000000000000$. Set $b=331/64$. The following finite set of proof obligations suffices for every allowed original birth phase $|\phi|\le2^{-19}$.

For each of the four section balls in N-169, prove that every point $x$ in the ball has a signed solution $y$ to the original angle ODE through $y(0)=x$. Require the usual regular spatial box through $[-b,b]$, low field at zero, high field at both caps, and nonzero time derivative at each end of any first well at height $h$. Each choice of $x$ can use its own solution.

**Conclusion.** For every such $\phi$, there exist a strictly interior $0.470<u<0.478$, a signed solution through the original torus interpolation at $\phi$, and its first accessible well $[l,r]$. The two mirrors are transverse. The physical arclength action over that same well equals $6799610938322487/5000000000000000$ exactly. Both tori are chosen before $\phi$. [Section theorem](../../PlasmaLean/Design/DommaschkRadialSectionAction.lean)

## Recovering the birth from a section crossing

The short physical approach in N-169 ends in an explicit Euclidean ball at the zero section. The identity frame identifies that ball with the initial state set of the signed ODE solver. Terminal-value uniqueness for the original ODE identifies the backwards portion of the selected solution through the section with the short approach. In particular it recovers the true torus interpolation at the original angle, including zero. The same solution retains every supplied field or arclength observable. Choosing one solution at each radius now supplies the family in N-171, where continuity follows from the physical ODE. [Birth-position uniqueness](../../PlasmaLean/Design/DommaschkPhysicalFirstMirrorValues.lean) · [Continuous radial family](radial-field-line-continuation.md)

## What has been checked

The candidate implication `DommaschkRadialSectionTargetOn391_328_48_16_48_16_8_5.from_sections` was kernel-checked against the archived physical endpoints. Its receipt is `8fe8d001db7738659c40aa10b9604cabd76e001d8ec5c1b67623720a362eeed2`. The four section obligations still require the physical through-going traces and their observed field signs. Their exact external screens cover both directions, and the first signed central residuals have passed Lean. [Entry balls and cap signs](upper-radial-ribbon-entry-and-caps.md) · [Central ODE proofs](radial-ribbon-central-defects.md)

```sh
lake build PlasmaLean.Design.DommaschkRadialSectionAction
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_section_target.py \
  --flow /tmp/plasma-n171-flow.json --output /tmp/plasma-n176-target.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-176 |
| Kind | Physical prescribed-action criterion on four section balls |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-162, N-167, N-169, N-171 |
| Dependency requirement | Through-birth uniqueness, exact endpoint action comparison and the four section entries. |
| Produces | A true torus-interpolated interior birth with transverse mirrors and exact target action, conditional only on the four universal signed section checks. |
| Status | The criterion and its actual endpoint instantiation are Lean-verified. The long section checks are running. |
| Lean evidence | `DommaschkRadialSectionAction.from_section`, `.realized_of_sections` and generated `.from_sections`. |
| Audit evidence | Each theorem uses only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
