# Both physical field-line branches at all eight Dommaschk launches

There is one pair of nested Q-16 flux tori such that every admissible birth at each of the eight action endpoints reaches its section and has a physical field line on the signed angular interval $[-1/64,1/64]$ about that section. The line has the same state at the join and satisfies the physical ODE there. For every angle on each side it lies in the original signed moving tube, and it reaches the archived exit enclosure on each side. [Shared-tori statement and proof](../../PlasmaLean/Design/DommaschkEndpointSignedTrace.lean)

| Section | Interpolation parameters between the two surfaces | Birth-sector half-width |
| --- | --- | --- |
| $0$ | 0.470, 0.478, 0.523, 0.531 | $2^{-19}$ radians |
| $\pi/2$ | 0.456, 0.464, 0.509, 0.517 | $2^{-20}$ radians |

The physical approach from the birth to its section is part of the theorem. The quantifier over the two tori lies outside the quantifier over all endpoints and birth angles. The field line can depend on the birth. The earlier central-reference bounds provide the forcing error. The new spatial Jacobian bounds allow this error and the birth uncertainty to be propagated together. [Physical launch theorem](../../PlasmaLean/Design/DommaschkEndpointFirstSlab.lean) · [Earlier reference estimates](dommaschk-eight-reference-defects.md)

Reflection reverses the sign of the vertical coordinate and the angular clock. At 0.478 and 0.531 the forward spatial rectangle also encloses the reflected backward trial. Five other launches use a common rectangle widened to include the shift between the two reference polynomials. The physical growth inequalities and central forcing are checked for each signed row. At 0.470 the proof uses the two previously verified physical first steps. A reflected trajectory also transports action bounds to the reflected seed by the equality of their strength and arclength profiles. [Shifted rectangles](../../PlasmaLean/Design/DommaschkShiftedTrial.lean) · [Backward physical bounds](../../PlasmaLean/Design/DommaschkBackwardRectangle.lean) · [Action under reflection](../../PlasmaLean/Design/DommaschkReflectedActionBounds.lean)

This supplies the first pair of actual trajectory rows for every endpoint in the quadrature archive. The remaining application requires extending each trajectory to its turning points and checking the original pointwise quadrature bounds on the intervening panels.

## Reproduce

From the repository root on the configured workstation, the following commands build the generated Lean proofs. For the backward proof, the second Jacobian report supplies the five widened rectangles.

```sh
lake build PlasmaLean.Design.DommaschkEndpointSignedTrace PlasmaLean.Design.DommaschkBackwardRectangle PlasmaLean.Design.DommaschkReflectedActionBounds PlasmaLean.Design.DommaschkOppositeHarmonic PlasmaLean.Design.DommaschkHarmonicBlock00 PlasmaLean.Design.DommaschkPhysicalFirstStep PlasmaLean.Design.DommaschkPhysicalBackwardFirstStep
py=.venv-ws/bin/python
scripts=scripts/dommaschk_kam
$py $scripts/verify_endpoint_reference_slabs.py --endpoints q0r478 q0r523 q0r531 q1r456 q1r464 q1r509 q1r517 --workers 2 --output /tmp/qa2r-ref.json
$py $scripts/verify_endpoint_forward_jacobians.py --workers 2 --output /tmp/qa2r-jac.json
$py $scripts/verify_endpoint_physical_launches.py --references /tmp/qa2r-ref.json --jacobians /tmp/qa2r-jac.json --output /tmp/qa2r-forward.json
$py $scripts/verify_endpoint_forward_jacobians.py --paired-trials --endpoints q0r523 q1r456 q1r464 q1r509 q1r517 --workers 2 --output /tmp/qa2r-paired-jac.json
$py $scripts/verify_endpoint_backward_launches.py --endpoints q0r478 q0r523 q0r531 q1r456 q1r464 q1r509 q1r517 --jacobians /tmp/qa2r-jac.json /tmp/qa2r-paired-jac.json --references /tmp/qa2r-ref.json --output /tmp/qa2r-backward.json
$py $scripts/verify_endpoint_signed_launches.py --forward /tmp/qa2r-forward.json --backward /tmp/qa2r-backward.json --output /tmp/qa2r-signed.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-91 |
| Kind | Physical trajectory and certificate composition |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-64, N-66, N-83, N-89 |
| Dependency requirement | Common nested tori, a physical section entry for every birth, and both signed first-step field bounds and frame tests. |
| Produces | One signed field line through each birth's section state and enclosures in both original tubes. |
| Difficulty | Propagating later slabs with distinct reference curves and maintaining whole-well action bounds. |
| Status | Workstation on-demand proofs compiled and axiom-checked for all eight endpoints. |
| Lean evidence | `DommaschkSignedLaunchesAll.launches`, `DommaschkEndpointSignedTrace.common_of_chains`, `DommaschkBackwardRectangle.field_bounds`. |
| Audit evidence | Signed proof key `00d2435ba6f701921afb68b8863175e6ac12e5d4ec2a672c79261395f1dea663`. Lean reports only the standard three axioms. |
| Last updated | 25 November 2026 |
