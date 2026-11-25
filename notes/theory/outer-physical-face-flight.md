# Flight time and action response on the completed outer radial face

On the original nested embedded QA2R tori, every admitted birth at \(u=239/500\) and \(|\phi|\le2^{-19}\) has a single true field line on which the following hold for **all** archived heights \(h_L\le h\le h_U\). Its first well around the actual birth has two mirrors. The action between them equals the fixed-window clipped action \(J(h)\), and the ordinary derivative \(J'(h)\) exists and equals the normalized one-way Cartesian flight time \(T(h)>0\). The time integral uses the norm of the derivative of the physical Cartesian space curve. The signed field line and both mirrors are already verified on this face. [Physical theorem](../../PlasmaLean/Design/DommaschkOuterFaceFlight.lean) · [Original outer-face branch](secondary-first-mirror-height-band.md)

Over \(h_U-10^{-5}\le h\le h_U\), the quantitative upper bound is \(T(h)<452\). It yields
\[
 |J(h)-J(h_U)|\le452(h_U-h),\qquad
 J(h)>J_*+19/10000-452(h_U-h).
\]
For example, throughout the last \(2\times10^{-6}\) of the interval the outer-face action exceeds \(J_*+0.000996\). Throughout the last \(4\times10^{-6}\) it still exceeds \(J_*+0.000092\). These bounds need neither the long four-tile interpolation trajectories nor a new quadrature at each height. [Original upper-height quadrature and birth identification](physical-face-action-exit.md)

On each signed half, the speed denominator is bounded using the separation from the lower height before its first contact. On the collar, the squared field increases outward at rate greater than \(1/400\), with mirror times in \((317/64,327/64)\). Integrating the inverse square-root singularity and the core ceiling gives less than 226 time units per half. The fixed-window derivative theorem then turns the total time bound into an action bound. The times and heights here are normalized. [Branch integral inequality](../../PlasmaLean/Theory/Kinetic/MirrorBranchTimeUpper.lean)

## Verification

```sh
lake build PlasmaLean.Design.DommaschkOuterFaceFlight
.venv-ws/bin/python scripts/dommaschk_kam/verify_outer_face_flight.py \
  --faces /tmp/plasma-n199-measured.json --output /tmp/plasma-n202-outer-flight.json
```

The common-torus theorem `DommaschkOuterFaceFlightOn391_328_48_16_48_16_8_5.from_nested_tori` has key `c5cbf2b552dd27ba47bf8a82c059efc5b0a761d3a7f4ece7290106bf001014d6`. Both generated declarations use only the three standard axioms.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-202 |
| Kind | Physical first-well action derivative and flight-time bound on the outer face |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-122, N-162, N-188, N-199 and the two transverse mirror branches on the outer face |
| Dependency requirement | Original true endpoint ODEs, first-well actions and the signed outer collar slopes. |
| Produces | A full-band derivative identity and an explicit uniform near-upper action margin without a new trajectory solve. |
| Status | Unconditional on the original outer launch face for the stated height intervals. |
| Lean evidence | `DommaschkOuterFaceFlight.response`, `.top_lipschitz`, `.of_outer_witness` and the generated `.from_nested_tori`. |
| Last updated | 25 November 2026 |
