# One radian forward and a signed field-line trace from a common birth

At section zero of the Dommaschk QA2R vacuum field, fix launch radius $u=0.470$ on the certified nested Q-16 surfaces and any birth phase $|\varphi|\le2^{-19}$. A physical field line starting at the transferred section state follows 64 consecutive forward references to **one geometric radian**. The signed theorem follows one solution from the same birth for 64 slabs on either side of zero, throughout **$[-1,1]$ radians**. It also gives the endpoint ellipsoid on each side. Both theorems bound the Euclidean position error in dimensionless $(R,z)$ coordinates, including the joins. [Forward verifier](../../scripts/dommaschk_kam/verify_physical_trace_prefix.py) · [Signed trajectory theorem](../../PlasmaLean/Design/DommaschkBackwardPairedPrefix.lean)

| Interval | Verified slabs | Maximum distance from the applicable reference |
| --- | --- | --- |
| $[0,1]$ | 64 forward | $2617428504681487741/2^{80}<2.166\times10^{-6}$ |
| $[-3/4,3/4]$ | 48 backward and 48 forward | $2291404284220660349/2^{80}<1.896\times10^{-6}$ |
| $[-1,1]$ | 64 backward and 64 forward | $2617428504681487742/2^{80}<2.166\times10^{-6}$ |

## What the remaining rows establish

For this section and radius, every one of the 391 forward and 391 backward reference slabs now has a Lean-checked central residual certificate. These bound the defect of the reference curve in the field-line equation. Following the true solution through a slab also requires a derivative bound on the surrounding tube and a proof that the preceding exit supplies its initial state. The physical extent claimed above counts only the connected trajectory proofs. First mirror passage, radial variation of the bounce action, and thermal guiding-centre confinement remain open. [Full-trace requirements](dommaschk-full-frame-budgets.md) · [C1–C5 assessment](stellarator-conditions-and-geometric-questions.md)

On backward row 42 the forward growth allowance was slightly too large. Rechecking the existing field enclosures on eight time intervals gave the tighter backward inequality. This allowed the two prefixes to be joined at the actual state reached from each birth. [Backward panel check](../../scripts/dommaschk_kam/emit_backward_panel_rate.py) · [Paired proof generator](../../scripts/dommaschk_kam/verify_paired_physical_prefix.py)

A separate Lean theorem encloses the trial ellipsoid using a different width for each coordinate. An exact-arithmetic screen at this endpoint then checks 387 of 391 row pairs without subdivision, three with time subdivisions, and row 226 with an additional split in the vertical coordinate. These are feasibility checks for future Jacobian proofs. [Rectangle theorem](../../PlasmaLean/Design/DommaschkProjectedTrial.lean) · [Exact signed-pair screen](../../scripts/dommaschk_kam/results/bounce_projected_jacobian_q0_u470_pair.json)

## Reproduce the phase

Use the workstation Python environment in the repository root and the [earlier build instructions](dommaschk-signed-four-slab-trace.md). Build `PlasmaLean.Design.DommaschkBackwardPairedPrefix`, `PlasmaLean.Design.DommaschkProjectedTrial`, `PlasmaLean.Design.DommaschkJacobianForward042`, and harmonic blocks 00 through 07. The forward prefixes use ordinary Jacobian certificates on rows 2–15, shared-power certificates on rows 16–41 and 43–63, and the tracked eight-panel proof on row 42. The forward reference certificates on rows 2–63 are prerequisites.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_trace_prefix.py --length 64 --shared-from 16 --output /tmp/q0r470-forward64.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_backward_physical_prefix.py --length 64 --output /tmp/q0r470-backward64.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_paired_physical_prefix.py --forward /tmp/q0r470-forward64.json --backward /tmp/q0r470-backward64.json
.venv-ws/bin/python scripts/dommaschk_kam/screen_projected_jacobians.py --reflected --check scripts/dommaschk_kam/results/bounce_projected_jacobian_q0_u470_pair.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-71 |
| Title | One radian forward and a signed field-line trace from a common birth |
| Kind | Physical field-line certificate |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-61–N-68, N-70 |
| Dependency requirement | Match the field, clock, section state, physical tube and exit at every join. |
| Produces | A 64-slab forward theorem, a 128-slab signed theorem and a reusable coordinate-wise tube enclosure. |
| Difficulty | Validating derivative bounds on the remaining tubes and identifying the physical mirrors along the connected path. |
| Status | Compiled Lean theorems at the stated durations. The projected-row feasibility results are external exact arithmetic. |
| Lean evidence | On-demand `DommaschkPhysicalPrefix064.exists_nested_prefix`, `DommaschkPhysicalPrefix064.uniform_tube_error`, `DommaschkPairedPrefix064.exists_nested_paired`, `DommaschkPairedPrefix064.uniform_paired_error`, and `DommaschkProjectedTrial.trial_membership`. |
| Audit evidence | Four forward and two paired declarations passed the standard-axiom audit. Prefix keys `761f07b15d0d` and `ba73b8f944e8`. |
| Last updated | 24 November 2026 |
