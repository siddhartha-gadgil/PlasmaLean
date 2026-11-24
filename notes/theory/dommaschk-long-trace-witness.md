# A two-sided long-trace witness for the Dommaschk mirror calculation

| Field | Value |
| --- | --- |
| ID | N-62 |
| Kind | Certificate and reusable trajectory theorem |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-57, N-59, N-60, N-61 |
| Dependency requirement | The ODE, transferred initial point, frames, observable bounds and integration clock must all refer to the same trajectory. |
| Produces | A replayable pair of trajectories at one N-60 endpoint, a finite-slab gluing theorem, and physical observable identities. |
| Difficulty | Identifying the residual and spatial derivative bounds with the actual candidate on each moving tube. |
| Status | Exact external trajectory replay. Lean verifies the general gluing theorem, the moving-frame step and the physical observable identities. |
| Lean evidence | `TrajectorySlabs.Chain.exists_trajectory`, `TrajectorySlabs.MovingFrame.step_of_defect`, `DommaschkBounceField.physical_trace_tangent` |
| Audit evidence | Workstation builds and standard-axiom audits. The external checker reproduces archived action and crossing bounds and rejects corruption. |
| Patched by | N-63 extends external replay to eight endpoints. N-64 checks physical entry, the scalar chains, the harmonics and the first reference defect in Lean. |
| Last updated | 24 November 2026 |

## What the witness covers

At the N-60 launch radius $u=0.470$ in the sector centred on zero, the lossless witness contains 391 steps of width $1/64$ in each direction from the common section. Each half reaches $391/64=6.109375$ geometric radians. Earlier steps reproduce the action intervals and first-mirror crossings for that endpoint. The file carries the transferred seed, reference polynomial coefficients, both ends of the moving frames, reference jumps, error radii, and bounds for each accepted step. [Witness](../../scripts/dommaschk_kam/results/bounce_frame_q0_u470.json.gz)

**Exact external replay.** From the stored integers the checker reconstructs both traces, with the floating trajectory and frame proposers disabled. It rejects a one-unit change to the outgoing error radius at the second backward slab and a missing direction. The compressed file has SHA-256 `203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d`. [Generator and checker](../../scripts/dommaschk_kam/bounce_frame_witness.py)

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_frame_witness.py check
```

## What Lean proves

**Compiled Lean theorem.** A finite chain of closed ODE slabs produces a single solution from each admissible initial condition. The next step accepts the actual exit state of the previous step. The resulting solution stays in every recorded tube and has the required derivative on the whole time interval, including internal joins. A moving-frame step obtains this contract from a defect estimate and a one-sided Jacobian bound. Its endpoint enclosure can be rounded outward and transferred to a changed centre or frame. [Trajectory gluing](../../PlasmaLean/Theory/Fields/TrajectorySlabs.lean) · [Moving-frame step](../../PlasmaLean/Theory/Fields/MovingFrameSlabs.lean)

**Compiled Lean theorem, on demand.** At positive cylindrical radius the three sparse Dommaschk field polynomials give the squared physical field strength. Where the denominator is positive they also give the squared arclength per geometric radian. A physical field-line solution therefore has the tangent and arclength density used by the quadrature. [Physical observables](../../PlasmaLean/Design/DommaschkBounceObservables.lean)

The open application is to discharge the angular, field, defect and Jacobian enclosures on all 782 time slabs in Lean. The other seven N-60 endpoints and the radial derivatives on the sixteen tiles also need their corresponding physical enclosures. The unconditional Lean physical launch result covers 1/64 radian in either direction on both sectors. [N-61](dommaschk-mirror-certificate-replay.md)
