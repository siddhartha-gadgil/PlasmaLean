# A three-eighths-radian field-line trace and a four-slab signed passage

| Field | Value |
| --- | --- |
| ID | N-70 |
| Kind | Physical field-line certificate |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-64–N-68 |
| Dependency requirement | The reference defects, spatial Jacobian bounds, inherited ellipsoids and physical clocks must match at each join. |
| Produces | A 24-slab forward proof and a four-slab signed proof from the same launch family. |
| Difficulty | Extending the physical inequalities to every slab up to both mirrors, then controlling action and radial variation. |
| Status | Kernel-checked forward milestones through 24 and 32 slabs and the signed four-slab passage. The all-radius projection screen uses external exact arithmetic. |
| Lean evidence | On-demand `DommaschkMirrorLaunch.exists_nested_four_slabs`, `DommaschkPhysicalPrefix024.exists_nested_prefix`, `DommaschkPhysicalPrefix032.exists_nested_prefix`, `DommaschkPhysicalPrefix032.uniform_tube_error`, and `PositionFrameProjection.coordinates_le`. |
| Audit evidence | Standard axioms for the signed passage, physical backward step, projection theorem and four generated prefix theorems. Forward prefix keys `546a6c4056fe` (24 slabs) and `c17a99c688e5` (32 slabs). |
| Last updated | 24 November 2026 |

## Certified intervals

Fix the same nested Q-16 surfaces and a birth at $u=0.470$ with $|\varphi|\le 2^{-19}$ about section zero. From its transferred section state there is a physical field-line solution through 24 adjacent forward slabs, or $3/8$ geometric radian. The Euclidean error in dimensionless $(R,z)$ is bounded by $1755239024901380218/2^{80}<1.452\times10^{-6}$ throughout. The generated theorem also controls the last exit ellipsoid. [Forward proof generator](../../scripts/dommaschk_kam/verify_physical_trace_prefix.py)

Under the same birth hypotheses a single physical field line follows two backward and two forward reference slabs on $[-1/32,1/32]$. Its error is at most $1.232\times10^{-6}$, including at all three joins. The backward and forward paths agree at the state reached from this birth. The signed-clock lemma proves the ODE there as well. These intervals measure toroidal angle. Thermal guiding-centre drift and physical time remain open. [Four-slab theorem](../../PlasmaLean/Design/DommaschkMirrorTwoSided.lean) · [Two backward steps](../../PlasmaLean/Design/DommaschkMirrorTwoBackwardSlabs.lean)

## Half-radian extension

At the same radius and on the same birth sector, the 32-slab theorem gives one physical field-line solution on $[0,1/2]$ with dimensionless Euclidean error at most $1960457298773104133/2^{80}<1.622\times10^{-6}$. The four generated theorems passed the standard-axiom audit. The longer proof uses the same replay procedure below. Build `PlasmaLean.Design.DommaschkHarmonicBlock03`, extend the reference and shared-power Jacobian ranges to row 31, and run `.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_trace_prefix.py --length 32 --shared-from 16`.

## Reusing the spatial bound under reflection

The second backward step uses the field reflection and its own reference defect, trial radius and growth allowance. A bound on the row lengths of the endpoint frames places the entire interpolated backward trial ellipsoid inside the forward Jacobian's coordinate box. This permits reuse of the forward spatial certificate. At all four section-zero radii the exact external projection test passes on all 391 row pairs, or 1,564 in total. The physical theorem uses the checked inequalities for the second backward step. [Projection theorem](../../PlasmaLean/Certificates/PositionFrameProjection.lean) · [Backward step](../../PlasmaLean/Design/DommaschkPhysicalBackwardSecondStep.lean) · [Exact projection report](../../scripts/dommaschk_kam/results/bounce_frame_projections.json)

## Reproduce the proofs

Start in the repository root with the workstation Python environment installed. The forward verifier uses ordinary Jacobian certificates through row 15 and shared-power certificates from row 16. Both verify the generated Lean declarations and check their axiom dependencies. [Earlier forward proof](dommaschk-quarter-radian-trace.md)

```sh
lake build PlasmaLean.Design.DommaschkMirrorTwoSided PlasmaLean.Design.DommaschkStoredPowers PlasmaLean.Design.DommaschkHarmonicBlock00 PlasmaLean.Design.DommaschkHarmonicBlock01 PlasmaLean.Design.DommaschkHarmonicBlock02
.venv-ws/bin/python scripts/dommaschk_kam/screen_reflected_frame_projections.py --check scripts/dommaschk_kam/results/bounce_frame_projections.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_sparse_reference_slabs.py --direction 1 --range 2 23 --workers 4
.venv-ws/bin/python scripts/dommaschk_kam/verify_sparse_forward_jacobians.py --range 2 15 --workers 4
.venv-ws/bin/python scripts/dommaschk_kam/verify_shared_forward_jacobians.py --range 16 23 --workers 4
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_trace_prefix.py --length 24 --shared-from 16
```
