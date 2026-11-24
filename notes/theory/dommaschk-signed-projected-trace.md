# One physical trajectory on both sides of a Dommaschk birth

For every section-zero Q-16 birth at radius $u=0.470$ and phase $|φ|≤2^{-19}$, Lean proves existence of a single signed-angle field line through the transferred state over $[-9/8,9/8]$ radians. It stays within $2676379663306118010 / 2^{80}<2.214×10^{-6}$ of the corresponding reference in dimensionless Euclidean $(R,z)$ coordinates on all 72 slabs in each direction. The ODE holds across the joins and at the common section. [Signed passage theorem generator](../../scripts/dommaschk_kam/verify_paired_physical_prefix.py)

The backward proof reflects the vertical coordinate of the backward trajectory into the forward Taylor model. Separate radial and vertical inequalities for the two rows of the moving frame place its entire trial ellipsoid inside the rectangle used to prove the Jacobian bound. This reuses the forward rectangle whenever the spatial bound satisfies the backward rate budget. Row 68 requires an additional backward rate proof using eight time panels. Rows 69–71 share the same three rectangles in both directions. The first 62 generated backward row keys agree with the earlier 64-slab run. [Reflection lemma](../../PlasmaLean/Design/DommaschkReflectedProjectedTrial.lean) · [Forward rectangles](dommaschk-projected-physical-trace.md)

## Reproduce

Prepare the dependencies and spatial certificates in N-71 and N-74. Run these commands from the repository root. Each output records its upstream proof keys and the axioms used by the assembled trajectory.

```sh
lake build PlasmaLean.Design.DommaschkReflectedProjectedTrial
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_trace_prefix.py --length 72 --shared-from 16 --square-panels 68 --projected 69 70 71 --output /tmp/forward72.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_backward_physical_prefix.py --length 72 --shared-from 16 --square-panels 68 --projected 69 70 71 --output /tmp/backward72.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_paired_physical_prefix.py --forward /tmp/forward72.json --backward /tmp/backward72.json --output /tmp/paired72.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-75 |
| Kind | Physical field-line certificate |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-71, N-74 |
| Dependency requirement | The two continuous passages share the transferred birth state. Each signed trial fits the authenticated Jacobian domain at its own rate. |
| Produces | A connected field line across 144 physical slabs with a uniform position-error bound. |
| Difficulty | Mirror contact requires reaching the archived bracket and verifying field-strength signs along the physical solution. |
| Status | Compiled and audited for the specified birth family. Thermal operating scales remain open. |
| Lean evidence | On-demand `DommaschkPairedPrefix072.exists_nested_paired` and `DommaschkPairedPrefix072.uniform_paired_error`. |
| Audit evidence | Paired key `c40a5a4cfeef`, forward `5b2044da4579`, backward `7f840403b2db`. The two paired declarations use `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 24 November 2026 |
