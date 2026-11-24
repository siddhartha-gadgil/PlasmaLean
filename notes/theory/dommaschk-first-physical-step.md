# The first physical moving-frame step from a Dommaschk mirror birth

| Field | Value |
| --- | --- |
| ID | N-65 |
| Kind | Physical ODE theorem and reusable certificate interpretation |
| Addresses | Q-35, Q-1, G-6, G-10 |
| Depends on | N-61 through N-64 |
| Dependency requirement | The launch endpoint, polynomial, derivative, matrix and trial tube must be the ones used by a single physical solution. |
| Produces | An unconditional forward trajectory with Euclidean error control from a physical Q-16 birth on the first recorded slab. |
| Difficulty | Certifying the reference and spatial Jacobian consistently on each successive slab. |
| Status | First forward slab composed in Lean. Three physical reference defects checked individually. A separate exact arithmetic screen passes all 6,256 central defect budgets. |
| Lean evidence | `DommaschkMirrorLaunch.exists_nested_firstPassage`, `DommaschkPhysicalFirstStep.physical_first_step`, `DommaschkJacobian.physical_derivative`, `DommaschkJacobian.physical_clock_log_norm`, `PositionFrameSlabs.Chain.cartesian_trajectory` |
| Audit evidence | Default and heavy standard-axiom checks passed for 54,471 and 93,099 project declarations, respectively. |
| Last updated | 24 November 2026 |
| Patches | N-64, physical Jacobian and composition on the first forward step |

## Physical statement

There exists one nested pair of Q-16 invariant tori such that, for every birth phase $|φ|≤2^{-19}$ at launch radius $u=0.470$, the true QA2R field line reaches phase zero. From that same section state a forward field-line solution exists over every geometric angle $0≤t≤1/64$. Its Euclidean distance in the dimensionless $(R,z)$ plane from the recorded polynomial at $t$ is at most $1.23×10^{-6}$. Its terminal state belongs to the recorded incoming set for the next row. The proof retains both pieces of trajectory and uses the actual end of the first as the initial value of the second. The approach to the section is oriented according to the side on which the birth lies. [Birth-to-step theorem](../../PlasmaLean/Design/DommaschkMirrorFirstPassage.lean)

The local theorem applies to **every** point in the exported entry ellipsoid. Its tighter distance bound throughout the closed slab is $1481700234749866732/2^{80}$, approximately $1.225634×10^{-6}$. Time is the geometric toroidal angle. No operating point or conversion into physical time is used. [Moving-tube theorem](../../PlasmaLean/Design/DommaschkPhysicalFirstStep.lean)

## How the Jacobian estimate closes

The formal radial and vertical derivatives of a sparse polynomial give its Fréchet derivative in Euclidean coordinates. Applying the quotient rule to the two velocity components gives the candidate’s actual spatial Jacobian wherever the cylindrical radius is positive and the denominator is nonzero. Along a signed clock the Jacobian includes the sign of that clock. [Physical derivative and joint continuity](../../PlasmaLean/Design/DommaschkPhysicalJacobian.lean)

On the first moving tube, bounding the symmetric matrix row by row exceeds the archived logarithmic norm. The successful calculation retains its half-trace and the two independent entries of its traceless part. Lean obtains a logarithmic norm at most $201/10000=0.0201$, below the archived $0.0211087$. Combined with the physical central defect of N-64, this gives both the pointwise distance bound and the terminal ellipsoid. The general chain theorem propagates any number of such steps if the analytic data are supplied for every row. [First Jacobian bound](../../PlasmaLean/Design/DommaschkJacobianFirstBound.lean) · [Euclidean step](../../PlasmaLean/Certificates/PositionFrameODE.lean) · [Finite chain](../../PlasmaLean/Certificates/PositionFrameChain.lean)

## Evidence beyond the first step

Two further Lean theorems bound the physical reference defect on the first backward and last forward slabs at this radius, including the actual signed clock and frame. These individual results leave the intervening physical propagations open. An independent exact arithmetic screen checks both directions at all eight endpoints. The worst of its 6,256 Euclidean defect bounds is about 77.11% of the archived allowance, at section $π/2$, radius 0.456, backward slab 380 (numbered from zero). This measures the feasibility of the remaining central defect proofs. It does not supply their Lean terms or Jacobian estimates. [Backward first defect](../../PlasmaLean/Design/DommaschkTraceResidualBack000.lean) · [Forward last defect](../../PlasmaLean/Design/DommaschkTraceResidualForward390.lean) · [Exact results](../../scripts/dommaschk_kam/results/bounce_sparse_reference_defects.json)

```sh
lake build PlasmaLean.Design.DommaschkMirrorFirstPassage
lake build PlasmaLean.Design.DommaschkTraceResidualBack000 PlasmaLean.Design.DommaschkTraceResidualForward390
.venv-ws/bin/python scripts/dommaschk_kam/emit_sparse_jacobian.py --check
.venv-ws/bin/python scripts/dommaschk_kam/emit_sparse_trace_defect_samples.py --check
```

The next target is a second successive *physical* step from the first exit ellipsoid, followed by a checked chain to the first mirror. The long trace to $391/64$, the radial derivatives of the action graphs and thermal confinement in physical units remain open. [Long-trace inputs](dommaschk-physical-frame-trace.md)
