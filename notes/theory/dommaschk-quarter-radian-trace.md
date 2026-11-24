# A quarter-radian physical field-line trace from a Q-16 birth

| Field | Value |
| --- | --- |
| ID | N-68 |
| Kind | Physical trajectory theorem and section-zero reflection |
| Addresses | Q-35, Q-1, G-6, G-10 |
| Depends on | N-61 through N-67 |
| Dependency requirement | Each actual section state, signed clock, accepted scalar row, central defect, spatial derivative and exit ellipsoid must match on every adjacent slab. |
| Produces | One physical forward trajectory through 16 recorded slabs and a separate two-sided trajectory across the birth section. |
| Difficulty | Closing all intervening physical rows through the first mirror, then controlling the radial derivative and the action. |
| Status | The generated 16-row forward prefix and the two-sided first slab are kernel-checked. |
| Lean evidence | `DommaschkPhysicalPrefix016.exists_nested_prefix`, `DommaschkPhysicalPrefix016.uniform_tube_error`, `DommaschkMirrorLaunch.exists_nested_bidirectional` |
| Audit evidence | Four generated prefix theorems passed the standard-axiom check. The on-demand audit including the two-sided and reflection results checked 94,889 declarations. |
| Last updated | 24 November 2026 |
| Patches | N-67, physical duration and direction |

## Physical extent

Take the nested Q-16 surfaces, launch radius $u=0.470$, and any birth with $|φ|≤2^{-19}$ geometric radian about section zero. The physical solution starting at the transferred section state follows the 16 consecutive forward reference polynomials on $0≤t≤1/4$. Its Euclidean distance in dimensionless $(R,z)$ coordinates from the applicable reference on every slab is bounded by $1623991328784261631/2^{80}<1.344×10^{-6}$. The derivative statement holds at the frame joins and the last state belongs to the sixteenth exit ellipsoid. [Generated theorem and kernel replay](../../scripts/dommaschk_kam/verify_physical_trace_prefix.py)

For the same launch conditions there is also a single signed-angle solution across $[-1/64,1/64]$. Both directions start at the same physical state reached by the birth. The derivative holds through zero and the Euclidean error stays at most $1.23×10^{-6}$. The two-sided result establishes a backward physical step as well as the forward one. [Bidirectional theorem](../../PlasmaLean/Design/DommaschkMirrorBidirectional.lean)

## Reflection and the remaining cost

The physical QA2R field is equivariant under reflection about section zero. The saved centre polynomials and frames reflect exactly on all 1,564 row pairs at its four radii. Reusing a sharper forward defect enclosure and checking each backward row against its own allowance succeeds in exact arithmetic for all of them. Sixteen backward rows at radius 0.470 have also passed this transfer in Lean. At the opposite section none of the 1,564 paired saved centre polynomials coincide exactly after reflection. [Physical identity](../../PlasmaLean/Design/DommaschkSectionReflection.lean) · [Concrete transfer](../../PlasmaLean/Design/DommaschkReflectedBack001.lean) · [All-radius comparison](../../scripts/dommaschk_kam/results/bounce_reflected_reference_defects.json)

The spatial comparison uses the larger of the two paired trial radii and the smaller Jacobian allowance. All 1,564 section-zero pairs pass the exact screen. A separate physical Jacobian proof at forward slab 42 uses eight time subintervals to establish its one-sided bound. This isolated proof supplies one input to that row; the connected trajectory must traverse every earlier row. [Reflected Jacobians](../../scripts/dommaschk_kam/results/bounce_reflected_jacobians.json) · [Slab 42 theorem](../../PlasmaLean/Design/DommaschkJacobianForward042.lean)

## Reproduce the forward prefix

The generator uses the two checked-in physical steps for rows 0 and 1. For rows 2–15 it verifies the compiled central defect and Jacobian artifacts, imports their physical step proofs and constructs the single trajectory. With the repository dependencies and workstation Python environment installed, run these commands from the repository root. Worker counts can be reduced.

```sh
lake build PlasmaLean.Design.DommaschkMirrorFramePath PlasmaLean.Design.DommaschkPhysicalSecondStep PlasmaLean.Design.DommaschkHarmonicBlock00 PlasmaLean.Design.DommaschkHarmonicBlock01
.venv-ws/bin/python scripts/dommaschk_kam/verify_sparse_reference_slabs.py --direction 1 --range 2 15 --workers 6
.venv-ws/bin/python scripts/dommaschk_kam/verify_sparse_forward_jacobians.py --range 2 15 --workers 5
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_trace_prefix.py --length 16
```

The longer target is 391/64 geometric radians in each direction at each of the eight endpoints. The remaining physical slabs, radial variation of the action, and conversion to a thermal confinement claim in seconds are open. [Long-trace criterion](dommaschk-full-frame-budgets.md)
