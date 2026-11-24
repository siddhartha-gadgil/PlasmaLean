# Two consecutive physical field-line slabs from a Q-16 birth

| Field | Value |
| --- | --- |
| ID | N-67 |
| Kind | Physical theorem for the true Dommaschk QA2R field |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-61 through N-66 |
| Dependency requirement | The first physical exit must satisfy the second entry, with the actual centre, nonidentity frame and radius at the join. |
| Produces | One physical solution on [0,1/32] with pointwise Euclidean position error below 1.232 × 10⁻⁶. |
| Difficulty | Extending the same checked physical comparisons through the long trace and to the radial derivatives of the action. |
| Status | Both adjacent physical steps and their composition from a Q-16 birth passed Lean. |
| Lean evidence | `DommaschkMirrorLaunch.exists_nested_two_slabs`, `two_tube_error`, `DommaschkPhysicalSecondStep.physical_second_step` |
| Audit evidence | Heavy audit passed on 94,013 project declarations with standard axioms. |
| Last updated | 24 November 2026 |
| Patched by | N-68 extends the forward physical trajectory to 16 slabs and proves a two-sided first passage. |
| Patches | N-65 and N-66, unconditional physical duration at one radius |

## Physical statement

For one nested pair of Q-16 invariant tori, take any birth at radial interpolation parameter $u=0.470$ and angular phase $|φ|≤2^{-19}$. Its approach to phase zero reaches the actual start of a forward field-line solution through $1/32$ geometric radian. The solution satisfies the ODE throughout the closed interval, including $t=1/64$, where the reference and frame change. Its final state lies in the second recorded exit ellipsoid. On both slabs the Euclidean error relative to the applicable polynomial is **at most $1.232×10^{-6}$** in dimensionless radius and height. The piecewise reference takes the first polynomial at the join. [Two-slab solution and error theorem](../../PlasmaLean/Design/DommaschkMirrorTwoSlabs.lean)

| Forward interval | Exact outgoing radius in units of 2⁻⁸⁰ | Physical proof |
| --- | ---: | --- |
| [0, 1/64] | 1,481,700,234,749,866,732 | [First moving tube](../../PlasmaLean/Design/DommaschkPhysicalFirstStep.lean) |
| [1/64, 2/64] | 1,488,403,201,111,526,573 | [Second moving tube](../../PlasmaLean/Design/DommaschkPhysicalSecondStep.lean) |

The second step checks a central moving-frame defect against $7515353228031/2^{80}$. Its one-sided Jacobian bound on the physical trial ball is $80889/4000000=0.02022225$, below the archived allowance. The field denominator stays positive on that same tube. A reusable theorem now assembles a row from the identities for its position and velocity, regularity on the ball, a logarithmic norm bound and a pullback defect. [Second reference defect](../../PlasmaLean/Design/DommaschkTraceResidualForward001.lean) · [Second Jacobian](../../PlasmaLean/Design/DommaschkJacobianForward001.lean) · [Physical row assembly](../../PlasmaLean/Design/DommaschkPhysicalTraceStep.lean)

## Scaling beyond the join

A six-worker pilot independently kernel-checked the reference defects of 17 directed slabs, including the first eight in either direction and backward slab 283. Every theorem passed the standard-axiom check. The pilot took 10 minutes 6 seconds, peaked at 4.3 GiB across its worker group, and used no swap. Rechecking its saved artifact hashes took 4.59 seconds. A second six-worker batch passed all 16 additional directed slabs at indices 8–15, giving 33 audited cache entries across the two batches. Its peak was 4.4 GiB, with no swap use. These timings cover the central defect, which is one prerequisite for a physical row. [Resumable kernel checker](../../scripts/dommaschk_kam/verify_sparse_reference_slabs.py)

The eight-endpoint long-trace length is 391/64 radians in each direction in external arithmetic. A Lean proof of the quantitative physical trajectory at u=0.470 currently reaches 2/64 forward from the common section. A longer chain must discharge the physical estimates at all intermediate steps. Thermal time, birth fractions, and the radial derivative of the action remain open. [Long-trace criterion and exact screens](dommaschk-full-frame-budgets.md)
