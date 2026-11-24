# Field-strength sublevel arclengths from time panels

For a positive parallel-speed threshold $v$, the set where $B≤h-v^2/2$ is exactly the set where $v≤\sqrt{2(h-B)_+}$. This gives a finite geometric certificate for its arclength. For an upper estimate, cover the region with panels and sum the upper arclength weights of every panel whose upper speed reaches $v$. For a lower estimate, sum the lower weights of disjoint measurable panels whose lower speed reaches $v$. In both sums, equality at the speed threshold counts. At $v=0$ the full panel mass still gives an upper bound. A unit-length example with $B>h$ shows why counting every clipped speed would overestimate a lower bound. [Partition theorem and counterexample](../../PlasmaLean/Theory/Kinetic/MirrorSublevelPartition.lean)

Lean applies the same argument directly to the packed Dommaschk quadrature. The field profile and arclength density must satisfy the original pointwise packet coverage inequalities. Under measurability and nonnegative integrable density, those hypotheses give the directed sublevel length in the arclength-weighted angular measure. Every original time panel has width $1/3072$ radian and the density tick is $2^{-20}$. [Packed quadrature theorem](../../PlasmaLean/Certificates/MirrorSublevelQuadrature.lean)

| Physical archive and adaptive threshold | Whole time panels | Closed-threshold density ticks | Ticks coming exactly from equality |
| --- | ---: | ---: | ---: |
| Section 0, radius 0.470, upper bound at speed $78848/2^{20}$, left edge of cell 71 | 31,200 | 28,064,234,084 | 1,865,338 |
| Section 0, radius 0.478, lower bound at speed $63488/2^{20}$, right edge of cell 63 | 31,392 | 29,173,279,094 | 1,863,002 |

Both complete archive reductions, the counts one tick higher, and the scale conversion to the two N-78 node heights were kernel-checked. The first angular interval is $[-325/64,325/64]$, and the second is $[-327/64,327/64]$. The physical assumption in each concrete theorem is the original time-panel coverage along that whole interval. The remaining adaptive thresholds require their own arithmetic connection to the archive. [Both concrete node theorems](../../PlasmaLean/Design/DommaschkSublevelArchiveNodes.lean)

## Reproduce

```sh
lake build PlasmaLean.Design.DommaschkSublevelArchiveNodes
lake env lean scripts/check_axioms_heavy.lean
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-80 |
| Kind | Measure-theoretic arclength estimate and concrete packet bindings |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-60, N-61, N-72, N-73, N-78 |
| Dependency requirement | Measurable field, nonnegative integrable arclength density, directed physical packet covers, and strictly positive threshold for the lower estimate. |
| Produces | Upper and lower bounds for arbitrary thresholds, with two complete archived node sums checked. |
| Difficulty | Discharge the physical cover over the whole trajectory and efficiently bind all grid nodes to the packed speed witnesses. |
| Status | Compiled and audited. |
| Lean evidence | `MirrorSublevelPartition.upper`, `.lower`, `.zero_lower_counterexample`; `MirrorSublevelQuadrature.covers_sublevel`; `DommaschkSublevelArchiveNodes.Upper.node` and `.Lower.node`. |
| Audit evidence | The two full archived reductions depend only on standard axioms. Strict-cutoff replacements fail against both examples. |
| Last updated | 24 November 2026 |
