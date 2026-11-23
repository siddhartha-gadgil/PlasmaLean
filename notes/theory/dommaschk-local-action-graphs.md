# Two separated fixed-action curves on each of two Dommaschk phase sectors

## Metadata

| Field | Value |
| --- | --- |
| ID | N-60 |
| Kind | Candidate computation and reusable theorem for N-54, N-57 and N-58 |
| Addresses | Q-1, Q-35, G-6, G-10 |
| Depends on | N-52, N-54, N-56–N-59 |
| Dependency requirement | A common field, launch family, pair of heights and target action. Simple mirrors and a transverse secant bound must hold throughout each root bracket. |
| Produces | A continuous, bracket-unique root at each height on each of two local sectors, with a common strict lower bound on their radial separation. |
| Difficulty | Local curve arcs are externally checked. Continuing the same two levels through all intervening angles remains research. |
| Status | Abstract action comparison, continuity and graph theorems verified in the default Lean library. Candidate arithmetic and its application to the roots checked externally. |
| Lean evidence | `MirrorHeightAction.action_gap_ge_of_core`, `strictMonoOn_action_of_trace_order`, `continuousOn_action_family`, `LocalLevelGraphs.separated_graphs_of_local_secants`. |
| Audit evidence | The two-sided root tests use 16 radial tiles and eight endpoints. The assembler rechecks section, heights, radial coverage, outward slopes, action separation and derivative bounds. |
| Last updated | 23 November 2026 |

## Local result

Let $j_*=1.3599221876644974$, $h_1=1.0595923312168822$ and $h_2=1.0601092782791866$. At each launch phase within $1/4096$ geometric radians of the specified centre, the single-passage action of the well containing the launch equals $j_*$ at exactly one radius in each indicated bracket. These radii depend continuously on phase. The root at the higher height is inward of the other by **more than $9/200=0.045$** in the interpolation coordinate $u$. The uniqueness assertion is local to each bracket. [Endpoint records and combined verification](../../scripts/dommaschk_kam/results/bounce_local_graphs_20261123.json)

| Phase centre | Radius at $h_2$ | Radius at $h_1$ | Minimum signed endpoint margin in action | Uniform secant lower bounds at $h_2$, $h_1$ |
| --- | --- | --- | ---: | --- |
| $0$ | $(0.470,0.478)$ | $(0.523,0.531)$ | $>0.00151$ | 0.05089, 0.05075 |
| $\pi/2$ | $(0.456,0.464)$ | $(0.509,0.517)$ | $>0.00198$ | 0.02852, 0.02835 |

All four brackets use the same rational field, the same interpolation between the C and A launch profiles, their Q-16 errors, and the same $j_*$. Each consists of four closed radial tiles of width $1/500$ with exactly shared endpoints. The two angular sectors together occupy $1/1024$ radians of the period $\pi$. N-59 covers a larger angular set for the two outermost face inequalities. A winding curve requires connected continuation around the circle. [Phase-zero radial tubes](../../scripts/dommaschk_kam/results/bounce_radial_arcs_20261123.json) · [Opposite-sector radial tubes](../../scripts/dommaschk_kam/results/bounce_radial_arcs_opposite_20261123.json) · [N-59](dommaschk-phase-faces.md)

## Why the action increases across these brackets

Use a common trace coordinate $t$ measured from the fixed angular section, absolute arclength density $A=ds/dt>0$ in the increasing direction, and field strength $B$. At fixed launch phase the derivative with respect to $u$ follows the field-line variational equation. Its initial value before transfer is the difference between the two launch profiles. Bounds on the short transfer account for the change of tangent before the long trace. On the full trace $|t|\le6.1$, the interval checker gives $(B^2)_u<0$ and $(A^2)_u>0$. It verifies a fully accessible central interval $|t|\le1$, strictly forbidden endpoints, and positive outward slope of $B^2$ wherever it meets the entire height band. Hence there are two simple mirrors and the clipped action on the fixed trace coincides with the action of the launch well. [Radial trajectory and tangent enclosure](../../scripts/dommaschk_kam/bounce_radial_tube.py)

The integrand is $\sqrt{\max(2A^2(h-B),0)}$. It increases weakly across radii everywhere and strictly on the accessible core. If $P=2A^2(h-B)$ and the increase $P_2-P_1$ on a core of length $\ell$ is at least $k$ with $0\le P_1\le P_2\le M^2$, rationalizing the square roots gives an action increase at least $\ell k/(2M)$. This avoids dividing by the parallel speed near a mirror. The quantitative bound on each radial tile extends over the whole bracket by splitting a secant at the tile boundaries and summing. The endpoint signs then give existence, strict radial growth gives uniqueness, and compactness of the radius bracket gives continuity in phase. [Action comparison](../../PlasmaLean/Theory/Kinetic/MirrorActionComparison.lean) · [Local graph and residual bounds](../../PlasmaLean/Theory/Geometry/LocalLevelGraphs.lean)

## Verification and remaining application

At full-period resolution the separate floating-point survey sampled 17 radii and 256 phase intervals. Its positive signs and the positions of its roots selected the test intervals. The reported bounds in the table come from directed arithmetic on whole cells. Replaying the stored certificates checks the actual indices, endpoints, margins, minimum slopes and both trace directions. The input field and seed files are hash-identified. Independent reruns of all four phase-zero endpoints and of one opposite-section trajectory reproduced the stored integer bounds. The combined checker rejected a missing endpoint, a corrupted action margin, a mismatched section and a missing tangent tile. [Floating-point survey](../../scripts/dommaschk_kam/results/bounce_radial_variation_20261123.json) · [Combined checker](../../scripts/dommaschk_kam/bounce_local_graph.py)

```sh
env OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_local_graph.py --check-record scripts/dommaschk_kam/results/bounce_local_graphs_20261123.json
```

**Scoped audit.** The general graph uses the same action target at both heights. The radius is the launch interpolation fraction, the height is $E/\mu$, and the action is integrated once between the mirrors. Smooth dependence of the physical trajectory on initial conditions and the radial variational equation connect the external tangent calculation to the analytic action. The candidate trajectory, quadrature data and their identification with the Lean hypotheses remain external. The default build passed its standard-axiom audit for 53,665 declarations. The separately loaded heavy modules passed their 60,332-declaration audit.

The next geometric step is an overlapping chain of root brackets in phase. A common uniqueness bracket or an explicit equality on overlaps must identify the two local roots where neighbouring certificates meet, including at the period seam. Exploiting the slow motion of the measured roots in a phase-dependent radial bracket is preferable to validating the whole strip at every phase. A physical orbit claim further requires the reduced dynamics or a finite-time action drift bound, comparison to the physical radial observable, physical time and birth measure. Operating targets remain open. [Physical band criterion](hamiltonian-bounce-band-test.md)
