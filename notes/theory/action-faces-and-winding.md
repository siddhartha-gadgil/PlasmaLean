# Action bounds on two radial faces

[N-59](dommaschk-phase-faces.md) checks the two radial faces on six launch sectors.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-58 |
| Kind | Method for N-51, N-53 and N-54 |
| Addresses | Q-1, Q-35, G-6, G-10 |
| Depends on | N-51 for a corrected-invariant estimate when available, N-54 for the upward-crossing lemma |
| Dependency requirement | A continuous radial orbit and an action budget up to a possible first exit. The winding conclusion also needs a continuous periodic single-valued action for one well. |
| Produces | A finite-time radial barrier from two face extrema and, under an additional crossing condition, a continuous periodic graph. |
| Difficulty | The abstract theorems are proved. Bounding the physical orbit's action defect and the extrema around a full phase period is research. |
| Status | Geometry theorems and sanity examples compiled in the default library. Candidate application open. |
| Lean evidence | `ActionFaceBarrier.FaceBounds.stays_inside`, `stays_inside_of_corrected_action`, `PeriodicLevelGraphs.UpwardCrossings.exists_level_graph`, `separated_graphs_of_upward_crossings`. |
| Audit evidence | The three-root face example and the folded one-crossing example distinguish the two conclusions. |
| Last updated | 23 November 2026 |

## Confinement from the faces

Write $J(p,r,h)$ for an action, with phase or other launch parameters $p$, radius $r$ between $a$ and $b$, and mirror height $h$ in $[h_1,h_2]$. Suppose the action is nondecreasing in height on each radial face. Assume the following bounds hold uniformly in $p$.

$$
   J(p,a,h_2)\le L,\qquad U\le J(p,b,h_1).
$$

Let a path start at an interior radius with action $j_0$. Suppose that up to each possible first radial exit the height stays in the window and the action changes by at most $d$. **If $L+d<j_0<U-d$, the radius stays strictly between $a$ and $b$ for the whole time interval.** At a first hit its action would either be at most $L$ or at least $U$. The radius must be continuous. Its phase can live in an arbitrary space. The theorem applies to an existing path, so the physical application must establish existence through the proposed horizon. [First-exit proof](../../PlasmaLean/Theory/Geometry/ActionFaceBarrier.lean)

If the trajectory satisfies $(J+\varepsilon g)'=\varepsilon^2 k$ while it is in the band, with $|g|\le G$ and $|k|\le K$, one can take $d=2|\varepsilon|G+T\varepsilon^2K$. The theorem checks these bounds only on the closed strip. The corrected equation for the physical longitudinal action is an input. The construction in N-51 supplies such an equation for its own normalized stream on a suitable periodic phase chart. Identifying that stream or constructing a correction directly for $J$ requires an additional argument. [Displacement bound](../../PlasmaLean/Theory/Geometry/AveragedConfinement.lean) · [Physical definition of longitudinal action, Burby, MacKay and Naik, §2.1](https://arxiv.org/html/2211.13367#S2.SS1)

## When the level is a winding graph

At a fixed height, let a continuous periodic family strictly bracket a target on its two radial faces. If the radial derivative is positive **at every point on the target level**, each angle has exactly one root. The root depends continuously on the angle and returns after one period. For two heights, disjoint roots at every angle and their order at one angle give a uniform positive separation. In the mirror application strict increase in height on the same regular well provides disjointness. The N-57 middle-radius height bracket supplies the order witness at angle zero. [Oriented crossings and compact-fibre continuity](../../PlasmaLean/Theory/Geometry/PeriodicOrientedCrossings.lean) · [Middle-radius witness](dommaschk-regular-mirror-cell.md)

The cubic $J=h+(2r-1)^3-(2r-1)/4$ has a face gap from $-5/8$ to $5/8$ on $0\le r\le1$, $|h|\le1/8$. At $h=0$ the zero level has three radii. The first theorem still applies. A second example, $r(2-r)$ on $[-1,3/2]$, folds above its target and has one upward zero crossing. Both examples are proved in Lean. [Three-root example](../../PlasmaLean/Theory/Geometry/ActionFaceBarrier.lean) · [Folded-profile example](../../PlasmaLean/Theory/Geometry/PeriodicOrientedCrossings.lean)

## Consequences for the candidate

For an initial band $|j_0-j_*|\le e$, a sufficient quantitative target is $e+d<\min(j_*-L,U-j_*)$. On the Dommaschk strip, this prioritizes the **upper** mirror height on the inner radial face and the **lower** height on the outer face. An interior radial derivative is needed for some graph or excursion estimates. The face-only confinement test can proceed in parallel. Both routes require a well defined along the orbit, an identification of launch radius with the physical observable, a physical clock, and a birth measure before contributing to thermal C2. [Candidate screen](dommaschk-mirror-screen.md) · [Physical acceptance predicate](hamiltonian-bounce-band-test.md)
