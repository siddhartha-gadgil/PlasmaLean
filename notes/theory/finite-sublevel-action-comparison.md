# Comparing bounce actions from finitely many sublevel lengths

For a measured magnetic well with field strength $B$, let $F(v)$ be the arclength below the field-strength threshold $h-v^2/2$. In the project's single-passage normalization the action at mirror height $h$ is $J=\int_0^V F(v)\,dv$, where $V=\sqrt{2(h-b_0)}$ for a common lower field bound $b_0$. The profile $F$ is nonincreasing. Thus an arclength bound at the right end of a speed interval supplies a lower rectangle, and one at the left end supplies an upper rectangle. This applies to plateaus and atoms of the arclength distribution. [Representation theorem](bounce-action-sublevel-arclength.md) · [Finite-panel proofs](../../PlasmaLean/Theory/Kinetic/MirrorSublevelPanels.lean)

## A finite-sample comparison theorem

Choose any increasing grid $0=v_0\le\cdots\le v_n=V$, with largest gap at most $d$. Let $F,G$ be the profiles of two finite measured wells. If $|F(v_i)-G(v_i)|\le\varepsilon$ at all grid nodes, then
$$
|J_F-J_G|\le V\varepsilon+d\bigl(G(0)-G(V)\bigr).
$$
The first term accounts for the errors at measured thresholds. The second accounts for variation between thresholds and uses only the reference profile $G$. The proof sums the rectangle bounds and telescopes the successive drops of $G$. Independently of any second well, interval bounds on the node lengths give certified upper and lower sums for a single action.

The mesh correction has a concrete purpose. On two wells of unit arclength, take the constant field strengths $3/2$ and $7/8$ at mirror height 2. Both wells have the same sublevel lengths at field strengths 0 and 2. Their actions are 1 and $3/2$. This counterexample is kernel-checked alongside the estimate. [Theorem and counterexample](../../PlasmaLean/Theory/Kinetic/MirrorSublevelPanels.lean)

## Exact screen on the eight action endpoints

The existing Dommaschk packets store a directed speed bound and arclength-density bound on each original time panel. A Python replay checked every original square-root inequality and slab mass before grouping the panels by speed. On the fixed speed interval $[0,2]$, it tested uniform dyadic grids and a deterministic adaptive grid that bisects the cell with the largest gap between its two rectangle areas. The table shows the first grid of each kind that preserved the strict comparison with the archived target action. The computations use integers and rational numbers. [Replay script](../../scripts/dommaschk_kam/screen_sublevel_speed_grid.py) · [Original packet theorem and scope](dommaschk-mirror-certificate-replay.md)

| Section | Launch radius | Bound sought | Uniform speed intervals | Adaptive speed intervals |
| --- | ---: | --- | ---: | ---: |
| 0 | 0.470 | Upper | 8,192 | 305 |
| 0 | 0.478 | Lower | 8,192 | 433 |
| 0 | 0.523 | Upper | 8,192 | 330 |
| 0 | 0.531 | Lower | 8,192 | 409 |
| $\pi/2$ | 0.456 | Upper | 4,096 | 253 |
| $\pi/2$ | 0.464 | Lower | 8,192 | 336 |
| $\pi/2$ | 0.509 | Upper | 4,096 | 260 |
| $\pi/2$ | 0.517 | Lower | 8,192 | 329 |

Run `python3 scripts/dommaschk_kam/screen_sublevel_speed_grid.py` to reproduce the grid counts and exact positive margins. This screen concerns eight separate one-sided action comparisons. It uses all the original time-panel inputs and does not establish a discrepancy between neighboring field-line labels. Its practical use is to identify a feasible number of thresholds for future direct geometric arclength certificates. For a drift bound, one still needs control of the label variation between wells and the physical guiding-centre reduction.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-73 |
| Title | Comparing bounce actions from finitely many sublevel lengths |
| Kind | Mathematical theorem and exact arithmetic screen |
| Addresses | G-10, Q-35, N-69 |
| Depends on | N-72 for the action representation, N-61 for the eight directed packet inputs |
| Dependency requirement | A finite arclength measure and lower field bound for each well, a common speed grid, and certified node-length bounds. |
| Produces | Finite action enclosures, a two-well comparison with mesh correction, an exact counterexample, and adaptive-grid counts. |
| Difficulty | Establishing physical sublevel lengths across a returning family of wells remains the design problem. |
| Status | The general estimates and counterexample are compiled in the default library. The adaptive endpoint counts are external exact arithmetic. |
| Lean evidence | `Kinetic.MirrorSublevelAction.action_between_panel_sums`, `panel_gap_le`, `sampled_action_difference_le` and `two_thresholds_miss_action`. |
| Audit evidence | All four entry points are included in the default axiom audit. |
| Last updated | 24 November 2026 |
