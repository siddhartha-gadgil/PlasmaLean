# Eight exact action comparisons on adaptive speed grids

Lean now checks the integer arithmetic for all 2,655 speed intervals in the eight adaptive Dommaschk tables from N-73. Each table starts at zero, has strictly positive widths, ends at speed 2, and gives a strict one-sided comparison with the dimensionless target $J_* = 6799610938322487/5000000000000000$. [Eight concrete proofs](../../PlasmaLean/Design/DommaschkSublevelActionGrids.lean)

| Section | Radius | Cells | Comparison under the node bounds |
| --- | ---: | ---: | --- |
| 0 | 0.470 | 305 | $J<J_*$ |
| 0 | 0.478 | 433 | $J>J_*$ |
| 0 | 0.523 | 330 | $J<J_*$ |
| 0 | 0.531 | 409 | $J>J_*$ |
| 1 | 0.456 | 253 | $J<J_*$ |
| 1 | 0.464 | 336 | $J>J_*$ |
| 1 | 0.509 | 260 | $J<J_*$ |
| 1 | 0.517 | 329 | $J>J_*$ |

For a finite measured well with measurable field strength and the stated floor, the reusable theorem converts a table directly into a strict action inequality. At speed $v$, the height of the rectangle bounds the arclength of the set where $B≤h-v^2/2$. An upper comparison uses the left edge of each speed interval and a lower comparison uses the right. Widths have units of $2^{-20}$ in speed and heights have units of $1/(3072·2^{20})$ in dimensionless arclength. Lean checks the exact integer mass and proves that rescaling it gives the real rectangle sum. [Reusable checker and node hypotheses](../../PlasmaLean/Certificates/SublevelActionGrid.lean)

The table generator regroups directed time-panel data from the N-60 archive. Independent Python arithmetic checks the correspondence between the archived speed weights and the proposed grid. Each of the eight Lean theorems explicitly assumes its directed arclength inequalities on the measured well. Establishing those inequalities on an actual field line requires arclength and speed control over its whole well, including the mirror brackets.

## Reproduce

```sh
.venv-ws/bin/python scripts/dommaschk_kam/emit_sublevel_action_grids.py --check
.venv-ws/bin/python scripts/dommaschk_kam/screen_sublevel_speed_grid.py
lake build PlasmaLean.Design.DommaschkSublevelActionGrids
lake env lean scripts/check_axioms_heavy.lean
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-78 |
| Kind | Reusable action certificate and eight concrete instances |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-60, N-61, N-72, N-73 |
| Dependency requirement | Measured well, nonnegative field strength for the concrete heights, and correctly directed node arclengths. |
| Produces | Kernel-checked strict target arithmetic on each of the eight adaptive grids. |
| Difficulty | Attach physical node inequalities to the signed trajectories. |
| Status | All eight concrete conditional theorems compiled. |
| Lean evidence | `SublevelActionGrid.action_target` and the eight `DommaschkSublevelActionGrids.Q…R….endpoint` theorems. |
| Audit evidence | Reproducible byte-identical generation, successful default build and heavy audit over 95,167 declarations. |
| Last updated | 24 November 2026 |
