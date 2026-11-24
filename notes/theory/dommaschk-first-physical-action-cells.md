# Physical speed and arclength bounds on three original action panels

Lean now discharges the two pointwise physical bounds required by the action certificate on three panels in the phase-zero, radius-0.470 upper archive. Two panels straddle the birth section; the other is the earliest panel in the archive's increasing-angle order. Each has width $1/3072$ radian. All bounds use the original packed integer columns at the upper height $h_U=5300546391395933/5000000000000000$. [Packet contract](../../PlasmaLean/Certificates/MirrorActionQuadrature.lean) · [Archive-to-action theorem](dommaschk-complete-sublevel-archive.md)

| Signed angular interval | Physical trajectory covered | Upper bound on arclength per radian | Upper bound on clipped squared speed |
| --- | --- | --- | --- |
| $[-1/3072,0]$ and $[0,1/3072]$ | One signed Q-16 field line for each admissible birth | $1046881/2^{20}$ | $2151939/2^{26}$ |
| $[-325/64,-15599/3072]$ | One actual backward solution for each admissible local entry to outward slab 324 | $954067/2^{20}$ | $0$ |

The squared speed is $\max(2(h_U-|B|),0)$. In cylindrical coordinates the arclength density equals the norm of the angular derivative of the Cartesian field line. The launch proof identifies the two packed cells in their precise positions, including the final digit of slab 324 in chronological order. The earliest panel lies beyond the local mirror. A point bound at its inner edge and strict outward growth of squared field strength force its clipped speed to vanish throughout. The same local solution realizes the mirror hit and both columns of the earliest cell. [Arclength identity](../../PlasmaLean/Design/DommaschkPhysicalActionPanel.lean) · [Monotonicity argument](../../PlasmaLean/Design/DommaschkPhysicalActionCap.lean)

At present the connection between the local entry and this particular birth still requires the long physical trace. The entire endpoint action inequality requires the original pointwise bounds across all of its chronological panels. These first three cases establish how to discharge those bounds on actual ODE solutions. [Launch proof](../../scripts/dommaschk_kam/verify_physical_action_launch.py) · [Earliest panel proof](../../scripts/dommaschk_kam/verify_physical_action_cap.py)

## Reproduce

Build `PlasmaLean.Design.DommaschkPhysicalActionPanel` and `PlasmaLean.Design.DommaschkPhysicalActionCap`. For the earliest panel, first prepare the slope-324 and backward-hit-324 manifests as in [N-81](dommaschk-transverse-physical-mirror-brackets.md).

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_action_launch.py --output /tmp/qa2r-launch-cells.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_mirror_slopes.py --slopes /tmp/qa2r-slope-324.json --monotone --output /tmp/qa2r-monotone-324.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_action_cap.py --monotone /tmp/qa2r-monotone-324.json --physical-hit /tmp/qa2r-hit-back-324.json --output /tmp/qa2r-first-cell.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-86 |
| Kind | Physical realizations of original action-packet cells |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-66, N-77, N-81, N-82, N-84 |
| Dependency requirement | Signed Q-16 birth at the launch, or admissible entry to backward row 324 for the terminal local statement. |
| Produces | Three original upper action cells on actual physical solutions, with geometric arclength and clipped speed. |
| Difficulty | Reuse spatial bounds across successive panels and bind the local cap to the full birth trajectory. |
| Status | Launch and local-entry theorems passed and independently replayed. |
| Lean evidence | `DommaschkPhysicalLaunchAction.exists_nested_launch_cells`, `DommaschkFirstPhysicalActionCell.physical_cell`, `DommaschkFirstActionFromEntry.from_entry`. |
| Audit evidence | Standard three axioms; launch key `38fa46ba4f72`, local entry key `89b86392c7a1`. |
| Last updated | 24 November 2026 |
