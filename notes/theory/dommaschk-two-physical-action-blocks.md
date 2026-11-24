# The two complete physical action blocks around the launch

Every admissible phase-zero Q-16 birth at radius 0.470 admits a **single physical field line** satisfying the original action-packet contract on all 96 consecutive angular panels in $[-1/64,1/64]$. These are blocks 324 and 325 of the 650-block upper action archive at this launch. The theorem uses the original packed integers at the original times and proves the two inequalities on each entire closed panel. Block 324 is ordered towards the launch in increasing geometric angle. [Concrete proof producer](../../scripts/dommaschk_kam/verify_physical_action_launch_blocks.py)

Two versions of the cover hold on the same field line. One uses the exact cylindrical arclength formula; the other uses the norm of the derivative of the actual Cartesian trajectory. A physical solution is constructed for two slabs on either side of the section, placing **both edges of the quadrature interval** in the interior of the differentiable path. [Arclength along the physical ODE](../../PlasmaLean/Design/DommaschkPhysicalArcTrace.lean)

One pair of uniform bounds suffices on all 96 panels. Arclength per radian is at most $1046878/2^{20}$ and clipped squared parallel speed at most $2151939/2^{26}$. Lean verifies that each original upper record permits those bounds. To prove the second bound without excessive interval error, the verifier combines the field denominator $D$ and $kR^7$ **as polynomials before evaluation**, where $k=h_U-(2151939/2^{26})/2$. The five radial pieces share the three original field models. The general packet lemma allows the archived columns to differ from panel to panel. [Polynomial identity](../../PlasmaLean/Design/DommaschkCompensatedAction.lean) · [Uniform bounds to original packet cells](../../PlasmaLean/Certificates/MirrorActionUniformCells.lean)

This proves the physical input on two complete launch-adjacent blocks. N-86 also covers the first chronological panel from a local entry near the mirror. Extending the same signed trajectory and covering the remaining blocks are required for an unconditional whole-well action comparison. [Whole-archive implication](dommaschk-complete-sublevel-archive.md) · [First local mirror panel](dommaschk-first-physical-action-cells.md)

An independent exact Python replay reproduces all 31,200 original 72-bit action records at this endpoint, from the two signed sets of 325 outgoing trajectory slabs. It keeps seven harmonic channels and evaluates the spatial polynomials by Horner's rule. A comparison method using sparse field bounds and spatial subdivisions passed 168 of 325 signed slab pairs. The implementation target is therefore to verify the original seven-channel arithmetic and its connection to the physical field in Lean. The whole-archive replay is external arithmetic; the physical Lean cover above has 96 cells. [Original arithmetic replay](../../scripts/dommaschk_kam/replay_physical_action_archive.py) · [Subdivision comparison](../../scripts/dommaschk_kam/screen_action_block_reuse.py)

## Reproduce

With the tracked first-slab Jacobian and the standard physical launch modules built, run

```sh
lake build PlasmaLean.Certificates.MirrorActionUniformCells PlasmaLean.Design.DommaschkCompensatedAction PlasmaLean.Design.DommaschkPhysicalArcTrace
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_action_launch_blocks.py --output /tmp/qa2r-birth-blocks.json
.venv-ws/bin/python scripts/dommaschk_kam/replay_physical_action_archive.py --output /tmp/qa2r-original-action.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-90 |
| Kind | Physical cover of complete quadrature blocks |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-79, N-82, N-86 |
| Dependency requirement | Original action digits, exact field and harmonic models, two-sided physical birth path through the section. |
| Produces | Both geometric and Cartesian-derivative formulations of the original upper cover on 96 consecutive panels. |
| Difficulty | Efficiently discharge the other blocks and prove that the whole well lies on the same birth trajectory. |
| Status | Concrete physical cover and authenticated independent workstation replay passed. |
| Lean evidence | `DommaschkPhysicalLaunchBlocks.exists_nested_covers`, `MirrorActionQuadrature.cells_of_floor`, `DommaschkCompensatedAction.gap_from_shift`, `DommaschkPhysicalActionPanel.arcDensity_on_path`. |
| Audit evidence | Standard three axioms. Content key `fb11cf1750f2062f55c0e633f6805e11a1ddec030da2974431078c5ed8ff4838`. |
| Last updated | 24 November 2026 |
