# The actual opposite-section inner birth carries its first two action blocks

**26 November closeout.** All 320 pairs and their 15,360 action panels have been joined on one physical field line, and the queued first-well observation theorem passed. The original one-pair checkpoint and run instructions below record the earlier stage. [Completed campaign, exact action bound and archived theorem names](../../generated/qa2r/README.md#opposite-inner-campaign-closeout-26-november-2026)

For the original inner radius \(u=47/100\), both physical ODE steps from the \(\pi/2\) section are now Lean-certified. Their joined, increasing-angle field line carries 48 independently verified action panels on \([-1/64,1/64]\) relative to the section. Every original birth within \(2^{-27}\) of \(\pi/2\) follows the field to the initial point of this trajectory on the same pair of embedded tori. [Signed trajectory theorem](../../PlasmaLean/Design/DommaschkOppositeInnerTrajectory.lean) · [Original trajectory and panel assembler](../../scripts/dommaschk_kam/verify_opposite_inner_trajectory.py)

| Field | Value |
| --- | --- |
| ID | N-204 |
| Kind | Physical ODE certificate and resumable computation |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-195, the Q-16 embedded surfaces, independent phase-shifted moving-frame certificates, physical panel quadrature |
| Produces | A common signed physical field line, two actual ODE steps, and a lower panel cover for the first 48 opposite-sector panels |
| Status | The first checkpoint verified one signed pair. The 26 November closeout verifies all 320 pairs and 15,360 panels. |
| Lean evidence | Generated `DommaschkOppositeInnerThrough001.from_nested_tori`, `.physical_cells`, `.forward_steps`, `.backward_steps`; reusable `DommaschkOppositeInnerTrajectory.from_seed` and `.from_entry` |
| Audit evidence | All five trajectory assembly theorems use `propext`, `Classical.choice`, `Quot.sound`. The independent matrix, central defect, ODE and panel rows passed their own audits |
| Updated | 2026-11-25 |

## Signed physical proof

The original packet has separate central curves, error budgets and end frames for the two directions. The spatial proof bounds nine physical field quantities on a common projected rectangle and proves the matrix inequality separately for each archived frame. The central proof computes the signed trajectory defect separately in each direction. The local ODE starts at every point in the common Euclidean birth seed and arrives in the respective recorded end enclosure. At longer prefixes the entrance to each next step accepts the previous end enclosure. [Original ODE proof generator](../../scripts/dommaschk_kam/verify_opposite_inner_ode_group.py)

The trajectory and the observable certificates are attached by matching the original time, direction, position row and predecessor. The backward and forward chronological blocks share the same field line. The 24 original panels on each side correspond to 96 stored half-panel inequalities. This first physical window is too short to imply the N-195 action floor. That floor needs 320 pairs of physical rows and at least one actual first well for a statement about its value. [Positive-core reduction](opposite-inner-action-subwell.md)

| Physical result | Proof key |
| --- | --- |
| Shared spatial group and the independent first matrices | `a91382ad48f3e78da6a8dc81e2cce60219510b00e3ca04a3cba89fbe3efd0f77` |
| First forward ODE step | `c592c5c2cae1b7f1fa034e3a9988c78f973050801546beff7d2c49fd47f068bb` |
| First backward ODE step | `868cba6a2bb0e4bb61655fda2b97d98562164e2f3efc2523f40e8fdd9c892cfd` |
| Joined original trajectory, both action blocks, and nested original births | `ec4cadfc6436192feeadcce997379b297ba19805dce650cded65678e1f2c1279` |

## Standalone replay

Generate the canonical packet and the complete positive lower mass using the N-195 commands. Build the reusable trajectory theorem and run the signed campaign on its first row.

~~~sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
py=.venv-ws/bin/python
src=scripts/dommaschk_kam
lake build PlasmaLean.Design.DommaschkOppositeInnerTrajectory
"$py" "$src/run_opposite_inner_action_campaign.py" \
  --packet /tmp/plasma-n195-q1r470.json.gz --core /tmp/plasma-n195-subwell.json \
  --span 0 1 --workers 1 --output /tmp/plasma-opposite-inner-test.json \
  --through-output /tmp/plasma-n204-secondary-through001.json
~~~

The workstation unit `plasma-opposite-inner-action.service` verifies the canonical four-tile through-going receipt before starting additional rows. It allows two single-threaded workers, limits CPU to two cores, reserves four cores and 48 GiB of available RAM before starting jobs, and has 18 GiB and 26 GiB soft and hard service memory limits. The original singleton packet is pinned by SHA-256. Each accepted group is stored atomically and validated by the artifact digest and the expected proof declaration on restart. Nearby rows share field models whenever their individual signed budgets pass exact preflight. A failed group is bisected. A singleton outside its recorded budget remains an explicit failure in the campaign status. The complete invocation for a restart is below. [Campaign runner](../../scripts/dommaschk_kam/run_opposite_inner_action_campaign.py)

~~~sh
"$py" "$src/run_opposite_inner_action_campaign.py" \
  --packet /tmp/plasma-n195-q1r470.json.gz --core /tmp/plasma-n195-subwell.json \
  --span 0 320 --group 8 --workers 2 --reserve-cores 4 --reserve-gib 48 --poll 12 \
  --after-receipt /tmp/plasma-n175-through332.json --output /tmp/plasma-n204-secondary-campaign.json \
  --through-output /tmp/plasma-n204-secondary-through320.json
~~~

The observed sum of kernel build times for the first singleton pair of ODE steps was 228.76 seconds on one worker. Four independent single-direction observable rows took 107–115 seconds apiece, including their field models and exact panel checks. At that rate the remaining 636 signed observable rows account for about 20 single-worker hours. Larger ODE groups share the field part of the first measurement. The reported timings exclude queueing and the final trajectory assembly.

The offline planning preflight covered all 320 proposed row pairs in both directions. It found 41 spatial groups and 43 central groups with no unsupported row. Each subsequent physical step and action cover still needs its ordinary Lean proof.
