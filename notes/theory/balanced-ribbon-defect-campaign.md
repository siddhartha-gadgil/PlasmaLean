# Scheduling signed central defects and spatial bounds for the same radial trajectories

An original moving-frame IVP step requires both a spatial logarithmic-norm bound on its trial rectangle and a central ODE defect along its own polynomial reference. In the four-ribbon proof these two certificates have different costs. At the workstation handoff the kernel had accepted spatial bounds for 1,200 of the 1,328 ribbon row pairs, central defects for 600 pairs and both physical ODE steps for 584 pairs. Across all four tiles the first 128 pairs had already been joined. [Original physical-step verifier](../../scripts/dommaschk_kam/verify_ribbon_physical_group.py) · [Signed defect verifier](../../scripts/dommaschk_kam/verify_ribbon_central_group.py)

The four-tile theorem `DommaschkRadialRibbonThrough128.from_seed` supplies a single actual physical solution through each prescribed section state in its tile's initial ball. It proves the ordinary field-line equation and regularity on the closed angular interval `[-127/64,127/64]` and retains both 128-row tube histories. The final row on each side gives an exterior interval for the ordinary derivative at the closed endpoints. The kernel checked the combined theorem with `propext`, `Classical.choice` and `Quot.sound`. Its key is `feb07dd3a77cf75d0487342028cea5458ad5d848205f20d57fa3de30b545c14a`. The combined four-tile check used 6.32 GiB peak process RSS, compared with 5.42 GiB for 64 rows. [Through-chain construction](../../scripts/dommaschk_kam/verify_ribbon_through_chains.py)

## Assigning workers to the physical proof

An 80-second workstation sample before the handoff attributed 5.97 CPU cores to the ribbon spatial and physical checks, 2.00 to central defects, and 5.96 to the six other endpoint continuations. Across 24 available cores the sample measured 4.28 idle cores and 0.01 core of I/O wait. Available RAM remained above 100 GiB. During an eight-minute window, the older two controllers delivered 344 spatial row pairs, 80 central row pairs and 88 pairs of physical steps.

The joint controller checks every existing row against its packet, original index, signed theorem names, compiled artifacts and kernel audit. It holds the existing exclusive locks for both proof queues. During the transition, the two previous dispatchers stopped assigning new work, their in-flight groups finished, and the joint controller acquired their locks. Its worker pool first closes ready physical IVPs, then compares each tile's contiguous spatial and central coverage. A lead above twelve rows assigns the next slot to a central defect. This keeps the physical proof moving even when different tiles take different amounts of time to verify. [Controller and admission policy](../../scripts/dommaschk_kam/run_balanced_ribbon_campaign.py)

The workstation runs at most eight workers for the joint queue, with 40 GiB of available RAM reserved. It starts with seven workers and adjusts after two successive twenty-second CPU observations. It raises the target when at least three cores are idle and lowers it when fewer than two are idle. A group already in progress runs through its kernel audit. The two previous systemd CPU limits summed to 8.75 cores. Independent endpoint and action calculations use their own existing budgets.

The first 80-second sample after the transition measured 7.97 cores for the combined ribbon queue, equal to the previous 5.97 plus 2.00 cores. Other endpoint continuations used 6.95 cores during the second sample, and the workstation retained 3.20 idle cores. The faster supply of central bounds comes from reassignment within the ribbon's budget.

Two eight-minute windows give the following original signed row-pair counts. Each counted central or physical pair contains the two opposite clock directions for one tile and row. The second window consumed spatial bounds prepared earlier. These rates compare successive production windows on the same trajectory packet. [Receipt window replay](../../scripts/dommaschk_kam/measure_ribbon_receipt_rate.py)

| Completed and authenticated | Earlier controllers | Joint controller |
| --- | ---: | ---: |
| Central defect pairs | 80 | 208 |
| Spatial bound pairs | 344 | 0 |
| Actual physical IVP pairs | 88 | 224 |

The rate of central defect delivery rose by a factor of 2.60. The number of actual physical IVP pairs in the same wall-clock interval rose by a factor of 2.55. Stored spatial bounds still covered all four physical fronts at the end of the measurement.

Eight adjacent signed IVPs can also be composed while the later rows are still being proved. The incremental verifier uses the same per-tile row list, declaration source, kernel parents and cache key as the final family join. The workstation allocates half a core to this check after the timing comparison, leaving at most 7.5 for further leaf work. The total ceiling remains eight. [Incremental signed chain segments](../../scripts/dommaschk_kam/precheck_ribbon_segments.py)

## Reproduction

The commands below use the N-169 signed witness and row lists, the N-173 degree-twelve central plan and the N-177 spatial plan. The existing N-187 dyadic frame and adaptive-panel proofs are used from their recorded rows. The measurement counts actual row handoffs in two elapsed workstation time windows and independently verifies their signed Lean theorem names and artifact hashes. Fresh checkouts can use the timestamps for their own runs. [Central plan](../../scripts/dommaschk_kam/plan_ribbon_central_groups.py) · [Spatial plan](../../scripts/dommaschk_kam/plan_ribbon_spatial_groups.py) · [Receipt measurement](../../scripts/dommaschk_kam/measure_ribbon_receipt_rate.py)

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
src=scripts/dommaschk_kam
"$py" "$src/run_balanced_ribbon_campaign.py" \
  --ribbon /tmp/plasma-n169-four-ribbons.json --packets /tmp/plasma-n169-packets.json \
  --plan /tmp/plasma-n177-spatial-plan.json --central-plan /tmp/plasma-n173-central-plan.json \
  --central-status /tmp/plasma-n173-central-campaign.json --workers 8 --initial-workers 7 \
  --reserve-cores 2 --reserve-gib 40
"$py" "$src/measure_ribbon_receipt_rate.py" --before-end 1795569615 --after-start 1795569815 \
  --seconds 480 --output /tmp/plasma-n197-real-throughput.json
"$py" "$src/precheck_ribbon_segments.py" --packets /tmp/plasma-n169-packets.json \
  --from-row 128 --count 332 --wait --output /tmp/plasma-n197-streamed-segments.json
"$py" "$src/verify_ribbon_through_chains.py" --packets /tmp/plasma-n169-packets.json \
  --count 128 --output /tmp/plasma-n175-through128.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-197 |
| Kind | Physical trace verification checkpoint and measured proof scheduling |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-169, N-173, N-175, N-177, N-187 |
| Produces | A 128-row through-chain on every radial tile and a shared resource ceiling for central, spatial and true physical IVP proofs |
| Status | The four-tile closed interval through ±127/64 is kernel-checked. Equal eight-minute production windows delivered 80 then 208 central defect pairs, and 88 then 224 true physical pairs, with the same measured total ribbon CPU use. Longer intervals are assembled from the original accepted rows. |
| Lean evidence | `DommaschkRadialRibbonThrough128.from_seed` and each constituent `DommaschkPhysicalQ0R{471,473,475,477}{Forward,Back}NNN.physical_step` |
| Last updated | 25 November 2026 |
