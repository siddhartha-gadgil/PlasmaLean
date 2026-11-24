# All eight adaptive action grids follow from the original time-panel covers

Lean now derives **every one of the 2,655 adaptive arclength inequalities** in N-78 from the corresponding N-60 time-panel cover. A single exact pass through each endpoint archive counts the weights of all speed witnesses at or above each threshold. Across all eight archives, the proof uses 250,848 time panels. Weights at equality are included, which matters in both directions of comparison. [Histogram correctness](../../PlasmaLean/Certificates/MirrorSpeedHistogram.lean) · [Concrete proof generator](../../scripts/dommaschk_kam/emit_sublevel_archive_histograms.py)

For the four upper endpoints and four lower endpoints, the physical conclusion is the original strict comparison between the one-passage action in geometric angle and $6799610938322487/5000000000000000$. The hypotheses are that the physical field strength and arclength density satisfy the pointwise cover on the original time panels, the profiles are measurable, and the density is nonnegative and integrable on the bracket. The action theorem also requires nonnegative field strength there. All threshold counts, their association with the adaptive grid, and the quadrature normalization are now discharged in Lean. Proving the cover for the true field line across each whole well remains the physical task. [Upper example](../../PlasmaLean/Design/DommaschkSpeedHistogramQ0R470.lean) · [Lower example](../../PlasmaLean/Design/DommaschkSpeedHistogramQ0R478.lean) · [All eight comparison directions](dommaschk-adaptive-action-grids.md)

Each time panel updates one path in a balanced tree of thresholds. A general induction proves that every represented cutoff returns exactly the density sum obtained by scanning the packed archive at that cutoff. Each concrete final tree is verified by kernel reduction. Its agreement with all the table heights is checked separately. The largest table has 433 cutoffs and needs at most nine comparisons per time panel.

## Reproduce

```sh
.venv-ws/bin/python scripts/dommaschk_kam/emit_sublevel_archive_histograms.py --check
for name in Q0R470 Q0R478 Q0R523 Q0R531 Q1R456 Q1R464 Q1R509 Q1R517; do
  lake build "PlasmaLean.Design.DommaschkSpeedHistogram$name"
done
lake env lean scripts/check_axioms_heavy.lean
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-82 |
| Kind | Reusable exact histogram certificate with eight complete applications |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-60, N-61, N-73, N-78, N-80 |
| Dependency requirement | Directed physical packet cover on the stated closed angular interval, with the measurability and sign assumptions above. |
| Produces | All adaptive node inequalities and strict geometric-angle action comparisons at all eight endpoints from original time-panel covers. |
| Difficulty | Realize the archived speed and density contracts over the actual physical trajectories. |
| Status | All eight concrete packet reductions, table matches, nodal implications and endpoint action theorems compiled and audited. |
| Lean evidence | `MirrorSpeedHistogram.scan_spec`, `.nodeBounds`, `.trace_action` and the eight concrete `.scanned`, `.nodes` and `.endpoint` declarations. |
| Audit evidence | The final packet-to-tree reductions use only `propext`; the eight physical implications use the standard three axioms. Heavy audit passed over 95,430 declarations. |
| Last updated | 24 November 2026 |
