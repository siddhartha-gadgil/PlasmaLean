# Integer frame arithmetic and smaller time covers for the radial family

On the first eight slabs of radial tile 0, Lean checked the same physical Jacobian and growth budgets in 24.592 seconds with integer matrix arithmetic and adaptive time subdivision. The earlier certificate took 44.678 seconds on the same workstation and single-core limit. Both certificates bound the full physical trial rectangle over each original slab. The original forward and backward ODE steps were then rechecked against their signed central defects and archived radii. [Wide ribbon through-chains](radial-ribbon-through-chains.md) · [Integer field evaluations](../../PlasmaLean/Certificates/DyadicHornerStep.lean)

## Where the reduction occurs

The four affine coordinate entries and the derivatives of those entries have exact dyadic models. Matching each pair of stored endpoint integers to those models leaves a closed integer equality. For the quotient-rule matrix and its moving-frame transformation, the kernel checks each multiply, add, subtract and negate against the supplied dyadic Taylor model. Each check uses an integer bound on coefficient rounding, discarded terms and input errors. The resulting matrix models retain the same original coefficients, error radii and denominator as the rational computation. [Affine frame and operation lemmas](../../PlasmaLean/Design/DommaschkDyadicFrameModel.lean) · [Matrix proof emitter](../../scripts/dommaschk_kam/emit_sparse_jacobian.py)

For each symmetric matrix enclosure the producer tries one, two, four and eight equal time panels. On each panel it uses a positive lower denominator bound and checks both diagonal bounds and the determinant inequality at the original rate. The first successful subdivision covers the full closed time interval. For the 69 shared spatial evaluations selected in N-177, the exact screen gives the following counts. [Principal-minor certificate](../../PlasmaLean/Design/DommaschkJacobianPanels.lean) · [Spatial producer](../../scripts/dommaschk_kam/verify_ribbon_spatial_group.py)

| Time panels | Original signed row pairs |
| ---: | ---: |
| 1 | 459 |
| 2 | 763 |
| 4 | 104 |
| 8 | 2 |

This requires 2,417 panel checks across 1,328 paired moving frames, compared with 10,624 in the uniform eight-panel schedule. The mathematical inputs are the actual field jet, the original frames on both sides, their trial widths and the smaller admissible signed growth rate.

| Tile 0, rows 0–7 | Checked matrix and wrapped physical rate |
| --- | ---: |
| Rational matrix, eight panels | 44.678 s |
| Integer matrix, eight panels | 32.265 s |
| Integer matrix, adaptive panels | 24.592 s |

The last row has key `e90d0977871351457fd46052f8757a3b6712cc7d28ce26f4a92e745344de13cb`. Its sixteen original forward and backward physical IVP steps took a further 5.965 seconds and have key `20e53f199502002be940f71c5d59eb2875ba166e49f51906867540c95932e704`. The numerical budgets are identical across all three measurements. The recorded kernel times include their axiom audits and exclude the previously compiled field jet.

## Can the spatial jet also supply the central defect?

The original moving-frame inequality needs a much sharper estimate of the central ODE defect than it needs for the surrounding spatial derivative. An exact screen tried using the three full spatial field-value models directly on the local central curve. None of the 1,328 original paired defect budgets closed. The smallest ratio of proposed defect bound to budget was 17,462.28. [Central defect proof](radial-ribbon-central-defects.md) · [Exact transfer experiment](../../scripts/dommaschk_kam/screen_ribbon_center_transfer.py)

A second screen evaluated the fields accurately along one tile's central curve, then transferred them to another tile in the same shared box using the six spatial first-derivative models and the polynomial difference of the two centers. The best ratio fell to 4.8910, and the median ratio was 55.9167. All 3,752 ordered cross-tile transfers exceeded their original budgets. The figures quantify the loss for this particular shared enclosure and first-order transfer. The production run continues to check the central field along each tile with its own narrower models.

## Reproduction

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
py=.venv-ws/bin/python
src=scripts/dommaschk_kam
data=/tmp/plasma-n169-four-ribbons.json
packets=/tmp/plasma-n169-packets.json
lake build PlasmaLean.Design.DommaschkDyadicFrameModel
"$py" "$src/plan_ribbon_spatial_groups.py" --ribbon "$data" --partition-from 32 --output /tmp/ribbon-plan.json
"$py" "$src/screen_ribbon_center_transfer.py" --ribbon "$data" --plan /tmp/ribbon-plan.json --output /tmp/ribbon-reuse.json
"$py" "$src/verify_ribbon_spatial_group.py" --ribbon "$data" --span 0 8 --prove-tiles 0 \
  --dyadic --integer-frame --handoff /tmp/ribbon-matrices --output /tmp/ribbon-eight-matrices.json
"$py" "$src/verify_ribbon_physical_group.py" --ribbon "$data" --packets "$packets" --tile 0 \
  --span 0 8 --spatial /tmp/ribbon-matrices --handoff /tmp/ribbon-step-check \
  --output /tmp/ribbon-eight-signed-pairs.json
"$py" "$src/run_ribbon_physical_campaign.py" --ribbon "$data" --packets "$packets" \
  --plan /tmp/ribbon-plan.json --dyadic-from 22 --integer-frame-from 56 \
  --workers 6 --reserve-cores 2 --reserve-gib 40
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-187 |
| Kind | Physical certificate implementation and exact comparison of transfer methods |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-169, N-173, N-175, N-177 |
| Dependency requirement | Authenticated original signed radius, frame and central-defect records, dyadic multiplication bounds and the physical field Jacobian |
| Produces | A smaller verified matrix certificate and an exact comparison of direct and first-order reuse of the spatial field on the central curve |
| Status | Eight matrix bounds and both signed physical IVPs on every tested row kernel-checked. The complete adaptive panel counts and transfer failures are exact external arithmetic. |
| Lean evidence | `DommaschkDyadicFrameModel.frame_mem`, `.velocity_mem`, `.mul_mem`, `.add_mem`, `.sub_mem`, `.neg_mem` and the original signed `DommaschkPhysicalQ0R471{Forward,Back}00i.physical_step` for i = 0 through 7 |
| Audit evidence | The 24 spatial and 32 physical declarations use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |
