# Two-sided physical field lines from four radial birth intervals

For every section point in any of the four radius-$2^{-16}$ seed balls of N-169, Lean constructs a single field line that follows the archived forward and backward tubes through angular distance $16/64$ on each side. On the closed interval $[-15/64,15/64]$, this line has an ordinary derivative equal to the QA2R field-line vector field. Its cylindrical coordinates obey $7/8\le R\le1$ and $|z|\le5/64$. The short interval includes the join at the symmetry section and the joins between consecutive slabs. The physical inputs cover every permissible starting point of every continuous radial tile. [Entry from the interpolated birth](upper-radial-ribbon-entry-and-caps.md) · [Joining and restriction](../../PlasmaLean/Design/DommaschkRibbonThroughChains.lean)

## What closes a physical step

The degree-seven reference curve, affine moving frame, incoming and outgoing ellipsoids, Euclidean radius and rational scalar budgets come from the original signed row. The numerical checker verifies the jump at the previous endpoint, a positive frame determinant, the operator bound, the centered defect, the logarithmic norm on the entire trial ellipsoid and the scalar propagation inequality. The strict inequality between the propagated radius and the trial radius supplies the first-exit argument. The proof keeps the actual Euclidean outgoing error specified for that row. This formulation permits the larger seed radius required by a continuous interval of births. [Wide moving-frame step](../../PlasmaLean/Certificates/PositionFrameWide.lean) · [Spatial hypotheses on the projected rectangle](../../PlasmaLean/Design/DommaschkWideTraceFields.lean)

Several clocks and radial tiles can share the expensive field evaluations. The center of the common time polynomial is the coefficientwise average of the tile centers rounded down on the dyadic grid. Its radius includes the full projected coordinate width and the sum of the absolute coefficient differences for each covered tile. An affine restriction theorem proves each original time interval lies within the shared model. Each signed step retains its own moving frame and radius. On these four phase-zero tiles, exact reflection relates the two original reference curves and frames, so the spatial proof can check a rectangle containing both signed trial projections, at the smaller of the two admissible growth rates. The central defect is authenticated independently on both original clocks. [Exact spatial grouping](../../scripts/dommaschk_kam/radial_ribbon_jacobians.py) · [Signed central defects](radial-ribbon-central-defects.md)

An exact screen partitions all 2,656 signed steps through $332/64$ into 78 common evaluations of three field polynomials and their six spatial derivatives. The first two eight-slab inlet groups have passed the kernel on all four tiles. The combined sixteen-slab theorem is `DommaschkRadialRibbonThrough016.from_seed`, with receipt key `e8e4d6765daeabb73679a1ce2a0add4f1ac959a3db589f36e5d6c485e016e837`. The eight-slab checkpoint has key `dd44ec88639585d5735ace58baf49e91a6c12f6ca19bdd8aeea846fba74990f2`. The two signs are glued from the same quantified initial state. The signed solution satisfies the original physical differential equation across zero. The returned `Tracks` proposition indexes the full stored lists in their original clock order. The theorem uses `propext`, `Classical.choice` and `Quot.sound`. [Actual signed row composer](../../scripts/dommaschk_kam/verify_ribbon_physical_group.py) · [Joined family verifier](../../scripts/dommaschk_kam/verify_ribbon_through_chains.py)

Every stored physical position tube through row 331 also satisfies the regular cylindrical bounds of N-171. Lean checks all 2,656 polynomial and physical error enclosures, quantifying over every point in each tube. The eight declarations in `DommaschkRibbonTubeRegions332` have receipt key `f56b36c2d5604866155aa2979cea9c69fb2dbff8ec253a9b9b0702aa512cf016`. Membership of the long radial family in those tubes depends on the remaining physical steps.

## Reproduction

The radius witness and compiled row packets are generated in N-169. The signed central receipts are generated in N-173. The following commands use one BLAS thread per worker.

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
py=.venv-ws/bin/python
src=scripts/dommaschk_kam
data=/tmp/plasma-n169-four-ribbons.json
packets=/tmp/plasma-n169-packets.json
lake build PlasmaLean.Design.DommaschkWideTraceFields PlasmaLean.Design.DommaschkRibbonThroughChains
"$py" "$src/plan_ribbon_spatial_groups.py" --ribbon "$data" --output /tmp/ribbon-spatial-plan.json
"$py" "$src/verify_ribbon_spatial_group.py" --ribbon "$data" --span 0 8 --output /tmp/ribbon-spatial-inlet.json
for k in 0 1 2 3; do
  "$py" "$src/verify_ribbon_physical_group.py" --ribbon "$data" --packets "$packets" \
    --tile "$k" --span 0 8 --output "/tmp/ribbon-physical-inlet-$k.json"
done
"$py" "$src/verify_ribbon_through_chains.py" --packets "$packets" --count 8 --output /tmp/ribbon-through-eight.json
"$py" "$src/verify_ribbon_through_chains.py" --packets "$packets" --regions-only --output /tmp/ribbon-all-regions.json
"$py" "$src/run_ribbon_physical_campaign.py" --ribbon "$data" --packets "$packets" \
  --plan /tmp/ribbon-spatial-plan.json --workers 2 --reserve-gib 40
"$py" "$src/verify_ribbon_through_chains.py" --packets "$packets" --count 16 --output /tmp/ribbon-through16.json
"$py" "$src/verify_ribbon_through_chains.py" --packets "$packets" --count 332 --wait --output /tmp/ribbon-through332.json
```

The longer campaign checks the 332nd row in each direction so the cap $331/64$ lies strictly inside the signed window. This is the step needed to attach the previously certified common high-cap signs and first-mirror orientation to a field line for every intermediate birth. The complete through-cap claim requires all eight chains.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-175 |
| Kind | Physical ODE propagation for a continuous radial interval |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-65, N-119, N-169, N-171, N-173 |
| Dependency requirement | Immutable signed wide-row packets, exact central defects, positive-denominator field derivatives, and a common four-tile seed cover |
| Produces | Two-sided true field lines from every point of the four seed balls, with original row membership and ordinary derivatives on a closed interior window |
| Status | Sixteen adjacent original slabs in either direction kernel-checked on all four tiles. The complete 2,656-row regular-region enclosure is kernel-checked. The 332-slab physical campaign is running. |
| Lean evidence | `PositionFrameWide.physical_step_on`, `DommaschkWideTraceFields.forward_rectangle`, `.backward_rectangle`, `DommaschkRibbonThroughChains.from_chains`, `DommaschkRadialRibbonThrough016.from_seed`, `DommaschkRibbonTubeRegions332.forward0` and its seven companion claims |
| Last updated | 25 November 2026 |
