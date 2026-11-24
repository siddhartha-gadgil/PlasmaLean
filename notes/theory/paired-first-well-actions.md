# A finite radial secant between the first wells on two field lines

The QA2R pilot at radial label \(u=47/100\) and its neighbor at \(u=239/500\) now have a direct physical comparison on one embedded pair of invariant tori throughout \(-1\leq\phi\leq1\). For every admitted birth angle, their field strengths obey \(f_o\le f_i-1/18000\) and their increasing-angle Cartesian arclength densities obey \(w_o\ge (3999/4000)w_i\) there. The archived pilot is calibrated through both first mirrors. The neighboring trajectory needs to reach its own first mirrors to compare the full integrals. [Compared physical trajectories](compared-signed-trace-prefixes.md) · [Ordered outer 89 slabs](ordered-paired-profile-suffix.md)

## First-well theorem

Let \(J_u(h)\) be the single-passage action between the first two field-strength contacts enclosing the birth section at height \(h\), integrated with respect to Cartesian arclength. Use the same two nested embedded tori and the same birth angle \(|\phi_0|\le2^{-19}\) for both labels. For the full conclusion the two remaining finite inputs are:

1. A calibrated family with a signed outer trajectory through at least 328 slabs in each direction, whose first 327 rows agree with the outward branch archive.
2. The synchronized field and arclength comparisons on the first 325 original paired rows on each clock.

For every height for which both \(h\) and \(h+1/18000\) belong to the archived closed height band, the outer first well at \(h\) contains the pilot first well at the raised height. Its outward contact times in each direction belong to \((317/64,327/64)\). At equal heights the action difference and its secant satisfy
\[
 J_{239/500}(h)-J_{47/100}(h)>1/375,\qquad
 \frac{J_{239/500}(h)-J_{47/100}(h)}{239/500-47/100}>1/3.
\]
The pilot and outer paths are fixed before the height is chosen. The theorem compares the original physical trajectories and keeps the signed approach from each outer birth to the central section. The secant measures variation in the interpolated radial label. A thermal confinement time or a bound on bounce-averaged radial drift requires further physical input. [Physical action and secant](../../PlasmaLean/Design/DommaschkPairedFirstWellAction.lean) · [Calibration by height shift](finite-radial-action-comparison.md)

The mirror branches select the first contacts of the same outer path used by the paired estimates. The signed ODE on a larger interval makes the Cartesian speed equal to the field-derived arclength density on the entire closed outer well. At the pilot, the action calibration identifies a single pair of branches valid throughout the height band. Thus the interval estimates, moving endpoints and physical integrals all refer to the same two paths. [Generated branch application](../../scripts/dommaschk_kam/templates/paired_first_well_action.lean.tpl)

## Evidence and replay

The concrete 64-pair theorem `DommaschkComparedBirths064On391_128_48_5_32_5_5_5.from_common_tori` has key `a4817583f63dcf3c9de1ee199b349c2938cdf943a3291a3d449e4eb71a43542a`. The true signed trajectories and profile estimates apply simultaneously throughout ±1 radian there. The 13 grouped certificates also prove the two estimates over the disjoint outer intervals \(59/16\le|\phi|\le325/64\) for paths enclosed in those tubes. [Complete outer interval](ordered-paired-profile-suffix.md)

The theorem `DommaschkPairedFirstWell325.from_family` discharges the mirror, continuity and arclength obligations from the first 327 specified rows. Its proof key is `a2171f3a40357a5d476cd3b32c7c3ed20caab89019da6f7aca30b1c8254c1946`. At this checkpoint its two finite inputs above remain open. The generator can also consume the calibrated through-mirror family and its full 325-pair receipt to produce an unconditional declaration. [Proof generator](../../scripts/dommaschk_kam/verify_paired_first_well_action.py)

~~~bash
lake build PlasmaLean.Design.DommaschkPairedFirstWellAction
.venv-ws/bin/python scripts/dommaschk_kam/verify_paired_first_well_action.py \
  --well /tmp/plasma-q0r478-first-well-lower-bridge.json \
  --output /tmp/plasma-paired-first-well-bridge.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-144 |
| Kind | Conditional first-well comparison, physical secant and verified trajectory prefix |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-126, N-127, N-130, N-136, N-138, N-143 |
| Dependency requirement | One calibrated embedded family, the second signed mirror passage, and synchronized physical profiles through 325 rows |
| Produces | A strict equal-height action secant from finite endpoint data and a concrete two-trajectory comparison on ±1 radian |
| Status | Conditional first-well theorem and physical 64-pair prefix kernel-verified |
| Lean evidence | `DommaschkPairedFirstWellAction.on_chosen_paths`, `.gains_of_branches`, `.common`, `.physical_secant` and `DommaschkPairedFirstWell325.from_family` |
| Audit evidence | Generated physical theorems use propext, Classical.choice and Quot.sound |
| Last updated | 25 November 2026 |
