# Original upper-action digits on both physical tubes at outward row 16

For the phase-zero QA2R launch at radius parameter $u=47/100$, Lean proves the original upper-action bounds at every physical state in each of the 48 closed panels of outward row 16, in each direction. The archive stores those 96 panels in chronological blocks **308** and **341**. The hypotheses are membership of the physical state in the corresponding outgoing tube and membership of the angular time in the specified panel. The result applies from any predecessor state. [Physical panel proof producer](../../scripts/dommaschk_kam/verify_native_physical_action_panels.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-94 |
| Title | Original upper-action digits on both physical tubes at outward row 16 |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-66, N-79, N-82, N-86, N-90 |
| Dependency requirement | The identified QA2R field polynomials, original signed position polynomials and outgoing radii, certified harmonic models on the same elapsed clock, unchanged action records, and the physical interpretation of their density and speed columns. |
| Produces | Pointwise physical bounds for 96 original action panels at row 16, a four-polynomial harmonic identity, and a reusable signed-pair proof producer. |
| Difficulty | The speed bound is sensitive to cancellation between the toroidal field and the mirror height. Computing the seven harmonics at one physical angle retains enough accuracy to recover the original digits. |
| Status | Verified for both directions of row 16. The full signed cover remains open. |
| Lean evidence | On demand. `DommaschkNativePhysicalPanelsForward016.physical`, `DommaschkNativePhysicalPanelsBackward016.physical`, `DommaschkHarmonicHorner.expand_sound`, `DommaschkNativeActionGeometry.compensated_numerator` and `DommaschkNativeActionControls.unreversed_record_differs`. |
| Audit evidence | Physical panel declarations report only `propext`, `Classical.choice` and `Quot.sound`. Both content keys appear below. |
| Last updated | 25 November 2026 |

## Physical statement

All quantities use the dimensionless QA2R field and its geometric toroidal angle. Let $h=5300546391395933/5000000000000000$, let $t\in[16/64,17/64]$ be the elapsed outward angle, and let $s=128t-33$. For $n=0,\ldots,47$, assume $s\in[2n/48-1,2(n+1)/48-1]$. The forward physical angle is $\phi=t$, the backward angle is $\phi=-t$, and each physical panel has width $1/3072$ radians. The first forward panel uses record 0 of block 341. The same elapsed-time panel on the backward trace uses record 47 of block 308. In general these indices are $n$ and $47-n$. [Action archive](../../PlasmaLean/Design/DommaschkActionQ0R470.lean)

Suppose $x=(R,z)$ belongs to the signed outgoing physical tube at $t$. Let $a,g,y$ denote the unsigned 24-bit density, squared-speed and speed digits of the corresponding record. The field at $(R,\phi,z)$ obeys

$$
  \frac{R\lVert B\rVert}{B_\phi}\le \frac{a}{2^{20}},
  \qquad
  \max\{2(h-\lVert B\rVert),0\}\le \frac{g}{2^{26}} .
$$

The digit $y$ is the least nonnegative integer with $g\,2^{14}\le y^2$. N-86 identifies the first quantity with Cartesian arclength per radian along a positive-radius field line with positive toroidal field. N-90 already supplies a single birth trajectory satisfying all original panel conditions on the two launch-adjacent blocks 324 and 325. Row 16 adds another 96 certified panel bounds, with intervening blocks still required for a continuous cover from launch. [Physical arclength identity](../../PlasmaLean/Design/DommaschkPhysicalActionPanel.lean) · [Launch-adjacent cover](dommaschk-two-physical-action-blocks.md)

| Direction | Compiled physical theorem | Content key |
| --- | --- | --- |
| Forward | `DommaschkNativePhysicalPanelsForward016.physical` | `d25cf90bdbbdc77dcba94e5a63ce9e3d654aafa3764bec3357a3c4984b36be83` |
| Backward | `DommaschkNativePhysicalPanelsBackward016.physical` | `64a749c6def1ede9adcd942353c8e96b1fdb82680d070af9e230ec317d351e12` |

## Field and arithmetic certificates

The two pointwise bounds also imply `Cells` for the actual full archive list on any signed physical path that reaches these rows. `DommaschkNativePathCellsPaired016.forward_cells` and `backward_cells` use the same chosen trajectory and certify the two distinct clock orientations. The replay key is `ba0552566b81cc9cb7cdb8904e2a78df81fd8b998e729bd131679531adcee5ca`. [Signed cells on a path](../../scripts/dommaschk_kam/verify_native_path_cells.py)

Write $v=R-29/32$ for the spatial displacement. Each exact polynomial $D,n_R,n_Z$ equals a sum of seven bivariate polynomials in $(v,z)$, weighted by $1,\sin(2\phi),\cos(2\phi),\sin(4\phi),\cos(4\phi),\sin(6\phi),\cos(6\phi)$. The three expansions have 215, 224 and 200 nonzero spatial coefficients respectively. A fourth checked expansion represents $C=D-kR^7$ with $k=5297961656084411/5000000000000000$. The proof expands the seven channels and compares every rational coefficient against the identified physical polynomials. It uses the actual correlated harmonics of one angle. [Exact angular identity](../../PlasmaLean/Design/DommaschkHarmonicHorner.lean) · [Field model producer](../../scripts/dommaschk_kam/verify_native_action_models.py)

The original signed position polynomials and their respective outgoing radii enclose every admitted point on the whole time slab. Nested Horner evaluation first uses $v$ and then $z$. Each time-polynomial product retains degree seven and pays for all dropped terms and rounding on the $2^{-80}$ grid. The five resulting models enclose $D,R^8,R^{16},R^{16}\lVert B\rVert^2,R^{16}(h^2-\lVert B\rVert^2)$. Forming $C$ before evaluation retains the cancellation in the last quantity. Physical model keys are `9a2fae1312530e962a522780c5de4cb0d313ecc1d22cc2958a5aa96066dab10f` forward and `19f43d19a38301bc74de72b888a3ffa1209da47b60febde9524b2c2a4107ed60` backward. [Horner model checks](../../PlasmaLean/Design/DommaschkNativeActionModel.lean) · [Physical numerators](../../PlasmaLean/Design/DommaschkNativeActionGeometry.lean)

Fixed-point Horner bounds on each closed panel use a $2^{-52}$ interval grid. The checker verifies both square-root endpoints by integer inequalities, proves the division denominators positive, clips the speed at zero and compares the directed results with the original digits. On actual row-16 data, reversing the backward panel order gives the matching record and omitting reversal changes it. Decreasing the upper speed digit by one fails the square test. Increasing it by one passes that test and fails the adjacent-integer minimality test. [Interval checks](../../PlasmaLean/Certificates/NativeActionInterval.lean) · [Directed digits](../../PlasmaLean/Certificates/NativeActionColumns.lean) · [Negative controls](../../PlasmaLean/Design/DommaschkNativeActionControls.lean)

## Reuse across the remaining blocks

For outward rows 1 and 17 a single forward-oriented model encloses both physical signs. Its input radius is the larger of the two actual outgoing radii. The two coordinate checks independently use each stored row. For the backward row they identify the reflected height and use exact QA2R field-strength and denominator symmetry. The on-demand declarations are `DommaschkNativeActionPaired001.physical`, `DommaschkNativeActionPaired001.backward_physical` and the corresponding pair ending in `017`. A shared model proof supplies the five physical quantities needed by the subsequent 48-panel check. [Physical reflection](../../PlasmaLean/Design/DommaschkNativeActionReflection.lean)

An independent exact Python replay finds that across all 325 outward row pairs, enlarging to the maximum of the two recorded outgoing radii preserves **every one of the 93,600 archived digits** after reversal of the backward records. This is 31,200 cells and 650 complete 3,456-bit blocks. The independent direct replay also reproduces every original block using its own signed outgoing radius. The compressed signed trajectory input has SHA-256 `203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d`. These checks establish the feasibility of completing the full archive with 325 spatial field evaluations. [Paired replay](../../scripts/dommaschk_kam/screen_paired_action_archive.py) · [Original directed replay](../../scripts/dommaschk_kam/replay_physical_action_archive.py)

The remaining physical application requires all panel inequalities in chronological order, a single signed trajectory covering the two mirror brackets and the full `MirrorActionQuadrature.Covers` premise of N-82. That application concerns one dimensionless launch and one upper action comparison. A thermal operating point and the remaining launch/height comparisons are separate open inputs. [Whole-archive implication](dommaschk-complete-sublevel-archive.md)

## Reproduce

Run from the repository root with the workstation Python environment. The first command prepares the data and analytic imports used by the generated proofs.

```sh
lake build PlasmaLean.Design.DommaschkNativeActionReflection PlasmaLean.Design.DommaschkNativeActionColumns PlasmaLean.Design.DommaschkNativeActionControls PlasmaLean.Design.DommaschkHarmonicBlock02 PlasmaLean.Design.DommaschkPositionFramesFwd PlasmaLean.Design.DommaschkPositionFramesBack
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_native_physical_action_panels.py --row 16 --workers 2 --output /tmp/qa2r-row16-panels.json
lake build PlasmaLean.Certificates.NativeActionArchivePair
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_native_path_cells.py --row 16 --output /tmp/qa2r-row16-path.json
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_native_action_models.py --row 17 --paired --output /tmp/qa2r-row17-pair.json
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/screen_paired_action_archive.py
```

The signed-pair campaign writes an atomic manifest for each accepted pair, checks dependency and artifact hashes when resuming, and records the exact standard-axiom audit for each public physical theorem. The resource-limited workstation command builds up to ten pairs concurrently while reserving memory and CPU for propagation. A representative model pair used about 88 single-core seconds, with a peak working set of about 3.8 GiB per Lean invocation. [Campaign runner](../../scripts/dommaschk_kam/verify_native_action_campaign.py)

```sh
lake build -Kjobs=2 PlasmaLean.Design.DommaschkHarmonicTrace
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_native_action_campaign.py --range 0 324 --baseline 2 --workers 10 --reserve-gib 32 --reserve-cores 2 --output /tmp/qa2r-shared-models.json
```
