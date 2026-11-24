# Lower action quadrature on the second phase-zero trajectory

At the QA2R launch radius $239/500$, the application needs the one-way action between the two first mirrors to **exceed** the target $J_* = 6799610938322487/5000000000000000$ at the upper height $h_U=5300546391395933/5000000000000000$. The central 322 outward slabs in each direction already contain enough lower rectangle mass. This window ends before either upper-height mirror, whose outward angle lies between $325/64$ and $327/64$ on a trajectory that reaches the verified brackets. All quantities are dimensionless. [Mirror brackets](secondary-qa2r-mirror-brackets.md) · [First-mirror branch](secondary-first-mirror-height-band.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-134 |
| Title | Lower action quadrature on the second phase-zero trajectory |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-94, N-101, N-115, N-121, N-127 |
| Dependency requirement | The original lower quadrature packet, forward and backward actual field models, and the continuous signed field line from an admitted birth. The full first-well application also requires reaching both upper-height contacts. |
| Produces | Closed lower mass of the full and truncated archive under their physical cell hypotheses, a signed physical lower-cell checker, four verified pairs of rows, and a common-birth application for two pairs. |
| Difficulty | The lower clipped-speed and arclength columns have directed rounding at each division and square root. Chronological indexing reverses the negative branch. |
| Status | Verified on the stated cell samples and birth checkpoint. The complete physical first-well lower bound remains conditional. |
| Lean evidence | `DommaschkSecondaryActionMass.floor_of_cover`, `DommaschkSecondaryActionCore.floor_on_enclosing_interval`, the generated `DommaschkLowerCellsQ0R478NNN.forward_cells` and `.backward_cells`, and `DommaschkLowerActionBirthQ0R478096R5f876504b1c8.from_nested_tori`. |
| Audit evidence | Both signed applications at all four samples and the common-birth application use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## How much of the well is needed?

For a symmetric window reaching $n/64$ in either direction, the quadrature takes the $2n$ contiguous chronological blocks centered at the launch. Each block contains 48 panels of width $1/3072$. The table gives the lower rectangle sum after both speed and density have been rounded down. [Original lower packet](../../PlasmaLean/Design/DommaschkActionQ0R478.lean) · [Verified inner sums](../../PlasmaLean/Design/DommaschkSecondaryActionCore.lean)

| Slabs per direction | Exact lower rectangle sum | Sum minus $J_*$, approximately |
| --- | --- | --- |
| 321 | $573991600928383/422212465065984$ | $-0.000436980$ |
| 322 | $1148484200086339/844424930131968$ | $+0.000156322$ |
| 327 | $383207832386575/281474976710656$ | $+0.001505520$ |

Each archived contribution is nonnegative, so 322 is the smallest symmetric whole-slab count giving this comparison. For physical continuous inputs on a well $[l,r]$ containing $[-322/64,322/64]$, the lower cell hypotheses on the central 644 blocks imply

\[
 J_* < \frac{1148484200086339}{844424930131968}
 \le \int_l^r w(t)\sqrt{2(h_U-f(t))}\,dt .
\]

Here $f$ is field magnitude, $w$ is arclength density, and the real square root clips nonpositive kinetic energy to zero. The proof uses monotonicity of the integral of a nonnegative function under interval inclusion. This permits the first-well application to use only the strictly interior core. The separate full-packet theorem gives its exact larger mass as a lower bound for the integral on the full interval $[-327/64,327/64]$ once its complete physical cover is supplied. [Generic lower cover](../../PlasmaLean/Certificates/NativeLowerAction.lean) · [Full-packet mass](../../PlasmaLean/Design/DommaschkSecondaryActionMass.lean)

## Signed physical cells

The exact Python replay checks the three 24-bit digits of every original cell against the individual signed trajectory, and independently checks them using a shared Taylor model with the larger of the two outgoing radii. All 31,392 comparisons of 72-bit packed cells agree, including the reversal of each negative-time block. The Lean producer reconstructs the five physical Taylor models with 80-bit coefficients. On each of the 48 closed subintervals it checks 52-bit outward-rounded Horner evaluation, the positive divisors, the floor of the lower density and squared-speed columns, and the integer square root for the lower speed. The resulting theorems use the actual field magnitude and arclength density throughout the position tube. [Exact scan](../../scripts/dommaschk_kam/screen_secondary_action_archive.py) · [Lean proof producer](../../scripts/dommaschk_kam/verify_secondary_action_cells.py)

| Outward index | Original negative / positive chronological blocks | Physical proof key prefix |
| --- | --- | --- |
| 0 | 326 / 327 | `4c9b3979b24ab186` |
| 16 | 310 / 343 | `fea0905129b5f47d` |
| 317 | 9 / 644 | `28f325f1a5fec210` |
| 326 | 0 / 653 | `61c95059df645b6a` |

These eight physical block theorems account for 384 original closed panels. At the 96-slab checkpoint, the launch and bulk rows account for 192 panels on **one and the same** signed solution from the physical approach of every admitted birth, on one pair of nested Q-16 field tori. The two near-mirror samples give the local tube implications for each sign. A complete first-well application still requires a signed trajectory through the brackets and a physical cover of all 644 interior blocks on that trajectory. [Birth attachment](../../scripts/dommaschk_kam/verify_secondary_action_birth.py) · [Earlier upper-action computation at the inner radius](dommaschk-native-first-well-action-enclosure.md)

## Reproduction

Run from the repository root on the workstation with the Lean dependencies built. The 96-slab prefix receipt comes from the second-endpoint trace campaign. The four-row verification command compiles the integer evidence and the physical theorems using one worker. The final command selects the two row pairs available on that signed prefix.

```bash
lake build PlasmaLean.Design.DommaschkSecondaryActionCore PlasmaLean.Design.DommaschkEndpointMirrorBranch
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
.venv-ws/bin/python scripts/dommaschk_kam/screen_secondary_action_archive.py \
  --output /tmp/plasma-q0r478-native134-screen.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_cells.py \
  --rows 317 0 326 16 --output /tmp/plasma-q0r478-lower-cells-sample.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_birth.py \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/096.json --rows 0 16 \
  --output /tmp/plasma-q0r478-lower-action-birth096.json
```

The signed-prefix key is `9ea5807d84173a3007d21b8114bbf5b954cfe8769936517d59fa9176a969f22b`. The checked same-birth application has key `27d108a31fa20feac4302cb2753f192e64574737e8b74c46b081ff063e392b93`. To verify the full set of interior row pairs, pass `--range 0 321` to the cell producer. It authenticates and reuses completed modules. Per-row receipts appear in `.lake/secondary-lower-action/rows/` as each pair passes.
