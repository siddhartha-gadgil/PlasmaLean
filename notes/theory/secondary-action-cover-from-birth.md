# Consecutive lower-action cells on the second birth trajectory

For every admitted phase-zero QA2R birth at radius $239/500$, Lean verifies 1,536 consecutive lower quadrature panels at the upper mirror height on a single physical trajectory. On the signed angular interval $[-1/4,1/4]$, the one-way action satisfies

$$
J_U([-1/4,1/4]) \geq \frac{151485803144663}{1688849860263936}
\approx 0.08969761416 .
$$

The weight in this integral is the norm of the derivative of the Cartesian field line. The approach from the original birth, the section state, the forward and backward ODEs, and every closed quadrature panel use the same solution. The 96-slab signed checkpoint extends beyond both edges of the integration interval. [Physical trajectory interface](../../PlasmaLean/Design/DommaschkLowerActionPath.lean) · [Chronological assembly](../../scripts/dommaschk_kam/verify_secondary_action_cover.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-138 |
| Title | Consecutive lower-action cells on the second birth trajectory |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-94, N-101, N-115, N-121, N-127, N-134 |
| Dependency requirement | The signed second-launch ODE prefix, native lower cells on each included row, and the authenticated upper-height first-mirror branch. |
| Produces | A reusable signed trajectory and row-cover interface, an incremental checker of adjacent original blocks, two complete birth-to-action checkpoints, and a first-well reduction with two explicit remaining inputs. |
| Difficulty | Preserving the physical clock around zero and at adjacent blocks, the original packed list, and the same trajectory from birth through the first mirrors. |
| Status | Lean verified on the stated intervals. The full first-well target is conditional on a complete 644-block cover and a signed trajectory extending beyond the outer brackets. |
| Lean evidence | `DommaschkLowerActionPath.Signed.inputs`, `DommaschkQ0R478BirthCover016Of096.from_nested_tori`, and `DommaschkQ0R478LowerFirstWell.from_passage`. |
| Audit evidence | The on-demand proofs report only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Physical attachment

The two archived branches use outward time. Forward row $i$ contributes chronological block $327+i$. Backward row $i$ contributes block $326-i$ with its 48 panels in reverse order. Each leaf proves the consecutive `Covers false` predicate by checking equality to its slice of the original packed list. Each join identifies the adjacent lists and proves agreement of their rational endpoint clocks. The resulting cover theorem takes only tube membership through its largest row. It can be reused when a longer signed solution becomes available. [Original lower packet and masses](secondary-native-lower-action-cells.md) · [Cover concatenation theorem](../../PlasmaLean/Certificates/MirrorActionBlockBounds.lean)

The separate birth application retains the signed physical ODE at the section as well as on the open halves of the trajectory. The spatial box $7/8\le R\le1$, $|z|\le5/64$ gives the positive toroidal denominator and continuous field magnitude along the same path. This identifies the bounded arclength weight with the norm of the Cartesian derivative throughout the integration interval, including the launch. [Cartesian arclength identity](../../PlasmaLean/Design/DommaschkPhysicalArcTrace.lean) · [Signed spatial box](../../PlasmaLean/Design/DommaschkSignedTraceDomain.lean)

| Rows per side | Signed interval | Original blocks, half-open | Original panels | Exact lower bound |
| --- | --- | --- | --- | --- |
| 8 | $[-1/8,1/8]$ | $[319,335)$ | 768 | $25236716953749/562949953421312$ |
| 16 | $[-1/4,1/4]$ | $[311,343)$ | 1,536 | $151485803144663/1688849860263936$ |

The 16-pair archive theorem has key `78994222dfaf132dca09e6e5523deed8b238f0e948f6ab8efec19614add45707`. The birth application on the 96-slab prefix has key `fdcab163d75ec43c4034a33846ff9bec15d5a7ecf70574a90dd064cf9df19e02`. Both the trajectory hypotheses and all cell hypotheses have been discharged for these two integration intervals.

## What will establish the upper-height comparison?

The compiled theorem `DommaschkQ0R478LowerFirstWell.from_passage` requires a signed passage extending past $327/64$ and the lower cover on original blocks $[5,649)$ for paths tracking the original rows through $322/64$. It proves existence of the same physical birth trajectory and first mirrors $l\in(-327/64,-325/64)$ and $r\in(325/64,327/64)$, with

$$
\frac{6799610938322487}{5000000000000000}
< \frac{1148484200086339}{844424930131968}
\le J_U([l,r]).
$$

The closed core lies strictly inside both first mirrors. Integral monotonicity therefore suffices for the lower comparison. The checker has already established spatial regularity on all 327 rows of each signed branch and attached the cap times to the correct physical first-well component. The conditional theorem and its three supporting declarations have key `ebb5a91ccb0da8f6c8a9aa38aba932adba5d7fe106a7d0cab46417821820d087`. The full concrete application still needs the two stated receipts. [First-well proof](../../scripts/dommaschk_kam/templates/secondary_lower_well.lean.tpl) · [First-well verifier](../../scripts/dommaschk_kam/verify_secondary_first_well_action.py)

## Reproduction

Use the N-127 band receipt, the N-134 physical row receipts, and the signed endpoint prefix. The first command below checks the short-window result. Omitting `--signed` checks the archive cover independently of the available propagation length.

```bash
lake build PlasmaLean.Design.DommaschkLowerActionPath
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_cover.py \
  --band /tmp/plasma-q0r478-all-height-branches.json \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/096.json \
  --pairs 16 --output /tmp/plasma-q0r478-lower-cover016.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_first_well_action.py \
  --band /tmp/plasma-q0r478-all-height-branches.json \
  --output /tmp/plasma-q0r478-first-well-lower-bridge.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_campaign.py \
  --band /tmp/plasma-q0r478-all-height-branches.json \
  --output /tmp/plasma-q0r478-lower-action-assembly.json
```

The campaign waits for complete row sets and checks the 16, 32, 64, 128, 256 and 322-pair windows. It assembles a cover before a sufficiently long physical trajectory becomes available and attaches the birth when the trajectory arrives. With 322 pairs it waits for a signed prefix beyond the outer brackets to produce the complete physical first-well receipt. [Checkpoint campaign](../../scripts/dommaschk_kam/verify_secondary_action_campaign.py)
