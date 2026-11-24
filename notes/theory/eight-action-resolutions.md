# How many physical action panels do the eight endpoints need?

Each endpoint compares the one-way, dimensionless action to $J_*=6799610938322487/5000000000000000$. The original packets use 48 subintervals per signed slab. Twelve physical subintervals suffice at six endpoints, and sixteen suffice at the other two. The eight coarser packets together require **67,928 physical subinterval enclosures**, down from 250,848. Lean checked the direction of every proposed square-root bound, the exact weighted totals and the eight implications from a physical cover to the required action inequality. The actual position tubes and the full signed path still have to supply each cover. [Exact packet producer](../../scripts/dommaschk_kam/verify_coarse_action_packets.py)

| Section | Radius | Physical height | Required comparison | Panels per slab | Physical panels | Margin past $J_*$, rounded |
| --- | --- | --- | --- | ---: | ---: | ---: |
| 0 | 0.470 | Upper | $J<J_*$ | 12 | 7,800 | 0.000394420 |
| 0 | 0.478 | Upper | $J>J_*$ | 16 | 10,464 | 0.000346574 |
| 0 | 0.523 | Lower | $J<J_*$ | 12 | 7,776 | 0.000249806 |
| 0 | 0.531 | Lower | $J>J_*$ | 16 | 10,400 | 0.000414207 |
| $\pi/2$ | 0.456 | Upper | $J<J_*$ | 12 | 7,872 | 0.000987281 |
| $\pi/2$ | 0.464 | Upper | $J>J_*$ | 12 | 7,896 | 0.000295836 |
| $\pi/2$ | 0.509 | Lower | $J<J_*$ | 12 | 7,848 | 0.000874222 |
| $\pi/2$ | 0.517 | Lower | $J>J_*$ | 12 | 7,872 | 0.000342615 |

The screen evaluates the physical Taylor models separately on each coarse subinterval for each signed branch. At the opposite section it uses the original section-dependent harmonic coefficients. At the start, midpoint and end of each branch it also reproduces all 48 original archived digits for density, squared speed and speed. Two, four and eight panels per slab miss the target at every endpoint with this direct enclosure. The counts in the table are the first successful resolutions among 2, 4, 8, 12 and 16. [Exact resolution screen](../../scripts/dommaschk_kam/screen_action_panel_resolution.py)

The kernel uses the existing 48-cell format by repeating each checked coarse digit four or three times. The simulated enclosure is defined on the whole larger subinterval, so one physical proof can serve those four or three consecutive cells. The aggregate comparison at each endpoint assumes the physical cover of its complete packet, continuity of both physical profiles and nonnegative arclength density. Its independent arithmetic theorem uses only `propext`. Its integral theorem uses `propext`, `Classical.choice` and `Quot.sound`. [Quadrature semantics](../../PlasmaLean/Certificates/MirrorActionQuadrature.lean)

## Which part of a well proves a lower bound?

For the original lower-action archives let $M_e(k)$ be the normalized rectangle sum of the $k$ signed slabs nearest the birth on **each** side. Lean proves $M_e$ is nondecreasing, identifies the original contiguous chronological slice, and proves $M_e(k)<J_*$ for every smaller symmetric window than the one in the table. On the listed window $M_e(k)>J_*$. For any physical first well containing this interval, its action is at least $M_e(k)$ once the interior cells and the nonnegative continuous arclength density have been verified. This uses nonnegativity of the action integrand on the omitted collars. [Reusable first-crossing and integral theorems](../../PlasmaLean/Design/DommaschkLowerActionWindows.lean)

| Radius | Archived slabs per side | First sufficient $k$ | Exact original lower mass $M_e(k)$ | Excess over $J_*$ |
| --- | ---: | ---: | --- | ---: |
| 0.478 | 327 | 322 | $1148484200086339/844424930131968$ | 0.000156322 |
| 0.531 | 325 | 321 | $765884512546961/562949953421312$ | 0.000562004 |
| 0.464 | 329 | 325 | $1148689030526513/844424930131968$ | 0.000398889 |
| 0.517 | 328 | 323 | $574189753884545/422212465065984$ | 0.000032341 |

The first table changes the physical panel resolution on the full archived interval. The second keeps the original 48-cell rule and shortens the integration interval for lower bounds. Its cutoffs concern that particular lower sum. At $u=0.478$, N-138 already attaches part of the original lower cover to a field line from birth. At the pilot $u=0.470$, N-101 has already discharged the full original upper cover on the true first well. [Second lower cover](secondary-action-cover-from-birth.md) · [Pilot upper action](dommaschk-native-first-well-action-enclosure.md)

## Reproduction

```bash
lake build PlasmaLean.Design.DommaschkLowerActionWindows
.venv-ws/bin/python scripts/dommaschk_kam/screen_action_panel_resolution.py \
  --splits 2 4 8 12 16 --output /tmp/qa2r-action-resolutions.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_action_packets.py \
  --workers 2 --output-dir /tmp/qa2r-coarse-action-packets
```

Each JSON receipt includes the input and original action archive hashes, the exact rational mass and margin, the package and module names, the generated proof hash and the two separate axiom checks. The packet declarations are called `checked` and `endpoint`.

| Endpoint | Audited packet key |
| --- | --- |
| q0r470 | `c9192ca72c4d65f1af4c474fe891ba609a2d9fdc6b24d296fc5df0f15f7bac7b` |
| q0r478 | `822463e39459d515c9dc82bc94cae5818de16304c6e18363f2a7ee0afcd31c60` |
| q0r523 | `b5b98256e5f16e31a7b7b45b0982a9223bb99ccd86971ca6ee7923ef1e54259b` |
| q0r531 | `6fad106a9683ae606e9bdac09d5c7d2ea13765fa80f8e9dfc9d16646c824989d` |
| q1r456 | `bd0307957f8f2b63b64a1e98bb697046c710db9ed1c8acc232731398417f2054` |
| q1r464 | `7833c0f8d53ca97240c32ed77b6457ee7ce140e62c2ddf74fa8483d3d76e7ccc` |
| q1r509 | `c05726f0bbb51e874af4e95e0dde2a1269420918eb38666ddc65719407bd3cef` |
| q1r517 | `7c918f81bed4f1a4b578d0df02f48db47149e5d206ddf4ab017b90778fdbe3dc` |

## Metadata

| Field | Value |
| --- | --- |
| ID | N-139 |
| Kind | Candidate-independent monotonicity argument and eight exact endpoint certificates |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-82, N-94, N-101, N-134, N-138 |
| Dependency requirement | Original independently signed position tubes, correct section and height, positive-weight clipped action and integer square-root witnesses |
| Status | All eight coarse arithmetic packets and conditional integral theorems verified. All four first sufficient original lower windows proved in Lean |
| Lean evidence | `mass_monotone`, `first_crossing`, `at_cutoff`, `action_on_enclosing_interval` and the eight generated `CoarseActionPacketCache` modules |
| Last updated | 25 November 2026 |
