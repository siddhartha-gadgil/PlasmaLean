# Field strength before the first mirror brackets at all four opposite-section launches

All 2,586 original incoming signed slab tubes at section $\pi/2$ have field strength strictly below the lower archived mirror height. For each launch and each sign this excludes any earlier mirror up to the first time of the lower bracket, provided the trajectory passes through these tubes. The field bounds hold at every real time and every position in the stated tube. The current attachment to actual field lines on one embedded torus pair runs to the angles in the third column. [Grouped physical proof and replay](../../scripts/dommaschk_kam/verify_opposite_incoming_fields.py) · [Strict physical cap signs](opposite-section-physical-mirror-caps.md)

| Radial label | Checked incoming slabs each way | Slabs on actual births each way in the 1,720-step common family | Ordered signed proof |
| --- | ---: | ---: | --- |
| 0.456 | 320 | 48 | `9809930842f254afcd015193466b18f7de212e7d80920dc49cd4ec20b8db2108` |
| 0.464 | 321 | 16 | `5fa5cf11141bdbe5206a8eb30c24aa189bbcb13612b7694c26ec0e98eeec0634` |
| 0.509 | 326 | 8 | `d1120dee62ce21ab7660915d66df57dc57b31af45812643312a583da068512f3` |
| 0.517 | 326 | 5 | `4d2c3f7f78307218fae4938fa88895f934c8c3f0a04254cffe700a10b31187fc` |

Every slab spans $1/64$ radian. The proof uses 25 groups. Within each group, a common polynomial enclosure of the signed trigonometric and spatial data bounds the scaled physical squared-strength gap strictly below zero. Each original signed slab is then checked against its enclosure. Splitting the rows first by elapsed time, then by radial label where needed, retains the strict sign close to the mirror threshold. Each of the four ordered Lean packages verifies both clocks without filling an untested gap by symmetry. [Harmonic strength model](../../scripts/dommaschk_kam/verify_harmonic_group_exclusion.py)

The four ordered proofs and signed endpoint cap data leave one main finite input for the measure-based first-mirror result at each of these radii. The original signed ODE must reach beyond the upper cap, respectively 328, 329, 335 and 336 slabs from section $\pi/2$ on each clock. Until that point the sections farther along the ordered field proof refer to certified tubes. [Topological and measure results for first contact](first-mirrors-regular-values.md) · [Signed continuation campaign](signed-moving-frames-beyond-mirror-caps.md)

The joint birth declaration is `DommaschkOppositeSubmirrorBirths391_328_48_16_48_16_8_5From320_321_326_326.from_common_tori` with key `e0f5d060c584a161d3bb3295b4a9b035637a81f0ce5e2610e03104892c41fecd`. It binds the two signs at all four radii to the calibrated family, and observes the shorter of the ODE length and the ordered field cover at each label. [Earlier opposite-section births](opposite-section-submirror-births.md)

## Replay

~~~bash
.venv-ws/bin/python scripts/dommaschk_kam/verify_opposite_incoming_fields.py \
  --workers 3 --calibrated /tmp/plasma-calibrated-at-328.json \
  --output /tmp/plasma-opposite-incoming-full-at328.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-155 |
| Kind | Ordered physical field certificates and a four-birth attachment |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-133, N-138, N-153 |
| Dependency requirement | Original signed tubes, common harmonic field models and a calibrated common set of birth trajectories |
| Produces | Complete signed incoming field exclusions at all four opposite launches, plus physical exclusion over their attained common-family prefixes |
| Status | All incoming tube signs and the stated physical prefixes are kernel verified. |
| Lean evidence | Four generated ordered submirror packages and the common-birth declaration above |
| Audit evidence | The ordered packages and the common-family attachment use propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
