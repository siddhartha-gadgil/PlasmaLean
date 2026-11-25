# Eight original launches through 2,590 signed physical slabs

The same two embedded QA2R tori now support 2,590 slab proofs on the eight original launch labels, 592 beyond the previous joint checkpoint. One slab advances the geometric azimuth by 1/64 radian. The positive and negative clocks each have their own physical ODE certificate. Every birth in each admitted phase sector is identified with its corresponding position on the same pair of tori. [Previous eight-launch checkpoint](eight-launch-signed-checkpoint.md) · [Reproducible family verifier](../../scripts/dommaschk_kam/checkpoint_signed_family.py)

| Phase centre | Radius label | Slabs in each direction | Angular distance each way |
| --- | ---: | ---: | ---: |
| 0 | 0.470 | 391 | 391/64 |
| 0 | 0.478 | 328 | 41/8 |
| 0 | 0.523 | 224 | 7/2 |
| 0 | 0.531 | 96 | 3/2 |
| π/2 | 0.456 | 96 | 3/2 |
| π/2 | 0.464 | 64 | 1 |
| π/2 | 0.509 | 48 | 3/4 |
| π/2 | 0.517 | 48 | 3/4 |

All four opposite-section trajectories stay strictly below the lower mirror height throughout their listed intervals. The phase-zero margin certificates and the 325 paired field and arclength comparisons at labels 0.470 and 0.478 are attached to these same witnesses. The two inner phase-zero trajectories already reach their mirrors. The six other listed trajectories still end before their mirror brackets. Slab counts here measure verified angular continuation, separately from the four-tile campaign covering every intermediate radial label. [Physical first-well action comparison](two-physical-first-well-actions.md) · [Four-tile criterion](radial-sector-through-trajectory-criterion.md)

## Verification

The common family receipt is `eef9f2fa012a0061e1d974718d519b9dcbede46de095e1878545e8e339446101`. The phase-zero margins, opposite-sector exclusions and paired action inputs have keys `6acec7f034a11acc713b8b3795865ebc900b052e38f516801c064ef61aff1a99`, `f140cc302439accf969d7568ada323d77957aa3d234babb611c650b678e06643` and `0f95b58b7eb9e90f50f98d5bd39c862f5148203e55f9c22dcd00add27ff66b3c`. The six composed receipts use only `propext`, `Classical.choice` and `Quot.sound`.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/checkpoint_signed_family.py \
  --lengths 328 224 96 96 64 48 48 \
  --pilot /tmp/plasma-full-signed391.json --flight /tmp/plasma-action-flight-bounds326.json \
  --clearances /tmp/plasma-n135-q0r478-317.json /tmp/plasma-n135-q0r523-322.json \
    /tmp/plasma-n135-q0r531-323.json --launch-profile /tmp/plasma-paired-action-profile000.json \
  --row-map /tmp/plasma-all325-compared-row-map.json --output-dir /tmp/plasma-n193-common
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-193 |
| Kind | Long signed physical ODE continuation |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-151, N-162, N-174 |
| Dependency requirement | Original common-torus launch identification, independent signed ODE continuations and authenticated rowwise field inequalities. |
| Produces | Eight launch families with 2,590 signed physical slabs and calibrated observables on one common torus pair. |
| Status | Kernel-verified at the stated lengths. Six further continuations are running. |
| Lean evidence | `DommaschkCommonEndpointTraces391_328_224_96_96_64_48_48`, `DommaschkOppositeSubmirrorBirths391_328_224_96_96_64_48_48From320_321_326_326` and `DommaschkComparedBirths325On391_328_224_96_96_64_48_48`. |
| Last updated | 25 November 2026 |
