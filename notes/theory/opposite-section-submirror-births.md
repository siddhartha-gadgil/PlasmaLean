# Four opposite-section births stay below mirror strength

Let $h_L=5297961656084411/5000000000000000$ be the lower QA2R mirror height. There is a pair of nested embedded invariant tori with the certified rotational transforms such that the following statements hold simultaneously.

* For every $|\phi-\pi/2|\le 2^{-20}$ and each radial label in the table, the field line from the torus-interpolated birth reaches the section at $\pi/2$. Writing $t$ for signed azimuth from that section, its physical strength satisfies $|B(\pi/2+t)|<h_L$ on the indicated closed interval. Both signed paths solve the field-line equation and meet at the actual incoming section state.
* On the same two surfaces, the pilot at radius $0.470$ has the first-well action and flight bounds of N-130 at every admitted phase-zero launch angle. [Pilot calibration](common-torus-pilot-action.md)

| Opposite-section radial label | Physical interval in radians | Original tubes with strict strength sign, per direction |
| --- | --- | --- |
| 0.456 | $[-1/4,1/4]$ | 16 |
| 0.464 | $[-5/64,5/64]$ | 16 |
| 0.509 | $[-5/64,5/64]$ | 16 |
| 0.517 | $[-5/64,5/64]$ | 16 |

Each physical interval excludes a first mirror there for every height $h\ge h_L$. The intervals are limited by the signed through-birth paths in the stated family. The remaining checked tubes can be used as soon as the original paths extend to them. Together with the four phase-zero results, all eight launch sectors now have a checked initial physical interval below the lower height. [Phase-zero births](outer-phase-zero-submirror-births.md) · [Full pilot](full-signed-pilot-birth.md)

## Why one field calculation suffices

For the forward trace take $\theta=\pi/2+t$. Reflect the backward vertical coordinate and take $\theta=t-\pi/2$. Both transformed harmonic pairs equal $(-\cos(2t),-\sin(2t))$. The two archived spatial rows have independent coefficients and error radii. At each time, an affine change of the polynomial clock places each original spatial row and harmonic pair inside one common Taylor enclosure. Field reflection then recovers the strength at the original backward position. This checks four radii, two directions and sixteen rows, or 128 original tubes. The certified upper bound on $R^{16}(|B|^2-h_L^2)$ is $-881602140921957116873/1208925819614629174706176$, and $R>0$ on every tube. [Lean field and trajectory lemmas](../../PlasmaLean/Design/DommaschkOppositeMirrorExclusion.lean)

## Reproduction

Build the heavy module and reproduce the calibrated eight-sector receipt from N-130. With its path in `calibrated`, run

```sh
lake build PlasmaLean.Design.DommaschkOppositeMirrorExclusion
.venv-ws/bin/python scripts/dommaschk_kam/verify_opposite_submirror.py \
  --calibrated "$calibrated" --workers 2 --output /tmp/opposite-submirror.json
```

The producer checks every original row against the shared enclosure. It then generates four theorems that accept any matching signed passage and one theorem on common tori. For the N-130 family with 1,046 signed slabs, the combined theorem is `DommaschkOppositeSubmirrorBirths391_64_32_5_16_5_5_5.from_common_tori`. Its key is `74ff4bf2e4065646025ad417cb5f7c113ba323f356aebc3bec37e3d1c760dac4`. The group key is `3ab16806a69ddd4b6ea9e0d8bb516cd91be025efbbce1992c71c1e80c0330316`. [Exact producer](../../scripts/dommaschk_kam/verify_opposite_submirror.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-133 |
| Kind | Signed physical mirror exclusion at the opposite section |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-91, N-105, N-120, N-121, N-130 |
| Dependency requirement | Separate original signed position rows, the shared harmonic clock and physical through-birth passages on the calibrated pair |
| Status | Implemented for all four initial intervals and all 128 listed tubes |
| Lean evidence | `FitsRow.below`, `from_passage`, four generated passage implications and `from_common_tori` |
| Audit evidence | All five final declarations use only `propext`, `Classical.choice` and `Quot.sound` |
| Follow-up | Extend the signed through-birth paths and locate their first mirror contacts |
