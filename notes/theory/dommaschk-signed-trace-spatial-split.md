# A signed three-radian field line and a split Jacobian at slab 226

For every Q-16 launch at section zero, radius 0.470 and phase magnitude at most $2^{-19}$, a single dimensionless magnetic field line through the transferred birth covers $[-3/2,3/2]$ in signed toroidal angle. Each of the 192 reference slabs has a uniform Euclidean position error at most $2678772121456213228/2^{80}<2.216×10^{-6}$. The forward maximum numerator is 2678772121456213225. The backward maximum is three units larger and supplies the paired estimate. [Signed proof generator](../../scripts/dommaschk_kam/verify_paired_physical_prefix.py)

Farther along the same archive, slab 226 needs a narrower spatial enclosure. For a Taylor polynomial with a uniform vertical error, two closed half-intervals of error cover the original interval, including their common boundary. Applying this fact pointwise divides the projected trial rectangle into two vertical boxes. Lean checks the denominator remains positive and the moving-frame growth bound holds on each half using eight time panels. The union gives the growth bound on the entire rectangle. The forward and reflected backward field-line steps through that slab are now proved from every state in their respective entrance ellipsoids. To apply either step to a given birth requires the intervening slabs. [Interval cover](../../PlasmaLean/Certificates/DyadicTaylorCover.lean) · [Split certificate generator](../../scripts/dommaschk_kam/verify_vertical_split_jacobian.py)

## Reproduce

For the signed 96-slab result, follow N-75 with length 96 in each directional verifier and use the resulting manifests as the inputs to the paired verifier. Supply the ordinary shared-power Jacobian certificates through row 95 except for the time-panel and projected rows listed in N-74.

For the separate step at index 226, prepare its harmonic block (28), central defect and the projected-trial dependencies in N-74/N-75, then run:

```sh
lake build PlasmaLean.Certificates.DyadicTaylorCover
.venv-ws/bin/python scripts/dommaschk_kam/verify_vertical_split_jacobian.py --part lower
.venv-ws/bin/python scripts/dommaschk_kam/verify_vertical_split_jacobian.py --part upper
.venv-ws/bin/python scripts/dommaschk_kam/verify_vertical_split_jacobian.py --part physical
.venv-ws/bin/python scripts/dommaschk_kam/verify_backward_physical_prefix.py --row 226 --vertical-split 226
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-76 |
| Kind | Physical field-line and Jacobian certificates |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-66, N-74, N-75 |
| Dependency requirement | Authenticated reference defect, signed rates on the full spatial cover, and compatible ellipsoids at each join. |
| Produces | One connected trajectory through 96 slabs each way and individual physical steps at slab 226 in both directions. |
| Difficulty | Connecting the intervening physical steps to the mirror brackets. |
| Status | Lean-verified for this launch family. |
| Lean evidence | On demand: `DommaschkPairedPrefix096.exists_nested_paired`, `uniform_paired_error`, `DommaschkPhysicalForward226.physical_step`, `DommaschkPhysicalBackward226.physical_step`. |
| Audit evidence | Paired `e9b226612cdf` from forward `3644a7efae68` and backward `92ebf63d1c2e`. Split union `a80e4cf5c8c6`, forward step `226f0bde8d85`, backward step `8cf331bc351d`. The heavy library audit over 94,989 declarations passed. |
| Last updated | 24 November 2026 |
