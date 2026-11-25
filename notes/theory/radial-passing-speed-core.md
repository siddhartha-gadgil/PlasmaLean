# A uniform parallel-speed floor along the original radial family

Choose the two original nested embedded invariant QA2R tori of the launch theorem. For every radial label \(u\in[47/100,239/500]\) and phase \(|\phi|\le2^{-19}\), there is one true signed field line through the interpolated birth at its own phase. Its ordinary field-line ODE holds on the closed interval \([-127/64,127/64]\). Throughout \([-59/32,59/32]\) its field strength satisfies \(|B|<132/125\). Consequently, for **every** normalized energy-to-moment ratio \(h\ge h_L\),
\[
\sqrt{2(h-|B|)}>1/12 .
\]
This excludes a turning point anywhere on the indicated part of the orbit, including for the lower archived mirror height. The interval has length \(59/16\) radians. The radius in this statement is a launch label. The proof certifies the state on the propagated field line using the cylindrical tube enclosures. [Passing theorem](../../PlasmaLean/Design/DommaschkRadialPassingCore.lean) · [Original chart and entries](upper-radial-ribbon-entry-and-caps.md)

## Physical proof

The four radial tiles each carry 128 certified ODE slabs in both directions. A joined solution through every point of their original section balls yields the closed ordinary-ODE window, allowing one exterior slab per end. For the first 118 rows on both clocks of all four tiles, 944 exact row exclusions give the stronger threshold \(132/125\). Their proof reuses the squared-field polynomial gap on the signed tubes, with a certified upper radius for the conversion to the lower field threshold. A uniqueness argument identifies the section solution with the original interpolated birth at phase \(\phi\). No through-cap hypothesis appears in this theorem. The calculation supplies an initial nonturning segment; quantifying thermal radial confinement requires the particle dynamics and operating targets. [Physical row and birth verifier](../../scripts/dommaschk_kam/verify_radial_passing_core.py)

## Replay

The 128-row physical join has key `feb07dd3a77cf75d0487342028cea5458ad5d848205f20d57fa3de30b545c14a`. The original-birth theorem has key `aeba1716f57d40c1b0c5976614b3ea54fa5d9f490049e722c8ceaeb4cdbaeece`. Both pass the standard axiom audit. For comparison, the preceding 64-row join gives a speed floor on \(\pm59/64\), with key `d30dd856058bc0775faa11ee3bb45c1503e5abd80a090fb791eea93133ef6ecc`.

```sh
lake build PlasmaLean.Design.DommaschkRadialPassingCore
.venv-ws/bin/python scripts/dommaschk_kam/verify_ribbon_through_chains.py \
  --packets /tmp/plasma-n169-packets.json --count 128 --output /tmp/plasma-n191-through128.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_passing_core.py \
  --ribbon /tmp/plasma-n169-four-ribbons.json --packets /tmp/plasma-n169-packets.json \
  --incoming /tmp/plasma-n172-incoming.json --through /tmp/plasma-n191-through128.json \
  --workers 2 --output /tmp/plasma-n191-core128.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-191 |
| Kind | Unconditional physical trajectory and positive-speed certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-169, N-172, N-175, N-179, N-186 |
| Dependency requirement | Joined signed physical ODEs and exact field gap envelopes covering their actual initial rows. |
| Produces | A positive normalized parallel-speed floor on the physical radial family over a closed angular interval. |
| Status | Lean verified for every original birth in the launch rectangle on the stated window. |
| Lean evidence | `DommaschkRadialPassingCore.passing_of_below`, `.from_seed`, and `DommaschkRadialPassing128Core118.from_nested_tori`. |
| Last updated | 25 November 2026 |
