# Eight original launches on a common pair of tori through 1,998 signed slabs

For every allowed phase in the two launch sectors, Lean certifies signed physical field lines through all eight corresponding radius labels on one pair of embedded nested invariant tori. The following is a fixed snapshot of the ongoing campaign. One slab advances the toroidal clock by $1/64$ radian. Forward and backward integrations have separate local ODE proofs. [Family verifier](../../scripts/dommaschk_kam/verify_common_endpoint_traces.py)

| Section | Birth label | Slabs each way | Half-length in radians |
| --- | ---: | ---: | ---: |
| $0$ | 0.470 | 391 | 391/64 |
| $0$ | 0.478 | 328 | 41/8 |
| $0$ | 0.523 | 128 | 2 |
| $0$ | 0.531 | 32 | 1/2 |
| $\pi/2$ | 0.456 | 48 | 3/4 |
| $\pi/2$ | 0.464 | 32 | 1/2 |
| $\pi/2$ | 0.509 | 16 | 1/4 |
| $\pi/2$ | 0.517 | 24 | 3/8 |

The previous joint snapshot covered 1,720 signed slabs. The additional 278 are on the same six secondary launches. At the opposite section the strict bound $|B|<h_L$ now holds along the actual field lines through the entire respective intervals in the table. At phase zero the three original nonpilot lines satisfy $|B|<h_L-1/270000$ through $317/64$ radians each way, $|B|<h_L-1/100000$ through 2 radians each way, and $|B|<h_L-1/50000$ through half a radian each way, respectively. The calibrated pilot carries its independently verified action and flight observables. The first two physical launches still carry all 325 pairs of equal-time field and arclength comparisons. [Opposite-section bounds](four-opposite-incoming-field-profiles.md) · [Phase-zero margins](common-original-birth-margins.md)

## Verification and replay

The common trajectory key is `45160c11a3437dd805b2ccf4c9fc7fbf313202bd41a63290f049176c2e35e4bd`. The authenticated phase-zero margins, opposite-section observations and paired comparison have keys `7a34412f2969d3e604e77c2977beacc7b823b4522cfa1538a5743fcf041f7678`, `c7029d54b48c3ce495dcee8955b53d548accde52dbe33a84ea31b18cddaf13bf` and `64b604533c6750c26e2c07a82d14f99971a9f922d5fd42ddcbbddf691fda8fc2`. Each depends only on propext, Classical.choice and Quot.sound.

The replay selects the exact seven secondary prefix lengths, authenticates each parent and rebuilds each derived proof. Omitting the lengths takes a fresh snapshot as the campaign grows. [Replay driver](../../scripts/dommaschk_kam/checkpoint_signed_family.py)

```sh
.venv-ws/bin/python scripts/dommaschk_kam/checkpoint_signed_family.py \
  --lengths 328 128 32 48 32 16 24 \
  --pilot /tmp/plasma-full-signed391.json --flight /tmp/plasma-action-flight-bounds326.json \
  --clearances /tmp/plasma-n135-q0r478-317.json /tmp/plasma-n135-q0r523-322.json \
    /tmp/plasma-n135-q0r531-323.json \
  --launch-profile /tmp/plasma-paired-action-profile000.json \
  --row-map /tmp/plasma-all325-compared-row-map.json --output-dir /tmp/plasma-n174-common
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-174 |
| Kind | Original-field signed ODE and attached observables |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-155, N-158, N-161, N-170 |
| Dependency requirement | Authenticated signed prefixes, original pilot and field-profile certificates. |
| Produces | A reproducible 1,998-slab family, observed phase-zero and opposite-sector margins, and 325 paired comparisons. |
| Status | Verified for this finite eight-launch snapshot. Continued propagation to the remaining mirror brackets is in progress. |
| Lean evidence | Generated `DommaschkCommonEndpointTraces391_328_128_32_48_32_16_24.same_nested_tori`, calibrated family and attached original-field comparison theorems. |
| Audit evidence | Each family and observation receipt has the standard three axioms. |
| Last updated | 25 November 2026 |
