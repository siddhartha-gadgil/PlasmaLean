# Four physical entry balls and a common high cap for the upper radial bracket

Every interpolated phase-zero birth with $47/100\le u\le239/500$ and $|\phi_0|\le2^{-19}$ reaches one of four explicit Euclidean balls at the zero section. Lean proves these entries on the same nested embedded invariant tori that supply the eight endpoint entries. The radius of each ball is $2^{-16}$. The actual field line from the section exists in both directions for at least $1/32$ radian. [Birth-to-section proof](../../PlasmaLean/Design/DommaschkRadialRibbonEntry.lean)

The four closed radial intervals have centers $471/1000$, $473/1000$, $475/1000$ and $477/1000$, with half-width $1/1000$. Each seed is a dyadic interpolation of the recorded endpoint centers. The exact Q-16 Fourier launch and short physical transfer give coordinate errors at most $1/80000$ radially and $1/1000000$ vertically. Their Euclidean combination fits the proposed ball. This argument applies to every birth in each tile, including the common boundaries.

## Common physical caps

On the forward and backward clocks, the chosen cap is $b=331/64$. Lean proves $|B(\pm b,x)|>h_U$ for every point in each of the eight specified physical cap tubes. The proof checks the three original QA2R field polynomials, their positive-sign inequality at the actual trigonometric phase and the relation of the box to the endpoint of the recorded moving frame. The combined theorem is `DommaschkRadialRibbonUpperCaps.above`, with receipt `60546410c61a922926ba0a127eaa38cc16e6c70c43edb50b5ad73e6e1c161e40`. Applying it to a particular interpolated birth at $b$ requires that line’s continued membership in the corresponding tube. [Physical cap proofs](../../scripts/dommaschk_kam/verify_radial_ribbon_caps.py)

## Exact screen for continuation and grazing

At every time slab the reference polynomial and its two endpoint frames are obtained by interpolating the two archived endpoint proposals and rounding to integer dyadic ticks. The verifier re-evaluates the physical ODE defect, the spatial Jacobian on the trial tube, the transfer to the next frame and the field-strength gap on the outgoing tube. Python uses rational or integer arithmetic for all acceptance decisions. The two archived reference traces form the only proposal inputs. [Exact ribbon replay](../../scripts/dommaschk_kam/screen_radial_birth_ribbon.py)

All eight replays cover 340 slabs. On the closed cap slab $[331/64,332/64]$ the squared-strength gap exceeds $7.29\times10^{-5}$ in every tile and direction. Up to that cap, only 70 signed slabs have a squared-strength range that can contain $h_U^2$. On every such slab the exact external lower bound on the outward derivative of $|B|^2$ exceeds $0.0008354$. The maximum outgoing position error through all 340 slabs is less than $0.0000455$.

| Radial tile | Possible upper-height contact indices on each outward clock | First slab entirely above the upper height |
| --- | --- | --- |
| $[0.470,0.472]$ | 321–328 | 329 |
| $[0.472,0.474]$ | 321–329 | 330 |
| $[0.474,0.476]$ | 321–329 | 330 |
| $[0.476,0.478]$ | 322–330 | 331 |

The complete deterministic signed witness has SHA-256 `c4f65ab5d7727fc5fdbae645c6924ecde6b474f521663a8b1b9de6be8d45a486`. The four Lean row packages contain every original coordinate and frame integer, exact defect and logarithmic-norm bound, and incoming, outgoing and trial radii. Their names are `RadialRibbonPacketCache.DommaschkRadialRibbonRows0` through `Rows3`, with `.forwardRows`, `.backwardRows` and `.seed`. Kernel verification of field-line continuation from the four entry balls through the common cap and the oriented contact slabs is a separate application. When combined with continuous dependence on the interpolated physical birth, those inputs give the intermediate action test. [Canonical row packages](../../scripts/dommaschk_kam/verify_radial_ribbon_packets.py) · [Target-or-grazing theorem](../../PlasmaLean/Design/DommaschkRadialActionAlternative.lean)

## Reproduction

```bash
export OPENBLAS_NUM_THREADS=1 LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkRadialRibbonEntry
.venv-ws/bin/python scripts/dommaschk_kam/screen_radial_birth_ribbon.py \
  --stop 340 --output /tmp/plasma-n169-four-ribbons.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_ribbon_packets.py \
  --ribbon /tmp/plasma-n169-four-ribbons.json --output /tmp/plasma-n169-packets.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_ribbon_caps.py \
  --ribbon /tmp/plasma-n169-four-ribbons.json --output /tmp/plasma-n169-caps.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-169 |
| Kind | Physical interval of births, radial-family computation and common-cap verification |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-65, N-120, N-156, N-162, N-167 |
| Dependency requirement | Sharp Q-16 launch profiles and the archived phase-zero endpoint reference polynomials and frames. |
| Produces | Common physical start balls for an entire radial interval, one common pair of field-strength caps, and exact signed ODE proposals through both caps. |
| Status | Birth, true short flows, eight cap signs and row data kernel-verified. Long propagation and orientation checked externally. |
| Lean evidence | `DommaschkRadialRibbonEntry.from_close`, `.from_nested_tori` and `DommaschkRadialRibbonUpperCaps.above`. |
| Audit evidence | Both physical birth declarations and the combined true-field cap theorem use only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
