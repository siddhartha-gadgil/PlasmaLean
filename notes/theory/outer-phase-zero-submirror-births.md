# Two outer phase-zero radii stay below the first mirror height

The two QA2R launch parameters $u=523/1000$ and $u=531/1000$ specify different births between the same nested invariant tori. The archived lower mirror height is $h_L=5297961656084411/5000000000000000$. A submirror certificate asserts the strict inequality $|B|<h_L$ on every point of a signed time interval. It excludes an earlier mirror there for every height $h\ge h_L$. Time in this note is the azimuthal difference from the section, measured in geometric radians. [QA2R birth geometry](../../PlasmaLean/Design/DommaschkFrameLaunch.lean)

For each birth azimuth $|\phi|\le2^{-19}$, the physical field line approaches section zero from the parameterized birth and then runs in both directions from its actual incoming section state. The positive and negative portions meet at that state. The verified inequalities hold for every azimuth on the closed physical intervals below. The shared-torus theorem chooses the two embedded invariant tori before the azimuth and the discrete radius labels. Each radius has its own actual field line. [Signed birth attachment](../../scripts/dommaschk_kam/verify_secondary_submirror_birth.py) · [Common embedded tori](../../scripts/dommaschk_kam/verify_common_submirror_births.py)

The finite tube and long physical trajectory have separate evidence. The grouped checker binds a shared affine time coordinate to every original outgoing row on both signs, with the radius, vertical coordinate, sine and cosine evaluated at the same time. It then checks the exact sign of the physical squared-strength difference, whose radial factor is positive. The physical birth attachment matches that ordered list against the actual forward and backward ODE proofs for the same launch record. [Grouped enclosure method](secondary-qa2r-submirror-exclusion.md)

## Checked physical intervals

| Launch parameter | Physical azimuth interval relative to section zero | Through-birth proof key |
| --- | --- | --- |
| $478/1000$ | $[-1,1]$ | `d5dbcaa27b47b334cd643cb146b53b08433e212e27b5cd910a4f1e76a9d148bd` |
| $523/1000$ | $[-1/2,1/2]$ | `8084ba7ca15b8947194256436aa15e31068cdfdb23d13d5c7ce8dc631b718193` |
| $531/1000$ | $[-5/64,5/64]$ | `47a690240a51de60cd3eb6bafa3b8a3492540003c41d6ea376a5bc9383edd9bf` |

The theorem `DommaschkCommonSubmirrorQ0R478N064Q0R523N032Q0R531N005.from_common_tori` packages all three intervals with common nested, embedded KAM tori and every admissible birth angle. Its proof key is `281b0a69872cba704661b4362dea51cd65aec575778f10f368b685779de35ec1`. The three individual physical paths have different launch parameters and can be chosen after the angle. Each row package and the combined theorem use only `propext`, `Classical.choice` and `Quot.sound`. Lean rejected an attempt to feed the $531/1000$ entry to the $523/1000$ birth theorem. The full incoming tube and through-birth results at the two additional radii are under verification.

## Reproduction

The signed propagation receipts identify their archive, checked row lists and actual starting section. For each radius and matching signed length, run the following commands with the corresponding paths.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_mirror_exclusion.py \
  --launch "$radius" --prefix-length "$length" --workers 1 --output "$early"
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_submirror_birth.py \
  --launch "$radius" --signed "$signed" --exclusion "$early" --output "$birth"
.venv-ws/bin/python scripts/dommaschk_kam/verify_common_submirror_births.py \
  --births "$birth478" "$birth523" "$birth531" --output /tmp/common-submirror-births.json
```

Run `verify_grouped_mirror_exclusion.py --launch 523 --workers 1 --output /tmp/q0r523-exclusion.json` and the corresponding command at 531 to produce the complete incoming tube exclusions. The two records begin their lower-height brackets at $322/64$ and $323/64$, respectively. Every replay builds exact Taylor and row-binding proof terms and audits the final theorem's axioms. [Exclusion archive producer](../../scripts/dommaschk_kam/verify_grouped_mirror_exclusion.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-131 |
| Kind | Phase-zero QA2R physical submirror intervals at additional radii |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-91, N-121 and the corresponding signed physical endpoint prefixes |
| Dependency requirement | The archived field model encloses both directions on each closed slab and the signed physical entry uses the identical original rows |
| Status | Implemented for the three closed signed intervals in the table |
| Lean evidence | `DommaschkQ0R523SubmirrorBirth032.from_birth`, `DommaschkQ0R531SubmirrorBirth005.from_birth` and `DommaschkCommonSubmirrorQ0R478N064Q0R523N032Q0R531N005.from_common_tori` |
| Audit evidence | Authenticated independent radius archives, both actual physical directions, common embedded surfaces, three standard axioms and rejection of a wrong-radius section entry |
| Last updated | 25 November 2026 |
