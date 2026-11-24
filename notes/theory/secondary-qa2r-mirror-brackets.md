# Mirror brackets at the second phase-zero launch

At section zero and launch radius $239/500$, take $t\ge0$ to be the outward azimuthal displacement on either signed branch. The physical field magnitude is evaluated at $(R,t,Z)$ on the forward branch and $(R,-t,Z)$ on the backward branch. Lean verifies these strict inequalities for **every point of the indicated closed spatial tube at the indicated time**. [Certificate generator](../../scripts/dommaschk_kam/verify_secondary_mirror_caps.py)

| Tube endpoint | Height | Field strength | Proof key prefix |
| --- | --- | --- | --- |
| Row 0 at $t=0$ | $h_L$ | below | `f6504b1d4b54` |
| Row 317 at $317/64$ | $h_L$ | below | `964196f6d758` |
| Row 317 at $318/64$ | $h_L$ | above | `14ad084dd542` |
| Row 325 at $325/64$ | $h_U$ | below | `41172fb8a634` |
| Row 326 at $327/64$ | $h_U$ | above | `08b824732114` |

The heights are $h_L=5297961656084411/5000000000000000$ and $h_U=5300546391395933/5000000000000000$. Every continuous trajectory enclosed in the indicated slab or pair of slabs encounters the corresponding height strictly between the stated endpoints. The four theorems `DommaschkQ0R478MirrorCrossings.{fwd,back}_{lower,upper}_hit` have aggregate key `bcea821ab1320f4cf141df01aa4b33d62209e90b3f835f606af1cff6d705a5e9`. They allow an arbitrary incoming state for each physical tube.

The checker uses the larger of the two archived outgoing coordinate errors. It proves the sparse polynomials for all three physical field components on that box and retains the common radial variable in the factored squared-strength gap $R^{16}(|B|^2-h^2)$. Section-zero reflection supplies the backward field norm after the exact coordinate centres and radii have been checked. The lower bound on cylindrical radius gives continuity all the way through the middle of the upper bracket. At $326/64$ the gap enclosure from row 325 runs from approximately $-5.78\cdot10^{-6}$ to $3.35\cdot10^{-6}$. The enclosure from row 326 also contains zero. The upper crossing uses the two outside faces without assigning a sign at their seam. [Physical gap identity](../../PlasmaLean/Design/DommaschkMirrorEndpointSign.lean) · [Physical norm continuity](../../PlasmaLean/Design/DommaschkMirrorTubeCrossing.lean)

On both signed tubes of each bracket row and at every point of its **closed** time interval, an actual solution with the physical ODE derivative there satisfies

\[
  \frac{d}{dt}|B(R(t),\pm t,Z(t))|^2 > \frac1{400}.
\]

At a positive reached height $h$ the derivative of the magnitude is greater than $1/(800h)$. The derivative premise at a closed boundary is supplied by a differentiable extension of the physical solution through that point. The checker uses the three full field polynomials and all twelve partial derivatives, the physical harmonic clock, the positive toroidal denominator and each branch's actual outgoing radius. [Physical derivative identities](../../PlasmaLean/Design/DommaschkMirrorStrengthSlope.lean) · [Signed slope generator](../../scripts/dommaschk_kam/verify_secondary_mirror_slopes.py)

| Row | Complete signed physical derivative proof key |
| --- | --- |
| 317 | `5a056410325d250fbd7c409530e4ecf53fe4553a692bb28f53751f3610d8f621` |
| 325 | `3379594a7536b88227d4a8a41756153f41cdb5cf87c88fdddf4d7c0acf492fef` |
| 326 | `681cc7df49c537fd137288fd0e817edfcc339297051b4c5e1b414a832819409b` |

The snapshot and derivative proofs concern local physical tubes. A first-mirror theorem for a birth at this second launch additionally needs the same field line to follow the full chain and to remain below its mirror level on the earlier portion. The path and exclusion certificates can be established independently and joined using the archived rows. The results are dimensionless.

## Reproduction

```sh
lake build PlasmaLean.Design.DommaschkMirrorBracketSlab PlasmaLean.Design.DommaschkMirrorStrengthSlope PlasmaLean.Design.DommaschkStoredPowers PlasmaLean.Design.DommaschkHarmonicBlock00 PlasmaLean.Design.DommaschkHarmonicBlock39 PlasmaLean.Design.DommaschkHarmonicBlock40
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_mirror_caps.py --launch 478 --workers 3 --output /tmp/plasma-q0r478-mirror-caps.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_mirror_slopes.py --launch 478 --rows 317 325 326 --workers 3 --output /tmp/plasma-q0r478-mirror-slopes.json
```

The input archive has SHA-256 `07763b1926fb24bb93889e651ced079f4871c59c72f443f6b7f2392fc5eb6f83`. The manifests record the theorem names, content keys and Lean import paths for independent checking. [Archived row data](../../scripts/dommaschk_kam/results/bounce_frame_q0_u478.json.gz)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-115 |
| Kind | Physical mirror-bracket certificates |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-81, N-91, N-102 |
| Dependency requirement | Compiled exact QA2R field and trigonometric identities, checked physical output boxes, section-zero reflection and continuity away from the cylindrical axis |
| Produces | Closed-tube endpoint signs, signed level crossings and outward crossing rates at the second phase-zero launch radius |
| Status | Five snapshots, four crossing theorems and twelve closed-row derivative theorems kernel-checked |
| Lean evidence | `DommaschkQ0R478MirrorCrossings`, the five snapshot packages, and `DommaschkQ0R478MirrorJet{317,325,326}Physical.{fwd,back}_{transverse,level_transverse}` |
| Audit evidence | Every reported physical implication uses only `propext`, `Classical.choice` and `Quot.sound`. Lean rejected a negative test requesting the opposite physical sign at $318/64$. |
| Last updated | 25 November 2026 |
