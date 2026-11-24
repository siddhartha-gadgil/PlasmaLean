# Pilot action and all eight signed launches on the same embedded tori

Lean now exhibits **one pair of nested embedded QA2R tori** supporting all eight signed launch sectors and the complete quantitative first-well result for every admitted pilot angle. The signed line that passes through the physical pilot birth at its original angle is defined on $[-391/64,391/64]$. On that same line the first mirrors exist throughout the closed height band, the one-way flight time lies between 54.98668 and 264, and the upper-height one-way action lies between 0.2765 and 1.357791. The height calibration, radial derivative at the section-centre birth, and finite two-line comparison criterion now refer to the same launch geometry. [Common-family theorem](../../PlasmaLean/Design/DommaschkCommonPilotObservables.lean) · [Ground assembler](../../scripts/dommaschk_kam/verify_common_pilot_observables.py)

## Why the order of the choices matters

Two statements that each produce their own nested pair give no identification of the two interpolated launch points. For a finite comparison between $u=0.470$ and $u=0.478$, the surfaces that define the radial interpolation must be fixed first. The reusable lemma accepts a pilot property proved for **every trajectory enclosed by the archived pilot tubes**. It restricts a trajectory of the common family to the records needed by that property. Uniqueness for the regular ODE on the short approach shows that this very trajectory goes through the interpolated birth at its original angle, including at nonzero launch angles. [Approach identification](../../PlasmaLean/Design/DommaschkSignedBirthApproach.lean) · [Prefix restriction of the same path](../../PlasmaLean/Design/DommaschkSignedTracePrefix.lean)

The concrete proof first works for any pilot trajectory with the original 326 forward and 326 backward rows. It uses strict first-contact signs, transverse derivatives, all 31,200 quadrature cells and the row-wise reciprocal-speed enclosures. It then restricts the actual 391-row trajectory on the common surfaces to those 326 rows. At every pilot angle $|\varphi|\le2^{-19}$ and every archived height, the complete physical action cap, its height derivative estimates and its inverse bound hold. The action increases by more than 0.0284 between the archived endpoint heights. [Original action](dommaschk-native-first-well-action-enclosure.md) · [Joint flight bounds](action-floor-for-first-mirror-flight-time.md) · [Height calibration and finite radial test](finite-radial-action-comparison.md)

The snapshot includes 523 rows each way. Each entry below counts complete angular slabs of width $1/64$ in **each** direction. The table describes the common family fixed for this proof.

| Section | Radial labels | Signed lengths per direction |
| --- | --- | --- |
| Zero | 0.470, 0.478, 0.523, 0.531 | 391, 64, 32, 5 |
| π/2 | 0.456, 0.464, 0.509, 0.517 | 16, 5, 5, 5 |

Only the pilot has the full action calibration here. To apply the finite radial test, the second path must reach its actual first mirrors and the two fields and arclength densities must satisfy the cross-line comparisons. [Secondary height branch](secondary-first-mirror-height-band.md) · [Signed traces](eight-signed-traces-on-common-tori.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-130 |
| Title | A calibrated physical pilot in the eight-sector embedded torus family |
| Kind | Geometric composition and ground proof |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-101, N-110, N-116, N-120, N-124, N-126 |
| Dependency requirement | An authenticated common torus family with a pilot of at least 326 rows, original contact and quadrature proofs, and the field-line approach at the actual birth angle. |
| Produces | Pilot action and flight calibration on every admissible 326-row pilot path and the same 391-row pilot and embedded surfaces as all eight launches. |
| Difficulty | Independent existential choices of surfaces, solutions, or turning points cannot be substituted for one another. |
| Status | Verified on the common family and independently replayed using a fresh assembly cache. |
| Lean evidence | DommaschkCommonPilotObservables.of_paths, DommaschkCalibratedFamily391_64_32_5_16_5_5_5.on_326 and same_embedded_tori. |
| Audit evidence | Both ground declarations used only propext, Classical.choice and Quot.sound. The calibrated 1,046-row snapshot has key 55c505589ca0d77f12171b4790f7e7fbc45aa384fa06c4c6273fd3f2083015aa. |
| Last updated | 25 November 2026 |

## Replay

Generate the N-120 family using the row counts above and the N-124 birth certificate for that family. The resulting family and birth keys are `eb55326d229e0ca93be75cce409477d7a9d21d1eada0b6dc1165f1e6e7119947` and `1d1b8623ac4004ac314009229299dd8d6f54a6ba532af6de5ab3c7e82f77a2c3`. The N-116 flight receipt must match the original pilot packet. [Eight-sector inputs](eight-signed-traces-on-common-tori.md) · [Physical birth verifier](pilot-radial-birth-variation.md)

~~~bash
lake build PlasmaLean.Design.DommaschkCommonPilotObservables PlasmaLean.Design.DommaschkFiniteRadialAction
.venv-ws/bin/python scripts/dommaschk_kam/verify_common_pilot_observables.py \
  --birth /tmp/plasma-radial-birth1046.json --flight /tmp/plasma-action-flight-bounds326.json \
  --output /tmp/plasma-calibrated-eight1046.json
~~~
