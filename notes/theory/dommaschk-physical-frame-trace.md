# Physical entry, frame arithmetic and the first trajectory defect

| Field | Value |
| --- | --- |
| ID | N-64 |
| Kind | Physical trajectory proof and exact certificates |
| Addresses | Q-35, Q-1, G-6, G-10 |
| Depends on | N-60 through N-63 |
| Dependency requirement | The physical launch, polynomial reference, moving frame, angle and seed of a directed trace must agree. |
| Produces | Physical entry on eight sub-sectors, 16 scalar frame chains, complete harmonic enclosures, and the first forward physical defect. |
| Difficulty | Bound the logarithmic norm of the physical Jacobian over a moving trial tube and propagate the actual initial value. |
| Status | The four results below are kernel-checked. The long physical field-line theorem is open. |
| Lean evidence | `exists_nested_section_entry`, `PositionFrameSlabs.Chain.sound`, `DommaschkHarmonicTrace.all_times`, `DommaschkReferenceFirst.framed_defect` |
| Audit evidence | 54,345 default and 91,933 on-demand declarations passed the standard-axiom audits. All 16 generated chains passed an independent Lean replay. |
| Last updated | 24 November 2026 |
| Patched by | N-65 proves the first physical Jacobian bound and composes the moving-frame step with the physical birth. |
| Patches | N-62 and N-63, physical start and Lean status of numerical hypotheses |

## Four checked results

1. **Physical entry at eight radii.** There is one nested pair of Q-16 invariant tori for which each birth at one of the four recorded radii on either symmetry section reaches that section inside the recorded Euclidean starting ball. The half-widths in geometric radians are $2^{-19}$ about zero and $2^{-20}$ about $π/2$. The theorem gives a solution of the actual field-line ODE from the birth to the section. The construction combines the Fourier displacement of the true launch profile with the previously proved velocity bound. Both trace directions use exactly this state, centre, identity frame and radius. The wider $2^{-12}$ sector used by the external calculation still needs the cancellation between chart motion and physical velocity. [Physical entry](../../PlasmaLean/Design/DommaschkFrameLaunch.lean) · [Endpoint data](../../PlasmaLean/Design/DommaschkMirrorEndpoints.lean)

2. **Scalar propagation along 16 chains.** Lean checks 391 successive steps per direction at each endpoint. It verifies both polynomial endpoints, the frame change and jump estimate, determinant greater than 0.97 throughout the affine frame, the rational radius recurrence, and the propagated scalar bounds. Across all 6,256 steps the recorded physical outgoing radius is below $3.45×10^{-6}$ and the trial radius below $10^{-5}$. These radii apply to an actual ODE solution once the reference defect and one-sided derivative estimates have been supplied for its tube. Two pilot modules are checked in place. The other fourteen Lean sources are generated from the committed compressed records by the same command. [Scalar soundness](../../PlasmaLean/Certificates/PositionFrameSlabs.lean) · [Proof emitter](../../scripts/dommaschk_kam/emit_position_slabs.py)

3. **Harmonics at every physical time.** For every elapsed angle $0≤t≤391/64$, Lean produces one of the 391 closed slabs containing $t$. On that same slab all three sine/cosine pairs, in both directions and at both physical sections, satisfy the Taylor model bounds. The proof accounts for the phase change at $π/2$. It is shared by every radius. [Physical angular theorem](../../PlasmaLean/Design/DommaschkHarmonicTrace.lean)

4. **First physical reference defect.** For the forward trace at section zero and radius 0.470, Lean compares the actual QA2R field-line velocity along the exported polynomial with the derivative of that polynomial, at every geometric angle from 0 to 1/64. The radial discrepancy is at most $10^{-12}$ and the vertical discrepancy at most $10^{-13}$. In the inverse of the actual affine frame the Euclidean discrepancy is at most $9271400940439/2^{80}$, approximately $7.67×10^{-12}$. The proof uses signed Taylor polynomials before taking absolute bounds and subintervals to retain cancellation. This estimate along the reference has no assumption about the location of the true trajectory. Separately, for points in the trial tube, Lean proves positivity of the field denominator and bounds both field numerators. [Physical defect](../../PlasmaLean/Design/DommaschkReferenceFirstDefect.lean) · [Physical trial-tube bounds](../../PlasmaLean/Design/DommaschkBounceTaylorFirst.lean)

## Reproduction

From the repository root, the following commands verify the geometry and physical entry, kernel-check all 16 emitted frame chains, and recheck the sparse defect arithmetic. The worker counts can be reduced on a smaller machine.

```sh
lake build PlasmaLean.Design.DommaschkFrameLaunch PlasmaLean.Design.DommaschkReferenceFirstDefect
python3 scripts/dommaschk_kam/emit_position_slabs.py --verify-all --jobs 8
bash scripts/dommaschk_kam/check_harmonic_trace.sh 5
.venv-ws/bin/python scripts/dommaschk_kam/emit_sparse_reference_defect.py --check
```

## Remaining application

The next physical lemma bounds the symmetric part of the moving-frame Jacobian on the entire first trial tube. Together with the central defect and the incoming ball it can yield an outgoing ball for the true solution. Extending that argument requires the corresponding physical bounds on the subsequent slabs as well as control of radial derivatives for the action-graph application. The unconditional full-sector physical field-line collar is still 1/64 radian. Physical time and trapped-birth coverage require further hypotheses. [Trajectory gluing](dommaschk-long-trace-witness.md) · [External long traces](dommaschk-eight-long-traces.md)
