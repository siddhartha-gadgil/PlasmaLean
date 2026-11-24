# Eight signed field-line traces on the same two Q-16 tori

Lean constructs **one pair of nested QA2R tori** supporting all eight endpoint launch sectors. For every admitted angle and each endpoint, the prescribed interpolated birth reaches its section under the physical field. From that section a single oriented solution stays inside the original forward and backward certified tubes for the following geometric angles. [Common-torus theorem](../../PlasmaLean/Design/DommaschkEndpointTraceFamily.lean) · [Eight-endpoint proof producer](../../scripts/dommaschk_kam/verify_common_endpoint_traces.py)

| Section | Radial interpolation $u$ | Physical slabs each way | Angular reach on each side of the section |
| --- | --- | ---: | ---: |
| $0$ | 0.470 | 391 | $391/64$ |
| $0$ | 0.478 | 48 | $3/4$ |
| $0$ | 0.523 | 16 | $1/4$ |
| $0$ | 0.531 | 5 | $5/64$ |
| $\pi/2$ | 0.456 | 12 | $3/16$ |
| $\pi/2$ | 0.464 | 5 | $5/64$ |
| $\pi/2$ | 0.509 | 5 | $5/64$ |
| $\pi/2$ | 0.517 | 5 | $5/64$ |

The certified birth sector has half-width $2^{-19}$ radian at section zero and $2^{-20}$ radian at section $\pi/2$. All eight families extend at least $5/64$ radian on both sides. The table covers 487 records per direction, or 974 signed records in total. Each row is an interval of $1/64$ radian. These numbers measure the field line's angular reach after the section crossing. [Endpoint sectors](../../PlasmaLean/Design/DommaschkMirrorEndpoints.lean) · [Full signed pilot trace](full-signed-pilot-birth.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-120 |
| Title | Eight signed physical traces on the same pair of nested Q-16 tori |
| Kind | Proof and certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-91, N-102, N-105, N-107, N-110, N-111 |
| Dependency requirement | The simultaneous section-entry theorem for the nested pair, both 391-row pilot chains and seven signed physical prefixes accepting any certified entry at their respective endpoint. |
| Produces | One existential pair of physical nested tori, with both original exits and all signed tubes through the recorded length for each endpoint. |
| Difficulty | A separately chosen torus pair for each trace would lose the common radial interpolation. The clock origin, phase sector, ordered tube lists and terminal ellipsoids also differ between endpoints. |
| Status | Verified |
| Lean evidence | `DommaschkEndpointTraceFamily.common_of_entry` and the on-demand `DommaschkCommonEndpointTraces391_48_16_5_12_5_5_5.same_nested_tori`. |
| Audit evidence | The resulting family, its per-entry implication, the pilot physical implication and both row counts for all labels have kernel proofs using only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Choosing the tori before the endpoints

**[Lean]** The reusable `Checkpoint` stores the signed duration as a row count, the two terminal reference states and both lists of rows. Given any assignment of checkpoints to the eight labels, `common_of_entry` needs one implication per label. Any entry satisfying `SectionEntry` at the prescribed interpolated birth must admit the corresponding signed physical passage. Applying those implications to the entries from `exists_nested_section_entry` fixes the two surfaces and the common interpolation before quantifying over the endpoint and angular displacement. Both surfaces retain their certified rotational transforms and geometric nesting. [Varying-duration family](../../PlasmaLean/Design/DommaschkEndpointTraceFamily.lean) · [Common Q-16 section entries](dommaschk-eight-signed-launches.md)

**[Lean]** For the pilot, each scalar chain and its field bounds imply a physical chain from every position in its actual entrance ellipsoid. The two 391-row chains therefore admit the same section entry as the seven shorter passages. The negative half of a signed solution is evaluated at physical azimuth $\phi_0-t$ while the outward clock $t$ increases. Both its terminal position and all intermediate positions satisfy the original certified enclosures. The separate endpoint choices may yield different field lines on this common geometry. [Pilot physical chain](../../PlasmaLean/Design/DommaschkBackwardPairedPrefix.lean) · [Oriented signed passage](../../PlasmaLean/Design/DommaschkEndpointSignedTrace.lean)

This phase provides finite field-line coverage for the listed sectors in the dimensionless QA2R model. Mirror and action claims at each endpoint still require their respective field-strength or quadrature certificates. [Physical pilot action](dommaschk-native-first-well-action-enclosure.md)

## Reproduce the snapshot

Run the signed pilot and secondary prefix producers first. The family verifier takes one paired pilot receipt and seven distinct signed secondary prefix receipts. It checks each content-addressed kernel artifact, each endpoint's archived frame-witness digest, the two row counts and both physical exit states. Passing longer receipts to the same command creates a separately named family proof. [Secondary prefix producer](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py) · [Pilot prefix producer](../../scripts/dommaschk_kam/verify_paired_physical_prefix.py)

```sh
LEAN_NUM_THREADS=1 lake build PlasmaLean.Design.DommaschkEndpointTraceFamily
py=.venv-ws/bin/python
prefix=.lake/secondary-trace-campaign
"$py" scripts/dommaschk_kam/verify_common_endpoint_traces.py \
  --pilot /tmp/plasma-full-signed391.json \
  --secondary "$prefix/q0r478/prefixes/048.json" "$prefix/q0r523/prefixes/016.json" \
    /tmp/plasma-horner-signed-q0r531-5.json "$prefix/q1r456/prefixes/012.json" \
    "$prefix/q1r464/prefixes/005.json" "$prefix/q1r509/prefixes/005.json" \
    "$prefix/q1r517/prefixes/005.json" \
  --output /tmp/plasma-common-endpoint-traces-extended.json
```

The 974-row family has content key `43ab61a2d1324883d585368927ba5249cd5237dd8f0f19a05103c1d56a255ef2`. The earlier, independently compiled 908-row family, in the same table order with lengths 391, 32, 12, 5, 8, 2, 2 and 2 each way, has key `b0189e95ed4afcd6a7999462afc50142c3d30caffc33271bfc8f8a414984aae4`. Each receipt records the full SHA-256 of each input archive and the proof key of each signed endpoint prefix.
