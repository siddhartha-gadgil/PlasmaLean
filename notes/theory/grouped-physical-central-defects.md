# Bounding the original signed ODE defects on a common polynomial clock

Six consecutive slabs of the \(u=523/1000\) phase-zero launch now share a single evaluation of the three polynomials \(D,N_R,N_z\) in the physical ODE. Lean verified the twelve original signed defect bounds on slabs 60–65. The forward and backward physical ODE steps at slab 60 also passed, including the ellipses and signed growth bounds from the original packet. The central-defect proof stages for these six rows took 199.813 seconds across their distinct build stages. The previous method took 465.098 seconds on the same six rows, a factor of 2.33. [Original packet](../../scripts/dommaschk_kam/results/bounce_frame_q0_u523.json.gz) · [Physical ODE consumer](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## A degree-twelve enclosure on a group

Let \(a\le i<b\) index the original slabs. Write \(s=128t-2i-1\) for the elapsed row clock and \(v=(2i+1-a-b+s)/(b-a)\) for the group clock. Every \(s\in[-1,1]\) maps into \([-1,1]\). The producer samples the original piecewise reference polynomials for \(R,z\) and the seven harmonic channels at thirteen rational nodes. It interpolates each channel over the rationals and rounds its coefficients to multiples of \(2^{-80}\). On each entire original row it bounds the absolute difference by the sum of the absolute coefficients of the difference after the affine substitution, including the original uncertainty. This final enclosure check establishes validity between nodes and across boundaries. [Exact model construction](../../scripts/dommaschk_kam/grouped_central_models.py) · [Physical coordinate inclusions](../../PlasmaLean/Design/DommaschkGroupedTrialJet.lean)

For a specified Taylor format \(F\), the reusable theorem `Run.mem` proves that an explicitly rounded Horner evaluation encloses the exact polynomial wherever the input models hold. Its row and harmonic-channel theorems assemble the three physical polynomials with the same angle in every channel. The producer applies this theorem in a degree-twelve format on the group. It then composes each result with the row's affine clock, rounds the first eight coefficients and charges the higher coefficients and rounding error to the row radius. Lean checks this restriction independently for each of the three polynomials. [Horner theorem](../../PlasmaLean/Design/DommaschkVariableHorner.lean) · [Grouped field verification](../../scripts/dommaschk_kam/verify_grouped_central_defects.py)

Each original defect uses the derivative of its own archived reference, the determinant and adjugate of its own moving frame, and the signed budget in its own row. The producer bounds \(N_R-D\,R'\) and \(N_z-D\,z'\) before taking the norm, and verifies a strictly positive lower denominator bound. The phase-zero reflection identifies the backward residual with the reflected forward residual. The scalar check uses the smaller of the two original signed allowances. [Row restriction and signed proof](../../scripts/dommaschk_kam/grouped_central_defect_rows.py) · [Central ODE defect](../../PlasmaLean/Design/DommaschkPhysicalCentralJet.lean)

## Ground evidence and campaign coverage

The shared field theorem for \([60,66)\) has key `4d41ef33e89375de85dadddb21fad918d13de71b85d56cc9718426d5667a7a9f`. Its build took 110.755 seconds and peaked at 3,958,500 KiB. The largest of the six defect-to-allowance ratios was \(1068485234959/3873155834201\) at row 61. The original spatial certificate from the group \([60,72)\) and the new central certificate give `DommaschkPhysicalQ0R523Forward060.physical_step` with key `0c4a293f7cf2b94759043f7cf805ef439bc7a7891d6902b519135f4bd31bf9fd` and `DommaschkPhysicalQ0R523Back060.physical_step` with key `69cf77a1dad928fa1b5692571c385fc8459fd0dd019adf6e197d0ceae0d64c5f`. The axiom audit for both steps and all twelve central bounds returned `propext`, `Classical.choice` and `Quot.sound`. [Grouped spatial proof](grouped-moving-frame-jacobians.md)

The speed comparison sums each distinct nonstatic verification stage once, including both signed wrappers. The static harmonic coefficients are common to both methods. The measurement covers central defects, with spatial Jacobians and final trajectory composition timed separately. Replaying the old scalar producer on row 60 returned its original field, sharp bound and both wrapper keys.

The exact external planner screened every original signed budget through one slab beyond both physical caps. For \(u=.523\), 337 rows form forty groups of eight, four of four and one singleton. The largest predicted ratio is \(260037660143/289744104509<0.898\) on row 316. For \(u=.531\), 338 rows form thirty-nine groups of eight, six of four and one of two. The largest predicted ratio is \(912206016122/939099356283<0.972\) on row 335. The live campaign takes a group only after its field proof, restrictions and both signed original row theorems pass. It retains accepted rows and uses the original scalar producer on a singleton or a failed group. Completion of the two full through-birth paths is tracked separately. [Exact planner](../../scripts/dommaschk_kam/plan_grouped_central_defects.py) · [Campaign handoff](../../scripts/dommaschk_kam/campaign_grouped_central.py)

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkVariableHorner \
  PlasmaLean.Design.DommaschkGroupedTrialJet PlasmaLean.Design.DommaschkPhysicalCentralJet \
  PlasmaLean.Design.DommaschkEndpointContinuation
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
"$py" "$dir/verify_grouped_central_defects.py" --endpoint q0r523 --span 60 66 \
  --output /tmp/grouped-central060-065.json
"$py" "$dir/verify_grouped_endpoint_jacobians.py" --endpoint q0r523 --span 60 72 \
  --rows 60 --output /tmp/grouped-spatial060.json
"$py" "$dir/verify_endpoint_signed_prefix.py" --endpoint q0r523 --row 60 \
  --references /tmp/grouped-central060-065.json --jacobians /tmp/grouped-spatial060.json \
  --output /tmp/grouped-physical060.json
"$py" "$dir/plan_grouped_central_defects.py" --output /tmp/grouped-central-plans.json
~~~

The live continuation can select these plans by adding `--activate-campaign .lake/secondary-trace-campaign` to the final command. It verifies the packet digest and length for each endpoint before installing new receipts.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-166 |
| Kind | Grouped original signed central ODE defects and measured acceleration |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-105, N-111, N-119, N-152, N-157 |
| Dependency requirement | Original piecewise references, identical phase-zero reflection, validated harmonic fields, actual moving frames and both archived budgets |
| Status | Twelve signed defect bounds and both physical ODE steps at row 60 checked. Exact group plans for all 675 rows of the two continuations. |
| Produces | Arbitrary-format certified harmonic Horner evaluation, degree-twelve affine restriction to original rows, and resumable grouped central-defect certificates |
| Lean evidence | `DommaschkVariableHorner.Run.mem`, `DommaschkVariableHorner.channel_cons`, original signed `physical_defect` rows 60–65, `DommaschkPhysicalQ0R523Forward060.physical_step`, `DommaschkPhysicalQ0R523Back060.physical_step` |
| Last updated | 25 November 2026 |
