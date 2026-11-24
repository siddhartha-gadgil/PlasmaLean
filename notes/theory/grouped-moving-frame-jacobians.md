# A shared spatial Jacobian on consecutive physical trial tubes

For the phase-zero QA2R launch at \(u=239/500\), Lean has checked the physical spatial Jacobian on each of the 48 original moving-frame slabs numbered 280 through 327. It certifies the original allowable logarithmic norm for both time directions. Four groups of twelve slabs supply the field data. Each slab retains its projected trial rectangle, time-dependent frame and signed growth allowances. [Physical trace packet](../../scripts/dommaschk_kam/results/bounce_frame_q0_u478.json.gz) · [Frame certificate generator](../../scripts/dommaschk_kam/verify_grouped_endpoint_jacobians.py)

## Mathematical statement

Let the group comprise the original indices \(a,\ldots,b-1\). At elapsed angle \(t\) on its \(i\)-th slab the original normalized coordinate is \(s=128t-2i-1\), with \(|s|\le1\). All the slabs share the group coordinate

\[
v=\frac{2i+1-a-b+s}{b-a}.
\]

`BoxMap.mem` proves that radial displacement, vertical position, \(\cos(2t)\) and \(\sin(2t)\), enclosed in the four models for this row at \(s\), belong to the group models at \(v\). An explicit coefficient bound accounts for the rounding error in each affine substitution. `Pullback.mem` transports a checked scalar output from \(v\) to its rounded row model at \(s\). Both statements quantify over all the enclosed real values and all \(|s|\le1\). [Grouped trial lemma](../../PlasmaLean/Design/DommaschkGroupedTrialJet.lean)

The group evaluates the actual three physical polynomials \(D,n_R,n_Z\) and both spatial derivatives of each using their exact seven-harmonic expansions. On each original slab Lean checks \(D>0\) and the quadratic form of the velocity Jacobian in the original moving frame. If \(M(t)\) is its frame matrix and \(J(t,x)\) the spatial Jacobian in physical coordinates, the checked upper bound is

\[
\langle w,M(t)^{-1}(J(t,x)M(t)-\dot M(t))w\rangle
\ \leq\ \mu_i\|w\|^2 .
\]

Here \(x\) is any point of the projected trial rectangle, \(w\) is arbitrary and \(\mu_i\) is the smaller of the two archived signed allowances. The negative-clock physical statement uses the phase-zero reflection and the two reflected frames. The signed continuation checker verifies frame conjugacy and equality of the recorded projected radii and allowances before consuming this matrix. [Original-frame construction](shared-harmonic-endpoint-jacobians.md) · [Local restriction and handoff](../../scripts/dommaschk_kam/grouped_trial_jacobian_rows.py)

## Physical check and cost

On index 317, the two original central reference defects and the grouped Jacobian prove `physical_step` on each signed original ODE tube. This local result accepts every point in the respective incoming ellipse. A through-birth passage requires the intervening earlier steps. The forward step key is `e24530eee55d8e004fc1a4f2143cc7829239ac84e792993f8475f8a52bb06084` and the backward step key is `4c73ae1138de3f27a7f5a91a850367598480287177faefbd7aabb9bcae558e42`. The step joins took 4.662 and 4.559 seconds respectively. The field, restriction, matrix and local physical theorems were audited for `propext`, `Classical.choice`, and `Quot.sound`. [Signed physical continuation](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

| Original indices | Group field and six derivatives | Full group with the 12 original frame checks |
| --- | ---: | ---: |
| 280–291 | 162.889 s | 354.577 s |
| 292–303 | 167.517 s | 357.045 s |
| 304–315 | 167.605 s | 357.652 s |
| 316–327 | 163.538 s | 355.772 s |

The total is 1,425.046 recorded Lean compilation seconds for 48 paired spatial bounds, or 29.69 seconds per index. Peak resident memory was 3.80 GiB rounded up. The nine preceding ordinary single-row proofs on indices 220–228 took 210.30–224.42 seconds each. Both timings reuse the same static polynomial coefficient proofs and include the frame checks and audits. These are sums of component compilation times, excluding Python preparation and concurrent scheduling.

On the same original slab 280 the singleton replay took 184.743 seconds. The grouped proof used 15.685 seconds for its own row work, plus one twelfth of the shared 162.889-second jet. The resulting 29.259 seconds per index at this row gives a factor of 6.31. Both runs produced the same five statements, packet digest, projected radii and rational rate.

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkGroupedTrialJet \
  PlasmaLean.Design.DommaschkGroupedHarmonicGap PlasmaLean.Design.DommaschkEndpointContinuation
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
for a in 280 292 304 316; do
  "$py" "$dir/verify_grouped_endpoint_jacobians.py" --span "$a" "$((a+12))" \
    --output "/tmp/q0r478-group-$a.json"
done
"$py" "$dir/verify_native_endpoint_residuals.py" --endpoint q0r478 --row 317 \
  --output /tmp/q0r478-reference317.json
"$py" "$dir/verify_endpoint_signed_prefix.py" --endpoint q0r478 --row 317 \
  --references /tmp/q0r478-reference317.json --jacobians /tmp/q0r478-group-316.json \
  --output /tmp/q0r478-physical317.json
~~~

The optional `--preflight` reports the first failing matrix panel for each original row before any Lean compilation. To add compiled rows to a matching live continuation campaign, pass `--handoff` with its endpoint directory. The producer authenticates the evidence and atomically installs missing rows. It preserves existing accepted receipts and skips rows already undergoing a single-slab proof. [Continuation campaign](../../scripts/dommaschk_kam/verify_endpoint_trace_campaign.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-152 |
| Kind | Grouped spatial enclosure and signed physical ODE application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-102, N-105, N-111, N-119, N-137 |
| Dependency requirement | Exact four-coordinate affine inclusions, physical polynomial identities and the two original signed frame tests |
| Status | Kernel-checked on the 48 paired spatial bounds at indices 280–327, including both local ODE steps at 317 |
| Produces | Reusable group-clock transfer and a checked input to the original signed continuation chain |
| Lean evidence | `DommaschkGroupedTrialJet.BoxMap.mem`, `DommaschkGroupedTrialJet.Pullback.mem`, `DommaschkJacobianQ0R478PairedForward317.physical_clock_log_norm`, both signed `physical_step` declarations at 317 |
| Last updated | 25 November 2026 |
