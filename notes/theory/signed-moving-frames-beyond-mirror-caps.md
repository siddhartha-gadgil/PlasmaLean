# Independent signed moving frames on a shared group of physical slabs

At toroidal section \(\pi/2\), the two matrices bounding the forward and backward ODEs can differ even after the reflection \(z\mapsto-z\). A single spatial field model can still serve both directions. The projected rectangle encloses the forward tube and the reflected backward tube, including the actual difference between their reference curves. Each original frame and its own signed growth allowance then give a separate matrix inequality. [Independent signed frames](independent-signed-endpoint-frames.md) · [Shared spatial Jacobian](grouped-moving-frame-jacobians.md)

## The physical trial at the opposite section

On elapsed slab \(i\), write \(s=128t-2i-1\). For a group with indices \(a\le i<b\), use \(v=(2i+1-a-b+s)/(b-a)\). The four projected coordinate enclosures are evaluated at that shared clock, with \(\theta=2(\pi/2+t)\). In the normalized forward calculation both fundamental harmonics acquire a minus sign. The original backward trajectory uses \(\pi/2-t\), and its spatial coordinates and original frame pass through the checked opposite-section reflection. The two matrix tests independently bound the quadratic forms for the original forward frame and the conjugate of the original backward frame. [Physical group producer](../../scripts/dommaschk_kam/verify_grouped_endpoint_jacobians.py) · [Signed frame and clock checks](../../scripts/dommaschk_kam/grouped_trial_jacobian_rows.py)

The ground example is the \(u=456/1000\) launch at original slab 129 in the group \([124,136)\). The top-right entries of the two reflected endpoint matrices are \(739106746475/2^{40}\) and \(739106746474/2^{40}\). Their reference coefficients have radial and vertical differences bounded by \(9883335869/2^{80}\) and \(10302985763/2^{80}\). The union of their projected trial rectangles uses radii \(1942716722794395477/2^{80}\) and \(3691350242869893469/2^{80}\). The two logarithmic-norm allowances are \(111034710688692258393117/2045380152416804779915042\) forward and \(4112396750786451659359/75754820457507533313760\) backward. [Original endpoint packet](../../scripts/dommaschk_kam/results/bounce_frame_q1_u456.json.gz)

Lean checked the actual ODE step on both signed physical tubes for all inputs in their respective incoming ellipses. The forward physical step key is `567b37f3b587763443aaf6de6968ac7468853ebd6bbba21cc7c56d1434449e42` and the backward key is `7fb45c3b4caf539c47c344c5700f2354f4d8f70ef6097f829a3446a3f3cdde12`. Their independent spatial keys are `6e654d5523f4405fc4ddb7d714a503237555e9c4494601a888ea0df3f48cf459` and `7670b07efc09b82041df9d8b7adcb9390d2e8bf1476adee842a824fdbc2711bd`. Both matrix packages and both physical step packages, including their denominator and clock-dependent norm inequalities, have the standard axiom audit `propext`, `Classical.choice` and `Quot.sound`. [Physical row verification](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## Extent of the remaining six traces

For each launch the planner finds the right endpoint \(b\) of the last exterior sign bracket at either archived height and in either direction. It targets \(b+1\) original slabs each way. The sign boundary at \(b/64\) is then an interior point of the signed path. [Cap planner](../../scripts/dommaschk_kam/plan_endpoint_continuations.py)

| Section | Launch \(u\) | Exterior \(b\) | Target slabs per direction | Groups |
| --- | ---: | ---: | ---: | ---: |
| \(0\) | .523 | 336 | 337 | 29 |
| \(0\) | .531 | 337 | 338 | 29 |
| \(\pi/2\) | .456 | 328 | 329 | 28 |
| \(\pi/2\) | .464 | 329 | 330 | 28 |
| \(\pi/2\) | .509 | 335 | 336 | 28 |
| \(\pi/2\) | .517 | 336 | 337 | 29 |

Exact arithmetic passes all 2,007 proposed slab indices in 171 groups. This screen checks the angular phase, projected widths, individual moving matrices and original signed allowances. The Lean campaign rebuilds the physical field identities and certifies each matrix and ODE step on its original tube. Each complete signed prefix then requires the independent exact central defect in both directions, the actual launch and the continuation of all preceding steps. [Endpoint continuation](continuing-endpoint-field-lines.md) · [Six-endpoint campaign](../../scripts/dommaschk_kam/run_endpoint_continuations.py)

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkGroupedTrialJet \
  PlasmaLean.Design.DommaschkOppositeHarmonic PlasmaLean.Design.DommaschkEndpointContinuation
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
"$py" "$dir/verify_grouped_endpoint_jacobians.py" --endpoint q1r456 --span 124 136 \
  --rows 129 --output /tmp/q1r456-matrices129.json
"$py" "$dir/verify_endpoint_reference_slabs.py" --endpoints q1r456 --range 129 129 \
  --shared --workers 1 --output /tmp/q1r456-defects129.json
"$py" "$dir/verify_endpoint_signed_prefix.py" --endpoint q1r456 --row 129 \
  --references /tmp/q1r456-defects129.json --jacobians /tmp/q1r456-matrices129.json \
  --output /tmp/q1r456-physical129.json
"$py" "$dir/plan_endpoint_continuations.py" --output /tmp/six-signed-targets.json
~~~

To continue the signed traces, supply the authenticated forward and backward launch receipts produced for all eight endpoints. The scheduler checks the completed 328-slab \(u=.478\) birth path before starting, adopts previous per-endpoint results and shares the worker allowance across all six endpoints. At full allocation the first two phase-zero continuations each receive four slots and each opposite-section continuation receives one. The remaining allocations change as endpoints complete. Long prefix joins use a shared lock. [Launch evidence](eight-signed-traces-on-common-tori.md)

~~~bash
"$py" "$dir/run_endpoint_continuations.py" --plan /tmp/six-signed-targets.json \
  --forward-launches "$forward_launches" --backward-launches "$backward_launches" \
  --workers 12 --baseline 4 --reserve-cores 3 --reserve-gib 40 \
  --output /tmp/six-signed-traces.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-157 |
| Kind | Opposite-section signed spatial certificate and multi-endpoint physical continuation |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-102, N-105, N-107, N-119, N-152 |
| Dependency requirement | Fully enclosed original signed rectangles, independently verified frames, both actual residuals and the corresponding archive cap nodes |
| Status | Both opposite-section physical steps checked at 129. Exact proposed group cover through the six post-cap targets. Global birth results are recorded separately as their signed chains complete. |
| Produces | An independently signed spatial proof on groups of original slabs, one actual opposite-section ODE application, and reproducible continuation targets through both exterior caps |
| Lean evidence | `DommaschkJacobianQ1R456IndependentForward129.physical_clock_log_norm`, `DommaschkJacobianQ1R456IndependentBack129.physical_clock_log_norm`, and both signed physical steps at 129 |
| Last updated | 25 November 2026 |
