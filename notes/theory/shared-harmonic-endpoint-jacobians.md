# One physical field evaluation for four signed launch branches

At the phase-zero QA2R launches $u=523/1000$ and $531/1000$, the same nine Taylor models certify the physical field and its two spatial derivatives on a rectangle containing both forward trial tubes and both reflected backward tubes. Each label retains its own moving frame, original residuals and growth budgets. Lean uses those bounds to construct the actual signed traces on $[-1/32,1/32]$ for both labels. Separately, the $u=239/500$ trace now reaches $[-1/16,1/16]$. The angular origin in all three statements is the canonical section. [Harmonic verification](../../scripts/dommaschk_kam/verify_horner_endpoint_jacobian.py) · [Physical continuation](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## The field identity and the spatial bound

The nine quantities are $D,n_R,n_Z$ and both spatial partial derivatives of each. For each polynomial $p$, Lean verifies once that its seven rational harmonic channels, evaluated at the common angle $\theta=2\phi$, equal the original QA2R sparse polynomial $p(R-R_0,z,\cos\theta,\sin\theta)$. Each slab uses rounded Horner evaluation in the two spatial coordinates. Lean checks every dyadic operation and the actual six nonconstant harmonics on the whole normalized clock interval. On each coordinate, the wider rectangle pays for the projected trial radius plus the coefficientwise distance from that endpoint’s centre. [Harmonic polynomial identities](../../PlasmaLean/Design/DommaschkHarmonicHorner.lean) · [Rounded Horner soundness](../../PlasmaLean/Design/DommaschkNativeActionModel.lean)

For each endpoint frame $M$, the same jet gives a separate lower bound on the physical denominator and an upper bound on the largest eigenvalue of the symmetric part of $M^{-1}(JM-M')$. Eight normalized-time panels suffice for the concrete pair at slab index 1. Both forward and backward archived growth allowances are checked for each label. The two ODE chains start at the section state reached by the interpolated birth. A common-torus theorem also places each label and the original $u=47/100$ pilot on the same pair of nested Q-16 tori. [Moving-frame bound](../../PlasmaLean/Design/DommaschkJacobianFrames.lean) · [Endpoint birth comparison](../../PlasmaLean/Design/DommaschkEndpointContinuation.lean)

| Phase-zero radial label | Slabs in each direction | Signed physical interval | Signed birth proof key |
| --- | ---: | --- | --- |
| $523/1000$ | 2 | $[-1/32,1/32]$ | `0d42b68851b8039905780f9eeb57015f608f5b67962159913cd8cec060844497` |
| $531/1000$ | 2 | $[-1/32,1/32]$ | `f3ca35f1a6c82ed67400bb32e64435daaf27dc20cf670dd20ede53db637cf69e` |
| $239/500$ | 4 | $[-1/16,1/16]$ | `f1e07dcc0281976bcc4d4c8721fa544d2144bd0d2499c9191dc1a6f48d1abe70` |

The first two rows use the new shared-rectangle proof. The four-slab $239/500$ trace uses the original sparse certificates and reaches a maximum archived physical outgoing radius of $1503818899076388360/2^{80}$, about $1.244\times10^{-6}$. Every signed-birth theorem in the table was audited for the standard three axioms. [Original four-slab witness](../../scripts/dommaschk_kam/results/bounce_frame_q0_u478.json.gz)

All three endpoints below also have a checked third signed slab, reaching $\pm3/64$ radians from their respective sections.

| Endpoint | Ground theorem | Content key |
| --- | --- | --- |
| q0r523 | DommaschkSignedPrefixQ0R523003.common_with_pilot | `e0f49fd82cd20d89ec6e3eca9a46018093785c13ed6bf5c2429e9484ea088a0a` |
| q0r531 | DommaschkSignedPrefixQ0R531003.common_with_pilot | `082ae398f9772eac1d5dfc38af57e48e9c61f565ab5622ad01801f22776b7e10` |
| q1r456 | DommaschkSignedPrefixQ1R456003.common_with_pilot | `f522698380df23633512aff3ed839c4983011f4763cfe812c9efda027a6e2cc1` |

## Measured cost and longer-range screen

The nine physical polynomial identities took 50.6 seconds once on one workstation core. Given these identities, index 1 took 231.7 seconds for the nine whole-box fields and both endpoint matrix proofs together. The independent sparse proof for the same $523/1000$ index alone took 517.0 seconds. The two methods yield different exact enclosures and independently imply the original growth budget. The content keys of the two new Jacobian theorems are `0455693033480b0f8933bb9e32d33d95ca801f420620adf5eaf0478803253ae5` and `8c10316298851f422db1c76c0e3fadfc426b36c3a52c79a5c28e23ea078dd116`. [New producer](../../scripts/dommaschk_kam/verify_horner_endpoint_jacobian.py) · [Sparse comparator](../../scripts/dommaschk_kam/verify_endpoint_forward_jacobians.py)

An exact-arithmetic screen over all 391 indices found the following coverage. Each count in the last two columns requires successful panel tests for **both** radial labels. The screen checks exact rational bounds using the physical angle enclosures and each label’s own matrix. The full-archive counts describe arithmetic proposals for further Lean replay. [Screen and rectangle construction](../../scripts/dommaschk_kam/screen_endpoint_jacobian_sharing.py)

| Section and neighbouring labels | Indices with exact reflected frames at both labels | Both pass a shared rectangle | Both pass their individual rectangles |
| --- | ---: | ---: | ---: |
| $0$, .470 and .478 | 391 | 180 | 391 |
| $0$, .523 and .531 | 391 | 179 | 391 |
| $\pi/2$, .456 and .464 | 129 | 65 | 129 |
| $\pi/2$, .509 and .517 | 270 | 145 | 270 |

Both zero-section pairs pass throughout indices 0–7. At the opposite section, both nearest-neighbour rectangles fail on the last time panel at each of these eight indices, including with 64 time panels. The individual rectangles pass these rows. At later opposite-section indices some backward endpoint frames differ from the exact conjugates of their forward partners. The two rates can then be tested against separately transformed matrices for the same physical jet. The archived section-zero paths through the first four mirrors and the action bounds at $u=.470$ remain distinct from the short trajectories at the new labels. The latter still require their own mirror and action certificates.

## Reproduction

Starting with the two N-91 launch reports and the N-102 residuals for both labels, run the three commands below. The signed trace producer checks the actual source and compiled artifacts of the upstream spatial and residual proofs.

```sh
lake build PlasmaLean.Design.DommaschkEndpointContinuation PlasmaLean.Design.DommaschkNativeActionModel
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
$py "$dir/verify_endpoint_reference_slabs.py" --endpoints q0r523 q0r531 --range 1 1 --workers 1 --shared --output /tmp/shared-residual1.json
$py "$dir/verify_horner_endpoint_jacobian.py" --endpoints q0r523 q0r531 --row 1 --output /tmp/shared-jet1.json
for e in q0r523 q0r531; do
  $py "$dir/verify_endpoint_signed_prefix.py" --endpoint "$e" --length 2 --forward-launches /tmp/plasma-all-eight-physical-launches.json --backward-launches .lake/endpoint-backward/all-eight-physical-backward-launches.json --references /tmp/shared-residual1.json --jacobians /tmp/shared-jet1.json --output "/tmp/signed-$e-2.json"
done
$py "$dir/screen_endpoint_jacobian_sharing.py" --range 0 390 --output /tmp/endpoint-sharing.json
```

For the four-slab $u=239/500$ proof, run the N-102 residual and paired sparse Jacobian producers with `--endpoints q0r478 --range 1 3`, then the signed-prefix producer with `--endpoint q0r478 --length 4` and those two saved reports. [N-102 commands](continuing-endpoint-field-lines.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-105 |
| Title | One physical field evaluation for four signed launch branches |
| Kind | Reusable certificate method and physical trajectories |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-91, N-94, N-102 |
| Dependency requirement | Original field polynomials and derivatives, physical harmonic enclosures, rounded Horner soundness, Q-16 births and signed frame chains. |
| Target | Reuse the physical field jet across nearby radial labels and both directions, with exact original tolerances and states. |
| Difficulty | Separate growth budgets, moving frames and unequal reference polynomials constrain the size of a shared rectangle. |
| Status | The first shared two-label Jacobian is verified and consumed by four signed ODE branches. The longer-range screen is exact external arithmetic. |
| Lean evidence | `DommaschkHornerJetData*.physical_identity`, `DommaschkJacobianQ0R{523,531}PairedForward001.physical_clock_log_norm`, `DommaschkSignedPrefixQ0R{523,531}002.common_with_pilot` and `DommaschkSignedPrefixQ0R478004.from_birth`. |
| Audit evidence | All concrete physical declarations audited with `propext`, `Classical.choice` and `Quot.sound`; proof keys appear above. |
| Last updated | 25 November 2026 |
