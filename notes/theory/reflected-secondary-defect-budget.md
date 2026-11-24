# Reusing the central defect on the second physical radial label

At the phase-zero QA2R launch $u=239/500$, Lean now proves a backward central ODE defect from the actual forward component enclosures and the backward row’s own archived allowance. On slab 4, the resulting backward physical step composes with its predecessors into a signed birth trajectory on $[-5/64,5/64]$. The from-birth theorem quantifies over every admitted angle $|\phi|\leq 2^{-19}$. Both signed branches start at the state reached by the physical approach from the interpolated Q-16 birth. [Reflected residual producer](../../scripts/dommaschk_kam/verify_reflected_endpoint_residuals.py) · [Signed ODE composition](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## The exact budget test

For each row the checker proves that reflection in the zero section maps the actual forward reference curve to the backward reference, with the radial coordinate fixed and the vertical coordinate negated. It checks both endpoint frames under conjugation by $S=\operatorname{diag}(1,-1)$. The physical section identity then equates the Euclidean norms of the two pulled-back defects at every normalized time. [Section reflection and defect identity](../../PlasmaLean/Design/DommaschkSectionReflection.lean)

Let $X,Y$ be upper bounds for the absolute values of the two framed residual numerators, and let $L>0$ be the denominator’s certified lower bound, in common dyadic units. Python proposes a rational $b=k/2^{80}$ with $k=1+\lfloor 2^{80}\sqrt{X^2+Y^2}/L\rfloor$. Lean rechecks $X^2+Y^2\leq b^2L^2$, verifies the complete forward interval certificate using $b$, and checks $b\leq b_{\rm back}$. The two archived defect budgets may differ. The backward reference, frame and budget in the final physical theorem are those of the original witness. [Framed residual checker](../../PlasmaLean/Design/DommaschkFramedTaylorResidual.lean) · [Exact certificate emitter](../../scripts/dommaschk_kam/emit_reflected_reference.py)

| Compiled result | Content key |
| --- | --- |
| q0r478 slab 4 backward physical central defect | `440e473dd26783fa15e268b1bf7178fcf8219b3f5da48dbf9b64626a783c73f0` |
| Five physical slabs each way from every admitted birth on the same nested Q-16 tori | `4d0d0b95d94673632c263b397ad748b62339b8272c2758c0507e54877d13df44` |

The backward defect proof on the workstation took 3.056 seconds after the forward certificate was available. An external exact replay finds that the dyadic $b$ fits the backward budget on all **391** q0r478 slabs. The largest ratio $b/b_{\rm back}$ is $932345622889/2537038575376$ on slab 283, approximately 0.3675. The whole-archive ratio measures feasibility. The table identifies the slab and signed-prefix results that were independently audited in Lean. [Archived position and frame witness](../../scripts/dommaschk_kam/results/bounce_frame_q0_u478.json.gz)

## The second radial trajectory

The monitored campaign targets 328 physical slabs in each direction, including original index 327. In the external compensated-strength replay, the lower height is bracketed within $[317/64,318/64]$ and the upper height within $[325/64,327/64]$ in both outward directions. The extra slab includes the full reported above-height interval. A genuine first mirror at this radial label still requires strict earlier field-strength bounds, the physical hit and the signed-slope certificate. It will then be possible to compare actions at two physically realized labels. [Strength observable](../../scripts/dommaschk_kam/bounce_phase_strength.py)

The campaign saves each verified spatial and central proof by row and checks intermediate signed trajectories. Its durable `status.json` records every accepted prefix key, the number of rows with both reference defects, available memory, active jobs and failures. The worker cap remains four while the original pilot’s physical action-cell campaign is active. Further workers can start after sustained idle capacity and at least 32 GiB of system headroom. [Resumable workstation campaign](../../scripts/dommaschk_kam/verify_endpoint_trace_campaign.py)

## Reproduction

Use the N-102 first-row launch reports and the paired Jacobian/residual reports for q0r478 rows 1–3. The following commands produce the row-4 growth bound and the reflected central proof, then replay the five-slab result.

```sh
lake build PlasmaLean.Design.DommaschkEndpointContinuation PlasmaLean.Design.DommaschkNativeActionModel PlasmaLean.Design.DommaschkSectionReflection
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
$py "$dir/verify_horner_endpoint_jacobian.py" --endpoints q0r478 --row 4 --output /tmp/q0r478-jet4.json
$py "$dir/verify_reflected_endpoint_residuals.py" --endpoint q0r478 --row 4 --output /tmp/q0r478-residual4.json
$py "$dir/verify_endpoint_signed_prefix.py" --endpoint q0r478 --length 5 --forward-launches /tmp/plasma-all-eight-physical-launches.json --backward-launches .lake/endpoint-backward/all-eight-physical-backward-launches.json --references /tmp/plasma-seven-endpoints-row-{1,2,3}.json /tmp/q0r478-residual4.json --jacobians /tmp/plasma-q0r478-paired-jac001-003.json /tmp/q0r478-jet4.json --output /tmp/q0r478-five.json
$py "$dir/verify_reflected_endpoint_residuals.py" --endpoint q0r478 --screen --output /tmp/q0r478-all-budgets.json
```

For a full campaign from the two first-row launch reports, all later field and residual proofs can be proposed and built on demand. The optional seed inputs reuse already verified progress.

```sh
$py "$dir/verify_endpoint_trace_campaign.py" --endpoint q0r478 --length 328 --reflected-residuals --forward-launches /tmp/plasma-all-eight-physical-launches.json --backward-launches .lake/endpoint-backward/all-eight-physical-backward-launches.json --jacobians-input /tmp/plasma-q0r478-paired-jac001-003.json --references-input '/tmp/plasma-seven-endpoints-row-?.json' --cells-progress /tmp/plasma-native-path-cells-adaptive.json --output /tmp/plasma-q0r478-long-campaign.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-111 |
| Title | Reusing the central defect on the second physical radial label |
| Kind | Physical proof reuse and trace campaign |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-91, N-102, N-105, N-107 |
| Dependency requirement | Physical section symmetry, per-row matched reference curves and frames, checked forward residual components, each backward budget, signed ODE chain. |
| Target | Extend q0r478 to the second first-mirror bracket with one heavy central field check per signed pair. |
| Difficulty | Equality of the physical defect norm still requires retesting the forward components against a bound small enough for the original backward allowance. |
| Status | Backward row 4 and the five- and six-slab physical signed prefixes verified. The 391-row feasibility screen passed. The long secondary trace is running. |
| Lean evidence | `DommaschkTraceResidualQ0R478Back004.exact_pair`, `forward_sharp`, `physical_defect`, and `DommaschkSignedPrefixQ0R478005.common_with_pilot`. |
| Audit evidence | Both certificates use only `propext`, `Classical.choice` and `Quot.sound`. Exact keys are in the table. |
| Last updated | 25 November 2026 |
