# Independent harmonic ODE residuals at the opposite section

For the QA2R launch at \(\phi_0=\pi/2,\ u=456/1000\), Lean has proved the two physical central ODE defects and both physical continuation steps on original slab 129. Each direction uses its own centre coefficients, angular models, endpoint matrices and archived defect allowance. This covers a slab on which the two reflected frame matrices differ. [Independent signed spatial proof](signed-moving-frames-beyond-mirror-caps.md) · [Original signed packet](../../scripts/dommaschk_kam/results/bounce_frame_q1_u456.json.gz)

## Statement and arithmetic

Fix \(\sigma\in\{-1,+1\}\), elapsed time \(129/64\le t\le130/64\), and \(s=128t-259\). Let \(p_\sigma(s)\) denote the stored central curve in cylindrical meridional coordinates, \(M_\sigma(s)\) its original interpolated frame and \(b_\sigma\) its defect budget. The theorem bounds the physical central residual by

\[
\left\|M_\sigma(s)^{-1}
\left(F_{\pi/2,\sigma}(t,p_\sigma(s))-128p_\sigma'(s)\right)\right\|_2
\ \le\ b_\sigma .
\]

The field uses the true physical angle \(\pi/2+\sigma t\). Its seven angle models evaluate the harmonics of \(2(\pi/2+\sigma t)\) at the original signed clock. On the central path the three actual field polynomials \(D,n_R,n_Z\) are evaluated by Horner's rule with exact rational enclosures of the rounding. For each component the verifier forms \(\sigma n-D(128p'_\sigma)\) before bounding it, multiplies by the frame adjugate, and encloses the denominator \(D\det M_\sigma\) on eight normalized time panels. This preserves the cancellation that determines the small central ODE defect. [Signed numerical and physical certificate](../../scripts/dommaschk_kam/verify_opposite_native_defects.py) · [Kernel theorem for the physical residual](../../PlasmaLean/Design/DommaschkPhysicalCentralJet.lean)

| Direction on slab 129 | Previous sparse compilation | Harmonic field, quotient and audits | Physical step key |
| --- | ---: | ---: | --- |
| Forward | 187.777 s | 59.810 s | `21ffa94623190bd4d9b3ca39b85ee534817a0c1d1fdefe8abe77b17eb42a29c4` |
| Backward | 185.247 s | 60.700 s | `c3f977be2f853b40c092051c769f3046c21e1e583133aa3881b846ff3e732c8a` |

The two methods verified the same signed assertion with the same packet and budgets. The recorded compilation and audit times total 120.510 seconds for the harmonic proof and 373.024 seconds for the earlier sparse proof, giving a factor of 3.10 on this row. The timing excludes the already-certified static polynomial identities and the later physical-step composition. The harmonic central-defect keys are `f4b399c6fcb69fadae2a9f6c72b1e94b43453e686ca823c9176d136c659eb55d` and `9be38aa73e48cd732b9ab3845c74064da38752edec04f1b2617904ab3f337dcb` for forward and backward respectively. The central and physical-step theorems have the standard `propext`, `Classical.choice`, `Quot.sound` audit. [Physical ODE consumer](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## Finite screen and ongoing ground proofs

For each of the four original opposite-section launches, exact arithmetic checks both directions through the first original slab beyond the exterior mirror cap. The ratio below divides the outward-rounded framed central bound by that direction's own archived allowance. [Full signed screen](../../scripts/dommaschk_kam/screen_opposite_native_defects.py)

| Launch \(u\) | Original signed residuals screened | Largest ratio, rounded up | Worst signed index |
| --- | ---: | ---: | --- |
| .456 | 658 | .33534 | 185 forward |
| .464 | 660 | .38359 | 266 forward |
| .509 | 672 | .39381 | 163 forward |
| .517 | 674 | .41053 | 117 backward |

The exact screen accepts all 2,664 budgets. The q1r456 slab-129 proofs above are kernel-checked. The continuation campaign checks each later selected row's physical polynomials, angle, central quotient and signed ODE inequality before the corresponding birth trajectory may consume it. Its packet-specific backend marker changes only newly requested original reference rows. Existing sparse or harmonic receipts retain their original proof keys. A rejected harmonic proof falls back to the sparse verifier. [Six-endpoint continuation](../../scripts/dommaschk_kam/run_endpoint_continuations.py)

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkPhysicalCentralJet \
  PlasmaLean.Design.DommaschkOppositeHarmonic PlasmaLean.Design.DommaschkGroupedTrialJet
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
"$py" "$dir/verify_opposite_native_defects.py" --endpoint q1r456 --row 129 \
  --output /tmp/q1r456-native-defects129.json
"$py" "$dir/verify_grouped_endpoint_jacobians.py" --endpoint q1r456 --span 124 136 --rows 129 \
  --output /tmp/q1r456-matrices129.json
"$py" "$dir/verify_endpoint_signed_prefix.py" --endpoint q1r456 --row 129 \
  --references /tmp/q1r456-native-defects129.json --jacobians /tmp/q1r456-matrices129.json \
  --output /tmp/q1r456-native-physical129.json
"$py" "$dir/screen_opposite_native_defects.py" --output /tmp/opposite-native-screen.json
~~~

Passing `--activate-campaign .lake/secondary-trace-campaign` to the final command installs the preference for all screened endpoints after every original allowance passes. It also supports selecting particular original launches with `--endpoints`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-163 |
| Kind | Independent signed harmonic residuals and checked physical continuation |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-102, N-107, N-119, N-157 |
| Dependency requirement | Each original signed reference, frame, angle packet and defect allowance |
| Status | Kernel-checked physical defects and both signed ODE steps at q1r456 index 129. Exact budget preflight for all 2,664 signed opposite-section rows through their post-cap nodes. |
| Produces | Per-direction original physical residuals using the harmonic representation at \(\pi/2\) and a reproducible comparison with the sparse method |
| Lean evidence | `DommaschkTraceResidualQ1R456Forward129.physical_defect`, `DommaschkTraceResidualQ1R456Back129.physical_defect`, `DommaschkPhysicalQ1R456Forward129.physical_step`, `DommaschkPhysicalQ1R456Back129.physical_step` |
| Last updated | 25 November 2026 |
