# Independent signed central defects at the opposite section

Starting at toroidal angle \(\pi/2\), the original forward and backward references have different coefficients. Their moving frames can also differ after vertical reflection. They can each use a high-order field evaluation shared across consecutive slabs. This preserves the signed reference, the derivative with respect to outward elapsed time, the moving frame and the original defect allowance at every index. [Opposite-section single rows](independent-harmonic-central-defects.md) · [Independent frames](independent-signed-endpoint-frames.md) · [Group-clock field enclosures](grouped-physical-central-defects.md)

## Signed original references

Fix a sign \(\sigma\in\{-1,1\}\) and indices \(a\le i<b\). Let \(s=128t-2i-1\) on original slab \(i\), and \(v=(2i+1-a-b+s)/(b-a)\) on the group. The generator constructs degree-twelve enclosures of the actual signed \(R_\sigma,z_\sigma\) and seven trigonometric channels at \(2(\pi/2+\sigma t)\). Each sign has its own three physical field enclosures on this clock. Affine substitution and outward rounding yield a degree-seven model on each original slab for \(D_\sigma,N_{R,\sigma},N_{z,\sigma}\). [Signed group construction](../../scripts/dommaschk_kam/grouped_opposite_central.py)

The numerators of the pulled error use
\[
  \sigma N_{R,\sigma}-D_\sigma \dot R_\sigma,\qquad
  \sigma N_{z,\sigma}-D_\sigma \dot z_\sigma .
\]
Here the dots denote derivatives with respect to the positive elapsed time on that signed original row. The adjugate of the original signed moving frame multiplies these errors. Eight rational time panels bound the two components and bound the product of the frame determinant and \(D_\sigma\) away from zero. The norm test uses the original signed allowance \(d_{\sigma,i}\). It gives the following inequality at every real time on the slab, in the exact physical field and the original frame \(P_{\sigma,i}\).
\[
 \bigl\|P_{\sigma,i}(t)^{-1}
   \bigl(V_\sigma(t,x_{\sigma,i}(t))-\dot x_{\sigma,i}(t)\bigr)\bigr\|_2
 \le d_{\sigma,i}.
\]
The original physical ODE step consumes that result together with a separate spatial Jacobian and frame-growth inequality. [Signed defect theorem producer](../../scripts/dommaschk_kam/verify_grouped_opposite_defects.py) · [Physical step composition](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## Exact feasibility

The planner tested all 2,664 signed original budgets through one entire slab beyond the last exterior mirror node. An initial group has eight original slabs. If either signed check exceeds its own allowance, the planner bisects the group and tests both children. The results below give the maximum ratio of proposed bound to original budget in each direction, rounded upward. [Exact group planner](../../scripts/dommaschk_kam/plan_opposite_central_groups.py)

| Section radius | Slabs per sign | Groups | Largest forward ratio | Largest backward ratio |
| --- | ---: | ---: | ---: | ---: |
| 0.456 | 329 | 42 | 0.868 | 0.924 |
| 0.464 | 330 | 43 | 0.876 | 0.907 |
| 0.509 | 336 | 45 | 0.857 | 0.864 |
| 0.517 | 337 | 45 | 0.765 | 0.794 |

The group \([49,57)\) at \(u=.456\) contains different forward and reflected backward coefficients on all eight original rows. On row 49 the largest differences in the two coordinate polynomials are \(3738456321/2^{80}\) and \(4546625536/2^{80}\). The largest proposed ratios within this group are \(933296117726/2555574892389\) forward on row 51 and \(1212208628605/3033080444969\) backward on row 56. [Original signed packet](../../scripts/dommaschk_kam/results/bounce_frame_q1_u456.json.gz)

Lean checked all sixteen original signed pointwise defect theorems in this group. On row 49 the two physical ODE proofs are `DommaschkPhysicalQ1R456Forward049.physical_step`, key `3326e204392e4fa18d1805ef17886c1b5e26e7592cae974fbd9e5ea0dc4635c8`, and `DommaschkPhysicalQ1R456Back049.physical_step`, key `b639f5039759ac76f4d66bb3bfe984a12b837bbf49a123ae99addfd736bb0f86`. The field enclosures, sixteen central defects and both signed ODE steps passed the `propext`, `Classical.choice` and `Quot.sound` audit.

On exactly these eight rows, building the sixteen single-row field and defect proofs took 1,206.442 seconds across distinct stages. The grouped field, restriction and defect checks took 380.668 seconds across 34 stages, a factor of 3.17. Peak process RSS in the grouped proof was 3,960,280 KiB. Both measurements exclude the static coefficient proofs reused by the two verifiers. The original single-row verifier replayed its two original keys at row 49. The four endpoint workers now use the grouped method via a packet-bound plan and pass each completed pair of signed theorems to the existing trajectory composition. The exact screen over 2,664 signed allowances and the sixteen individually proved theorems measure different stages of this calculation. [Physical campaign selection](../../scripts/dommaschk_kam/campaign_grouped_central.py)

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkVariableHorner PlasmaLean.Design.DommaschkGroupedTrialJet \
  PlasmaLean.Design.DommaschkOppositeHarmonic PlasmaLean.Design.DommaschkPhysicalCentralJet \
  PlasmaLean.Design.DommaschkEndpointContinuation
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
"$py" "$dir/plan_opposite_central_groups.py" --output /tmp/opposite-central-groups.json
"$py" "$dir/verify_grouped_opposite_defects.py" --endpoint q1r456 --span 49 57 \
  --output /tmp/opposite-defects049-056.json
"$py" "$dir/verify_grouped_endpoint_jacobians.py" --endpoint q1r456 --span 48 60 \
  --rows 49 --output /tmp/opposite-matrices049.json
"$py" "$dir/verify_endpoint_signed_prefix.py" --endpoint q1r456 --row 49 \
  --references /tmp/opposite-defects049-056.json --jacobians /tmp/opposite-matrices049.json \
  --output /tmp/opposite-physical049.json
~~~

To enable the plan for each running endpoint, pass `--activate-campaign .lake/secondary-trace-campaign` to the planner. The independent signed singleton verifier can replay any chosen original row through `verify_opposite_native_defects.py --endpoint q1r456 --row 49 --output /tmp/opposite-singleton049.json`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-170 |
| Kind | Grouped central defect on the original signed opposite-section tubes |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-107, N-119, N-152, N-157, N-163, N-166 |
| Dependency requirement | Original signed central coordinates, clock harmonics, moving frame and separate allowance at every index |
| Status | Sixteen original defects at \(u=.456\) and both physical ODE steps at row 49 checked. All four full-length plans pass the exact arithmetic screen. |
| Produces | Shared high-order physical field models for consecutive original rows on each signed branch and their original pointwise physical defect |
| Lean evidence | `DommaschkTraceResidualQ1R456{Forward,Back}049.physical_defect` and the corresponding theorems through 056, `DommaschkPhysicalQ1R456Forward049.physical_step` and `DommaschkPhysicalQ1R456Back049.physical_step` |
| Last updated | 25 November 2026 |
