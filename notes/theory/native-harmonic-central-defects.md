# Faster certification of the second radial trace with native harmonic central defects

For the QA2R phase-zero launch at $u=239/500$, Lean checks both original signed physical central ODE defects on row 4 in **66.5 seconds**. The previous sparse-polynomial forward proof and reflected backward proof for the same row took 163.89 and 3.06 seconds respectively. The new construction also passed on row 317, the first lower-mirror bracket, in 67.3 seconds. These timings use the same workstation with previously compiled identities for the three physical field polynomials. Both methods certify the archived allowances. The row-4 proof composed with both actual physical Jacobians into a five-slab signed trajectory through the common entry of every admitted birth. [Signed residual verifier](../../scripts/dommaschk_kam/verify_native_endpoint_residuals.py) · [Physical prefix consumer](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## What Lean checks

Evaluate the original field denominator $D$ and numerators $n_R,n_Z$ on the archived central curve by expanding in the constant, sine and cosine channels of harmonics $2\phi,4\phi,6\phi$. Each channel uses a bivariate Horner scheme in radial displacement and height; the three field models retain the common normalized angular variable. This reduces repeated interval arithmetic in the kernel. Earlier exact polynomial identities justify these seven-channel evaluations for the physical QA2R field. A reusable lemma takes the three certified memberships along the physical clock and gives the pulled-back Euclidean defect bound. Eight closed time panels cover each central quotient. A positive lower bound for its denominator is part of the certificate. [Physical defect from three model memberships](../../PlasmaLean/Design/DommaschkPhysicalCentralJet.lean) · [Whole-slab quotient and reflection proof](../../scripts/dommaschk_kam/templates/native_central_residual.lean.tpl)

The forward proof uses the original polynomial trajectory with zero central-coordinate uncertainty. It retains the outward rounding and remainders created during field and quotient evaluation. The two reflected stored coordinate polynomials and both endpoint frame matrices are checked against the actual backward row. The final dyadic bound must fit both archived defect allowances; the two signed proof declarations each state their own allowance. The external exact screen passes this rounded comparison on all 391 original q0r478 signed pairs. The largest rounded bound divided by the smaller of the two budgets is $44725044569/166469178427$ on row 20, approximately $0.26867$. This screen identifies feasible rows; the accepted kernel receipts below identify completed sample proofs. [Exact budget screen](../../scripts/dommaschk_kam/screen_native_endpoint_residuals.py)

| Kernel result | Content key |
| --- | --- |
| Row 4 forward central defect | `21d8ea626270cd6a26045c22f121fc7c117054e5991228e0af04a66eabf2cd37` |
| Row 4 backward central defect | `d84e3728aa410d1dc781750ab3aaa2fb1bdfa84ede7b7c17021fb04a65993925` |
| Row 317 forward central defect | `91cea8bbc894c113b3069a0f270601452458ab3f2d1fe74723d1ed29c4f79248` |
| Row 317 backward central defect | `a0ef998cf1e5b9463242a4e5e29a28c337052be55a07c9de741770d3244d8493` |
| Five-slab signed birth theorem using the new row-4 parents | `754c9bf30139be8d79172ca54ef52a783311955973ffeca98775630a93fa95e9` |

The largest individual Lean check on the native row-4 calculation peaked at 3,953,516 KiB RSS. The speedup is about $2.5$ for the signed central proof of the benchmark row. Each row still requires its separate spatial Jacobian and physical step assembly before it can extend a birth path. Certifying a local central residual at row 317 supplies one such input; the signed trajectory must reach the bracket to prove a physical first contact at this label.

## Reproduction

Start from the coordinate and frame archives of N-102 and the original signed launch reports. The five-slab replay uses the first three existing signed residuals and the four paired Jacobians, as in N-111.

```bash
lake build PlasmaLean.Design.DommaschkPhysicalCentralJet PlasmaLean.Design.DommaschkNativeActionModel
py=.venv-ws/bin/python
d=scripts/dommaschk_kam
$py "$d/screen_native_endpoint_residuals.py" --endpoint q0r478 --output /tmp/q0r478-native-screen.json
for i in 4 317; do
  $py "$d/verify_native_endpoint_residuals.py" --endpoint q0r478 --row "$i" --output "/tmp/q0r478-native-$i.json"
done
cache=.lake/secondary-trace-campaign/q0r478
$py "$d/verify_endpoint_signed_prefix.py" --endpoint q0r478 --length 5 \
  --forward-launches /tmp/plasma-all-eight-physical-launches.json \
  --backward-launches .lake/endpoint-backward/all-eight-physical-backward-launches.json \
  --references "$cache"/references/00{1,2,3}.json /tmp/q0r478-native-4.json \
  --jacobians "$cache"/jacobians/00{1,2,3,4}.json --output /tmp/q0r478-native-five.json
```

Use `--native-residuals` in the resumable campaign command of N-111 to select this method. Each signed receipt binds its physical polynomial inputs, clock and common quotient to the original packet and compiler. The prefix consumer supports mixtures of the three already checked central methods. [Campaign runner](../../scripts/dommaschk_kam/verify_endpoint_trace_campaign.py) · [Earlier sparse and reflected certificates, N-111](reflected-secondary-defect-budget.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-119 |
| Title | Faster certification of the second radial trace with native harmonic central defects |
| Kind | Numerical certificate method and benchmark |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-94, N-102, N-105, N-111 |
| Dependency requirement | Exact harmonic expansion of the three physical polynomials, checked angular models, the original central reference and endpoint frames, both signed budgets and the per-row ODE consumer. |
| Produces | Kernel-checked physical central defects using harmonic Horner enclosures, compatible with mixed archived methods in a signed birth trajectory. |
| Difficulty | Preserve residual cancellation through rounded local polynomial operations and retest the physical norm against the smaller signed allowance. |
| Status | Compiled on rows 4 and 317 in both directions; the five-slab physical composition and whole-archive exact feasibility screen passed. |
| Lean evidence | `DommaschkPhysicalCentralJet.of_memberships`, `DommaschkNativeCentralQ0R478004` and `…317` physical defects, `DommaschkSignedPrefixQ0R478005.common_with_pilot`. |
| Audit evidence | `propext`, `Classical.choice` and `Quot.sound` only. |
| Last updated | 25 November 2026 |
