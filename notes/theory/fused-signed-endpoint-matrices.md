# Faster spatial certificates for the other six signed field lines

On the section at `π/2`, Lean verified 24 original moving-frame Jacobian bounds for the birth at `u = 0.456` in 224.699 seconds of kernel checking. The previous implementation took 628.054 seconds for the same twelve slabs and both signed clocks. The true forward and backward field lines starting from the common Q-16 tori were then reconstructed on `[-15/16,15/16]` using all 24 new bounds. [Same-input comparison](../../scripts/dommaschk_kam/compare_fused_endpoint_jacobians.py) · [Physical prefix assembly](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## What the kernel checks

One wide Taylor enclosure of the three field polynomials and their six spatial derivatives can serve several consecutive time slabs. The producer restricts each of these nine models to the original row's affine clock and projected trial rectangle. The time-dependent coordinates and harmonics satisfy the true section clock. For each required signed frame, the kernel checks its affine interpolation, quotient-rule Jacobian and transformed symmetric matrix against the original logarithmic-norm rate. Dyadic arithmetic and the smallest sufficient subdivision of the time interval use the certificates of N-177 and N-187. [Spatial field models](../../scripts/dommaschk_kam/verify_ribbon_dyadic_jet.py) · [Frame matrices](../../PlasmaLean/Design/DommaschkDyadicFrameModel.lean) · [Time-panel inequalities](../../PlasmaLean/Design/DommaschkJacobianPanels.lean)

The coordinate check, the restricted jet and up to six pairs of signed frame proofs are elaborated in a single module. Each original signed matrix also has a small importable module with its original declaration names. Its receipt binds the original packet, checked field and matrix parents, Lean version, source and compiled artifacts. The two physical ODE steps consume that matrix and the independently checked central defect for their own clock. At section zero a reflected rectangle can serve both directions after checking the frame identities and the smaller rate. At section `π/2` each signed frame goes through its own matrix test. [Matrix producer](../../scripts/dommaschk_kam/verify_fused_endpoint_jacobians.py) · [Signed central residuals](../../scripts/dommaschk_kam/verify_grouped_opposite_defects.py)

### A backward frame that differs under reflection

For the `u = 0.456` birth on section `π/2`, row 130 is a slab on which the forward frame and the reflection of the stored backward frame differ at both ends. In units of `2⁻⁴⁰`, the upper-right entry at the left endpoint is 739106746475 forward and 739106746474 reflected backward. At the right endpoint the entries are 760745654314 and 760745654313. Both matrices used the certified rectangle with coordinate radii `(1973752001972229767, 3722379485257871125) / 2^80`. The signed growth rates were respectively `37919870526811850481525 / 672031604938037553323674` and `56879806465897365865409 / 1008047407378609143539989`. [Independent frame reconstruction](../../scripts/dommaschk_kam/screen_independent_endpoint_frames.py)

The actual local IVP theorems `DommaschkPhysicalQ1R456Forward130.physical_step` and `DommaschkPhysicalQ1R456Back130.physical_step` have keys `37a2e85b37250a87ed59913ae4b9df0f6f1298d4e04e485d4b7553bb8713b8f5` and `5dabbc105d32d71d7710adcbc20a8b457808a80173c1443166b320cf23611862`. Each applies to every admissible row-130 incoming state. Separately, the 60-slab prefix joins the original launch with the two signed chains and exhibits them on the same Q-16 tori as the pilot. Its key is `56877f640258d832b95ce02793fa5a95a7a927c07f4b4fc5aa7fee83c0d65dbd`. [Continuation from either physical section](../../PlasmaLean/Design/DommaschkEndpointContinuation.lean)

## Timing and production selection

The timed case used `q1r456`, indices 48 through 59, one Lean thread per process, the same endpoint packet, and the 96 original audited declarations. Each stage includes its axiom check. The nine static harmonic data packages cost 50.557 seconds once and are shared by both implementations. The sum of the remaining kernel times fell by a factor of 2.795. The measurement covers these twelve rows on this workstation.

| Kernel stage | Earlier implementation | Fused implementation |
| --- | ---: | ---: |
| Nine field and derivative models | 197.183 s | 95.118 s |
| Per-row clock, restrictions and signed matrices | 430.871 s | 64.281 s |
| Individual importable assertions and audits | Included above | 65.300 s |
| **Total after shared static data** | **628.054 s** | **224.699 s** |

The normal campaign selects this backend separately for each endpoint after its two local physical IVPs have passed. Each subsequent batch verifies the selection against that endpoint's own packet and signed proof artifacts. Existing completed rows can continue to supply the original declarations. On test inputs the selector rejected a different endpoint, a mismatched backward Jacobian and a missing signed physical step. [Endpoint-specific selection and replay](../../scripts/dommaschk_kam/enable_fused_endpoint_spatial.py)

All six production continuations passed their own two local IVPs. The entries below identify the exact package keys by prefix. The phase-zero rows use one spatial matrix for the two physical directions. Each opposite-section row uses two independently checked frame matrices.

| Section | Birth parameter | Pilot group | Pilot row | Forward physical proof | Backward physical proof |
| --- | ---: | --- | ---: | --- | --- |
| Zero | 0.523 | [228, 240) | 230 | `e50a2754f4edcb` | `c2694c928795bd` |
| Zero | 0.531 | [96, 108) | 97 | `a4baaa4fe069c9` | `00a06de7ca5573` |
| π/2 | 0.456 | [120, 132) | 130 | `37a2e85b37250a` | `5dabbc105d32d7` |
| π/2 | 0.464 | [48, 60) | 50 | `7ea7a98256a3e9` | `e03ca392a2cd2c` |
| π/2 | 0.509 | [36, 48) | 38 | `66347a09e7385a` | `f263db3a34df3b` |
| π/2 | 0.517 | [48, 60) | 50 | `9a0301d077f197` | `440ee9967b65bf` |

## Reproduction

With the campaign's original signed central receipts present, the following commands reproduce the timings, the nonconjugate local IVPs, and the endpoint-specific selection.

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
py=.venv-ws/bin/python
src=scripts/dommaschk_kam
c=.lake/secondary-trace-campaign
lake build PlasmaLean.Design.DommaschkDyadicFrameModel
"$py" "$src/verify_grouped_endpoint_jacobians.py" --endpoint q1r456 --span 48 60 --output /tmp/q1-regular.json
"$py" "$src/verify_grouped_endpoint_jacobians.py" --endpoint q1r456 --span 48 60 --fused --output /tmp/q1-fused.json
"$py" "$src/compare_fused_endpoint_jacobians.py" --original /tmp/q1-regular.json --fused /tmp/q1-fused.json --output /tmp/q1-timings.json
"$py" "$src/enable_fused_endpoint_spatial.py" --campaign "$c/q1r456" --span 120 132 --row 130
"$py" "$src/verify_endpoint_signed_prefix.py" --endpoint q1r456 --length 60 \
  --forward-launches /tmp/plasma-all-eight-physical-launches.json \
  --backward-launches .lake/endpoint-backward/all-eight-physical-backward-launches.json \
  --references "$c/q1r456/references/"{001..059}.json \
  --jacobians "$c/q1r456/jacobians/"{001..047}.json /tmp/q1-fused.json --output /tmp/q1-signed60.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-189 |
| Kind | Physical certificate implementation and throughput measurement |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-120, N-175, N-177, N-187 and the original independent signed endpoint frames |
| Produces | Reusable signed matrix certificates for grouped endpoint jets, with independent reverse frames at the opposite section |
| Status | Both directions on twelve original opposite-section rows, the nonconjugate local pair, and twelve endpoint-specific rollout IVPs are kernel-checked. The new 60-row prefix is attached to the common tori. |
| Lean evidence | `DommaschkSignedPrefixQ1R456060.from_birth`, `.common_with_pilot` and both signed row-130 physical IVPs |
| Audit evidence | Matrix and physical results use `propext`, `Classical.choice` and `Quot.sound`. Matched certificates use identical archived rates, projected trial radii and theorem lists. |
| Last updated | 25 November 2026 |
