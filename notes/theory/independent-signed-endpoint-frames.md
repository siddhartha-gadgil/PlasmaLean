# Independent signed frames for the QA2R field-line bound

Lean proves a physical backward ODE step at the first q1r456 slab where the archived backward frame differs from the reflection of the forward frame. For every point in the actual predecessor ellipsoid, the step supplies a solution throughout the outward clock interval $[129/64,130/64]$, in its recorded tube and reaching its recorded exit. The physical toroidal angle is $\pi/2-t$. A separate three-slab theorem realizes this method on an uninterrupted signed trajectory from every admitted q1r456 birth. Reaching the local slab 129 from those births requires assembling the intervening steps. [Local proof producer](../../scripts/dommaschk_kam/verify_independent_endpoint_steps.py) · [Signed chain producer](../../scripts/dommaschk_kam/verify_endpoint_signed_prefix.py)

## Why the second matrix suffices

Let $S=\operatorname{diag}(1,-1)$ be the exact QA2R section reflection. For error measured in the backward witness’s affine frame $M_b(t)$, use $S M_b(t) S$ as the comparison frame for the forward-clock field on the reflected spatial rectangle. The physical section identity transfers the resulting quadratic-form estimate to the backward field in $M_b(t)$. The forward witness can use a different frame $M_f(t)$ on this same field rectangle. Each matrix receives its own endpoint data, time derivative and archived logarithmic-norm allowance. The field evaluation and all six spatial derivatives are shared. The core reflection and moving-frame lemmas are compiled and apply to arbitrary admissible endpoint frames. [Physical reflection identity](../../PlasmaLean/Design/DommaschkSymmetricSections.lean) · [Backward field bound](../../PlasmaLean/Design/DommaschkBackwardRectangle.lean)

On q1r456 slab 129, the off-diagonal entry of the stored forward right frame has numerator $739106746475$, while the reflected backward right frame has $739106746474$. Their common denominator is $2^{40}$. The mismatch defeats the exact matching-frame hypothesis in the earlier shared-matrix proof. Both transformed matrices pass on a single seven-harmonic jet for q1r456 and q1r464. The backward q1r456 proof uses the archived central defect for **that direction**. It checks the denominator, transformed spatial growth and physical defect on the same moving trial tube before invoking local ODE existence. [Shared-field producer with independent frame mode](../../scripts/dommaschk_kam/verify_horner_endpoint_jacobian.py) · [Original q1r456 archive](../../scripts/dommaschk_kam/results/bounce_frame_q1_u456.json.gz)

| Kernel-checked result | Content key |
| --- | --- |
| q1r456 slab 129 forward transformed Jacobian | `9fa303c6126bb719d1026395d1640c785ae249f3868ba9391616d91fff31a21e` |
| q1r456 slab 129 reflected backward transformed Jacobian | `7f43a29fdee4ae034d9835efb4e3713f901a2b9135b1a454467db9dc97f6b4f9` |
| q1r464 slab 129 forward transformed Jacobian | `47085ae76f59868ac1b1191690cca92d316b706649571bceb95354414c958a96` |
| q1r464 slab 129 reflected backward transformed Jacobian | `d7b2db8fc81c14325beefa7a276cce0e533a838f2fa7141ed8e88b49df34aace` |
| q1r456 slab 129 actual backward ODE step | `e819d96b1a6033de972af2835d3ff3131c610e2f27bfea3fcab1a67559e3c634` |
| q1r456 three slabs each way from the same birth, using separate signed matrices on row 2 | `1d98a3176ab596a0b9b4011b87746028982e69af6e6e41427ca9c660fa12f5d3` |

## Exact whole-archive feasibility

An external exact-arithmetic replay covers 8 labels, 391 slabs and 2 clock directions. All **6,256** signed matrix tests pass on each label’s own rectangle enlarged to contain its reflected partner. The denominator and $2\times2$ symmetric principal-minor inequalities are checked on eight time panels with the original growth allowance of the corresponding direction. A single field jet across *two* neighbouring radial labels also passes all four matrix tests on 703 of 1,564 label-pair/slab combinations. These are feasibility counts for the physical matrix part. The local slab and signed-birth claims above have separate kernel receipts. [Independent-frame screen](../../scripts/dommaschk_kam/screen_independent_endpoint_frames.py)

| Section | Neighbouring labels | Slabs passing all four matrices on one shared field rectangle | Slabs passing all four on their two individual rectangles |
| --- | --- | ---: | ---: |
| $0$ | .470, .478 | 180 / 391 | 391 / 391 |
| $0$ | .523, .531 | 179 / 391 | 391 / 391 |
| $\pi/2$ | .456, .464 | 171 / 391 | 391 / 391 |
| $\pi/2$ | .509, .517 | 173 / 391 | 391 / 391 |

## Reproduction

```sh
lake build PlasmaLean.Design.DommaschkEndpointContinuation PlasmaLean.Design.DommaschkNativeActionModel PlasmaLean.Design.DommaschkHarmonicBlock16 PlasmaLean.Design.DommaschkOppositeHarmonic
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
$py "$dir/verify_horner_endpoint_jacobian.py" --endpoints q1r456 q1r464 --row 129 --independent-frames --output /tmp/independent-jet129.json
$py "$dir/verify_endpoint_reference_slabs.py" --endpoints q1r456 --direction -1 --range 129 129 --workers 1 --shared --output /tmp/back-reference129.json
$py "$dir/verify_independent_endpoint_steps.py" --jacobians /tmp/independent-jet129.json --references /tmp/back-reference129.json --endpoint q1r456 --direction -1 --output /tmp/back-physical129.json
$py "$dir/screen_independent_endpoint_frames.py" --output /tmp/independent-frame-screens391.json
```

To reproduce the q1r456 three-slab result from Q-16 births, use the N-102 first-row launch reports, the signed central residual reports for indices 1 and 2, the N-102 paired Jacobian for index 1, and the two `--independent-frames` Jacobians for index 2. Run the signed-prefix producer with `--endpoint q1r456 --length 3`. [N-102 launch and prefix commands](continuing-endpoint-field-lines.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-107 |
| Title | Independent signed frames for the QA2R field-line bound |
| Kind | Physical certificate method and feasibility assessment |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-91, N-102, N-105 |
| Dependency requirement | Exact section reflection, original positive and negative frames, whole-rectangle field models, and each sign’s original ODE central defect. |
| Target | A local true physical continuation through a nonconjugate frame and a composable method for the remaining secondary traces. |
| Difficulty | The two frames can differ by one dyadic tick. Separate transformed matrices must both meet their own original growth and defect budgets. |
| Status | Verified at the first nonconjugate q1r456 slab; exact feasibility covers the full archive of all eight labels. |
| Lean evidence | `DommaschkPhysicalQ1R456Back129.physical_step`, the four generated `physical_clock_log_norm` theorems and `DommaschkSignedPrefixQ1R456003.from_birth`. |
| Audit evidence | Standard axioms `propext`, `Classical.choice`, `Quot.sound`. The backward row-129 residual key is `0370c9c555fbdd317fe6c1be7693f2fafb9a60a417ae2756151691a0613b441b`. |
| Last updated | 25 November 2026 |
