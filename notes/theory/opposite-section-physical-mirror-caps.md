# Signed physical mirror brackets at the opposite section

At section $\phi=\pi/2$, take one of the four original QA2R radial launches. On each signed clock, the physical field strength at the early cap is below the chosen mirror height, and at the later cap it is above it, for every position in the corresponding original endpoint tube. Lean has checked eight strict cap signs per launch, covering two heights and two outward clocks. The rows have independent signed central paths, coefficients and error bounds. [Physical endpoint generator](../../scripts/dommaschk_kam/verify_opposite_mirror_caps.py)

The table records the open time brackets as **numerators in units of 1/64 radian**. Both signs have the listed brackets. Given a continuous strength profile following the corresponding cap tubes, there is a crossing in each indicated open interval. Extending the actual path from its original birth to those tubes and excluding earlier contacts are separate obligations. [Opposite-section physical continuations](signed-moving-frames-beyond-mirror-caps.md)

| Original radial label | Lower-height bracket | Upper-height bracket | Four crossing implications |
| --- | --- | --- | --- |
| 0.456 | (320, 322) | (327, 328) | `dc5804eacf0359d9bf9d807942d121e7f58b04879726a112db6a45539cbd5b34` |
| 0.464 | (321, 322) | (328, 329) | `8a50b3e9f841753c401f51b7a6f7270fa72061a54a3115af0c64f1c33277e603` |
| 0.509 | (326, 327) | (334, 335) | `d90bad66f11a7e0e32409a03baa5a66aabf1c423fa45ac02b7959359974ef0d9` |
| 0.517 | (326, 328) | (334, 336) | `14ebe5eca6edeab1f763e440229470dd79593243fac5b67d7e48fcd04711ff54` |

The finite sign test uses a rational polynomial with a uniform error bound for the positive multiple $R^{16}(h^2-|B|^2)$ on each original tube. At the cap the true strength lies strictly on the indicated side of $h$ if the signed value of the polynomial exceeds the error. Positivity of $R$ and nonnegativity of the field norm and height recover the sign of $h-|B|$. The intermediate value theorem then gives each crossing. The endpoint test is reusable for any positive multiplier and Taylor model. [Scalar sign theorem](../../PlasmaLean/Certificates/MirrorGapAtTime.lean) · [Physical Taylor models](../../scripts/dommaschk_kam/verify_coarse_action_models.py)

## Replay

~~~bash
for launch in q1r456 q1r464 q1r509 q1r517; do
  .venv-ws/bin/python scripts/dommaschk_kam/verify_opposite_mirror_caps.py \
    --endpoint "$launch" --output "/tmp/plasma-n153-$launch.json"
done
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-153 |
| Kind | Verified signs on physical endpoint tubes and conditional crossing theorems |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-107, N-115, N-133 |
| Dependency requirement | Original forward and backward physical models at both endpoint heights |
| Produces | Thirty-two endpoint inequalities and sixteen intermediate-value crossing implications |
| Status | Kernel verified on the original opposite-section tubes. The signed trajectory to each mirror and first-contact identification require further evidence. |
| Lean evidence | `TrajectoryTaylorModel.strength_at` and `DommaschkOppositeMirrorCrossingsQ1R456`, `Q1R464`, `Q1R509` and `Q1R517` packages |
| Audit evidence | All four endpoint packages use propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
