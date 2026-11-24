# A finite radial comparison of the first-well action

On the certified QA2R pilot at $u=0.470$, the action difference between the two archived heights exceeds **0.0284**. A separate comparison of two field lines can use this calibrated dependence on height. For the second label $u=0.478$, two explicit pointwise comparisons would force $J_{478}(h)-J_{470}(h)>1/375$. The height $h$ and the shifted height $h+1/18000$ must both lie in the pilot band. An external exact-arithmetic screen passes on all 325 paired rows in each direction. The physical path attachment for the entire second well and the kernel replay of the paired comparisons are in progress. [Pilot theorem](../../PlasmaLean/Design/DommaschkFiniteRadialAction.lean) · [Physical ground proof](../../scripts/dommaschk_kam/verify_pilot_height_scale.py)

## Comparing different first wells

Let $f,g$ be strengths and $w,v$ be arclength densities on two field lines parametrized by the same geometric angle. The first well of $f$ at height $H$ has endpoints $l,r$, and the first well of $g$ at $h$ has endpoints $L,R$. Both contain the section coordinate zero. If on $(l,r)$
$$
H-f(t)\le h-g(t),\qquad s\,w(t)\le v(t),
$$
then $L\le l<r\le R$ and $s J_f(H)\le J_g(h)$, with nonnegative outer density and continuous data on each closed well. Indeed the entire inner interval is accessible on the second line. Its first contacts must therefore lie at least as far from the section. Monotonicity of square root gives the integral comparison there, and the rest of the outer well contributes a nonnegative integral. This uses the actual first contacts even when they lie outside the pilot window. [Reusable comparison](../../PlasmaLean/Theory/Kinetic/MirrorActionHeightShift.lean)

On one original pilot trajectory N-116 supplies $T>9006443340496896/163793158879589$ and $J\le1146552112157123/844424930131968$ throughout the closed height band. Lean identifies $T$ with the derivative in height of the same action. Consequently this time floor applies to every height secant, and its reciprocal bounds the Lipschitz constant of the inverse height coordinate. Applying the lower secant to the two archived endpoint heights proves the absolute action-width bound. [Same-path time bounds](action-floor-for-first-mirror-flight-time.md) · [Height derivative](mirror-action-flight-identity.md)

For radial displacement $1/125$ take $H=h+1/18000$ and $s=3999/4000$. The two comparisons become
$$
f_{478}(t)\le f_{470}(t)-1/18000,\qquad w_{478}(t)\ge(3999/4000)w_{470}(t).
$$
The lower bound on the pilot action increment from $h$ to $H$, less at most $J_{470}(H)/4000$, exceeds $1/375$. The resulting difference quotient between these two labels exceeds $1/3$ if their complete physical profiles satisfy the comparisons. Monotonicity on the intervening radial interval is a further question. [Radial derivative criterion](pilot-radial-action-slope-criterion.md)

## What the archive establishes

The two original position packets are compared on a common normalized clock. Both strength ceilings $17/16$ and the arclength comparison pass on all 325 rows in the external rational screen. For the field drop, direct independent substitution in the Taylor models leaves 161 rows inconclusive. Evaluating the squared strength at the reference centres and using spatial derivatives to enclose its variation on each output box closes all 325. The smallest cleared-denominator margin for this method occurs at row 324 and exceeds $1.22\times10^{-7}$. Both archive directions are covered by the common reflected reference and the larger of the two output radii at each label. The cleared-polynomial margin has different units from the field difference. [Exact screen and four sufficient inequalities](../../scripts/dommaschk_kam/screen_paired_action_profiles.py)

The screen works with the finite sparse Dommaschk field, both packets' archived position envelopes, the same geometric angle and rational error bounds. It needs the second trajectory to occupy all the relevant tubes and the field and arclength inequalities to be proved for their arbitrary occupants in Lean. This two-label comparison requires no radial derivative of a neighboring solution family. [Second-label mirror brackets](secondary-qa2r-mirror-brackets.md) · [Incoming submirror proof](secondary-qa2r-submirror-exclusion.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-126 |
| Title | Comparing two physical first-well actions by a finite shift of height |
| Kind | Checked physical height calibration, conditional two-line comparison, external exact screen |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-101, N-104, N-113, N-116, N-120, N-121 |
| Dependency requirement | An actual signed pilot with its action cap and flight times on the same trajectory. Two neighboring trajectories for the finite comparison. |
| Produces | Exact inverse height modulus, positive pilot action width, a finite-difference test and 325 paired profile checks. |
| Difficulty | Absolute interval errors obscure the small difference between two close physical profiles. Spatial recentering recovers the needed margin. |
| Status | Grounded pilot calibration and conditional comparison verified in Lean. Full paired field-profile calculation checked externally. |
| Lean evidence | LaunchWell.transfer_height, DommaschkFiniteRadialAction.height_scale, endpoint_width, first_action, pair_test, and the ground DommaschkFiniteRadialAction326.from_birth. |
| Audit evidence | Two independent ground builds had key be7e66d9ad95735593f42ea8f60040f007e2290190cbe390594f22a861e1c7d6 and used only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkFiniteRadialAction
.venv-ws/bin/python scripts/dommaschk_kam/verify_pilot_height_scale.py \
  --flight /tmp/plasma-action-flight-bounds326.json --output /tmp/qa2r-height-scale.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/screen_paired_action_profiles.py --output /tmp/qa2r-paired-profiles.json
~~~
