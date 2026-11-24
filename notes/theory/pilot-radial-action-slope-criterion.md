# A pointwise target for positive radial action variation

For the QA2R interpolation label $u$, a useful next certificate would bound the radial derivative of the strength $f$ and the arclength density $w$ along the first well. On an N-116 pilot trajectory, the following two signed inequalities, together with the differentiability and integrability assumptions of N-118, imply **$\partial_u J>1/3$**:

$$
\partial_u f\le -1/144,\qquad \partial_u w\ge -w/32.
$$

Lean verifies the implication and its exact numerical margin. Direct certification of the two input inequalities on the moving physical field lines remains open. A two-resolution floating-point screen at $u=0.470$ and $0.478$ tests how much room these targets allow. [Pilot criterion](../../PlasmaLean/Design/DommaschkRadialActionCriterion.lean) · [Screen driver](../../scripts/dommaschk_kam/screen_first_variation_targets.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-123 |
| Title | A sufficient signed radial variation test on the actual first well |
| Kind | Checked conditional criterion and exploratory variational screen |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-56, N-101, N-116, N-118 |
| Dependency requirement | True action cap and time floor at the same first mirrors, the signed first-variation formula and a differentiable family of nearby traces. |
| Produces | A reusable signed comparison, its pilot arithmetic, and two pointwise derivative inequalities for the next validation. |
| Difficulty | The spatial sensitivity of the actual trajectory depends on its moving initial data. A separate error estimate is needed for the radial variational ODE. |
| Status | Implication checked in Lean. Derivative hypotheses screened externally. |
| Lean evidence | MirrorActionVariation.variation_lower, DommaschkRadialActionCriterion.slope_gt_third and at_first_well. |
| Audit evidence | The displayed comparisons use only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |

## A signed comparison

Write $q=\sqrt{2(h-f)_+}$. Where $q>0$, suppose $\dot f\le-k$ and $\dot w\ge-Aw$, with $w\ge0$. Then $\dot wq-w\dot f/q\ge k w/q-Awq$. On the forbidden part both terms vanish under the clipped convention. Integrating on the well gives $J'\ge kT-AJ$, with the derivative identification supplied by the common-window first-variation theorem. At simple first mirrors the two inverse-square-root endpoint singularities are integrable. The neighboring family must continue to select the same launch-connected well. [Signed comparison](../../PlasmaLean/Theory/Kinetic/MirrorActionVariationLower.lean) · [First-variation assumptions](first-variation-across-mirror-field-lines.md)

The proved N-116 bounds are $T>9006443340496896/163793158879589$ and $J\le1146552112157123/844424930131968$. Substitution of $k=1/144$ and $A=1/32$ gives a lower bound of
$1502261560737857758027833086737/4425952855775720811033331236864\approx0.339421049$.
The proper first-well endpoints are identified by uniqueness in `at_first_well`. A genuine positive radial derivative would give a local direction of increase for action. A bound on radial drift involves variation along the field-line label on a flux surface and a dynamical reduction. [Same-path input](action-floor-for-first-mirror-flight-time.md)

## What the independent screen found

The screen integrates the spatial tangent equation $Y'=D_xF_{\rm flow}\,Y$ in geometric angle from the interpolated seed derivative. It samples $u\in\{0.470,0.478\}$, the two archived heights and geometric launch angles $-2^{-19},0,2^{-19}$. Each signed connected component includes one neighboring sample beyond each mirror. Both 512 and 2048 steps per direction were tested. The smooth seed approximation and floating-point trajectory here are distinct inputs from the certified Taylor enclosures.

| Quantity over all samples | Observed extremum | Certificate target |
| --- | ---: | ---: |
| Minimum $\partial_u w/w$ | 0.00641550 | at least −0.03125 |
| Maximum $\partial_u f$ | −0.00812799 | at most −0.00694444… |

The earlier full-strip screen sampled many more labels and reported positive radial action derivatives. The present screen resolves the two *pointwise* inputs to the new implication on the two pilot labels. A rigorous replay needs a common enclosure of the initial radial tangent, its evolution and the two spatial observable derivatives throughout each accessible row. [Earlier radial screen](../../scripts/dommaschk_kam/bounce_radial_variation.py) · [Existing full-strip data](../../scripts/dommaschk_kam/results/bounce_radial_variation_20261123.json)

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkRadialActionCriterion
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/screen_first_variation_targets.py --output /tmp/qa2r-radial-sensitivity.json
~~~
