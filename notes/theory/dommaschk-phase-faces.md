# Action bounds on six sectors of the Dommaschk launch circle

[N-60](dommaschk-local-action-graphs.md) constructs two separated root arcs on each of the two symmetry sectors.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-59 |
| Kind | Candidate computation and method for N-54, N-57 and N-58 |
| Addresses | Q-35, G-6, G-10 |
| Depends on | N-52 for profile errors, N-54 for the proposed action and heights, N-56 for the actual field, N-57 for trajectory and quadrature checks, N-58 for the radial barrier |
| Dependency requirement | An oriented trace, an accessible launch, a forbidden cap on each side, and bounds on the positive-part action. Simple crossings additionally identify a regular mirror pair. |
| Produces | Two radial face inequalities on six positive-width angular sectors. Reusable moving-frame and launch-well envelope theorems. |
| Difficulty | The conservative field-line tube and the quadrature both widen with the phase interval. A full turn and the true orbit's action defect remain research. |
| Status | General theorems compiled in Lean. Candidate intervals checked externally in directed arithmetic. |
| Lean evidence | `MovingFrame.exists_rational_step`, `MirrorActionEnvelope.exists_launchWell`, `LaunchWell.action_bounds`, `LaunchWell.action_strictly_increases`. |
| Audit evidence | Exact shear, rejected singular frame, compensated field-strength identity, exact harmonic rotation, independent integration steps, and a nonintegrable bounce-time example. |
| Last updated | 23 November 2026 |

## Candidate results

Use the same rational field, Q-16 profile enclosures, heights and single-passage action as N-57. Set $j_*=1.3599221876644974$. For every launch in each row the action at $u=0.44$ is below the target and the action at $u=0.54$ is above it. The displayed margins are rounded down. They apply throughout the height window because the inner face is tested at the largest height and the outer face at the smallest. The radial inequalities quantify over the two faces. Regularity in the intervening radii needs its own certificate. [Symmetry-section records](../../scripts/dommaschk_kam/results/bounce_phase_faces_20261123.json) · [Other sectors](../../scripts/dommaschk_kam/results/bounce_phase_chart_20261123.json)

Write $a=\arctan(1/2)$. Angles and half-widths are in geometric toroidal radians modulo $\pi$.

| Sector centre | Half-width with two simple mirrors on each face | Inner margin | Outer margin |
| --- | ---: | ---: | ---: |
| $0$ | $2^{-10}$ | 0.02319 | 0.00477 |
| $\pi/2$ | $2^{-9}$ | 0.00484 | 0.01026 |
| $a$ | $2^{-10}$ | 0.00366 | 0.01848 |
| $\pi/4+a$ | $2^{-12}$ | 0.01443 | 0.01736 |
| $\pi/2+a$ | $2^{-12}$ | 0.01512 | 0.01775 |
| $3\pi/4+a$ | $2^{-10}$ | 0.00764 | 0.01561 |

At the two centres with half-width $2^{-12}$, a second check verifies the face inequalities on the larger half-width $2^{-10}$. It integrates the fully accessible launch core for a lower bound and includes all positive contributions up to strictly forbidden caps for an upper bound. The margins on the wider cells exceed 0.00919 on the inner face and 0.01207 on the outer face. The combined face sectors cover $14/1024$ radians, about 0.44% of a period. This is angular coverage on the two chosen faces. It supplies no trapped-birth probability. [Core and cap calculation](../../scripts/dommaschk_kam/bounce_phase_chart.py)

## Mathematical checks

A continuous field strength below the selected height at launch and above it at both ends has a unique pair of *first* hits. The intervening open interval is accessible. These launch intervals are nested as height increases, and the action increases strictly for positive density at launch. At a fixed height the action over a connected accessible core containing the launch is a lower bound. Integrating the clipped integrand over the full capped interval gives an upper bound, even if it includes part of another well. One Lean example has strict caps and infinite bounce time. A second example merges two wells and gives a jump of at least 1/2 in the launch-connected action even though the field strength is continuous. Physical-clock or graph applications still require separate regularity and continuity evidence. [Launch-well proofs and time counterexample](../../PlasmaLean/Theory/Kinetic/MirrorActionEnvelope.lean)

For the long trace write the spatial position as $x=p+Mv$, where $p$ is a reference trajectory and the columns of $M$ approximately track its variations. On every step the interval checker verifies invertibility, bounds the transformed residual $M^{-1}(F(p)-p')$, and bounds the signed growth from $M^{-1}(D F\,M-M')$. The actual solution is enclosed by an ellipsoid in physical coordinates. A common azimuth and exact rational coordinates for the angular origin allow the same physical polynomial to be evaluated off symmetry. Both tracing directions are checked. Compensating the polynomial for the toroidal field component before evaluating near a mirror sharpens the squared-strength bound. The moving-frame existence estimate is a Lean theorem. Its hypotheses for the particular candidate are checked by the external calculation. [Moving-frame theorem](../../PlasmaLean/Theory/Fields/MovingFrameTrajectory.lean) · [Interval implementation](../../scripts/dommaschk_kam/bounce_phase_frame.py)

## Readiness

A half-width of $1/256$ still leaves the face ordering unresolved at two of the general centres with the core and cap method. An angular sweep at the present width is expensive. The nearby graph test should first establish a radial secant bound and two local roots on the same phase interval. Global transport additionally needs a regular family along the physical trajectory, a bound on action drift, physical radial excursion, a time scale and a birth measure. [Two-face barrier](action-faces-and-winding.md)
