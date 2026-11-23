# Two mirror-height screens on the Dommaschk field

[N-56](dommaschk-launch-collar.md) verifies bounds on the continuous launch strip and a two-sided field-line segment.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-54 |
| Kind | Candidate computation and proof criteria for N-53 |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-33, N-49, N-51, N-53 |
| Dependency requirement | The specified rational field and two Fourier launch curves; the physical application also needs a regular fixed-action family, its clock and flux measure. |
| Produces | A rejected family, a second candidate strip, and inequalities whose continuum verification would establish separated winding graphs. |
| Difficulty | Moderate for launch geometry; research for validated field-line continuation and bounce-action derivatives. |
| Status | Reproducible floating-point screen. Abstract turning-point and winding-graph criteria proved in Lean. |
| Lean evidence | `MirrorWell.two_simple_mirrors`, `regularMirrorBirth_on_height_window`, `PeriodicLevelGraphs.separated_level_graphs`, `radius_error_of_action_residual`. |
| Audit evidence | Model and time conventions follow N-53. Physical targets remain open by user decision. |
| Alternatives | N-56 implements the launch geometry and first field-line enclosure. [N-57](dommaschk-regular-mirror-cell.md) reaches both mirrors on a local cell. |
| Last updated | 23 November 2026 |

## What was computed

Launches interpolate between two outboard Fourier seed cuts. The coordinate u is the linear interpolation fraction, and α is geometric toroidal launch angle modulo π. Between the cuts, each trajectory follows the supplied rational magnetic field. On the connected mirror well containing the launch, arclength and field strength give the scaled action j = ∫√(2(h−|B|)) ds, with h = E/μ. Two energies are tested at **one** prescribed action in each screen. In dimensional variables the full parallel bounce time is 2√(m/μ) ∂j/∂h. The launch flux density still needs the species charge and the physical normalization to give the reduced symplectic form. [Burby, MacKay and Naik, §2.1](https://arxiv.org/html/2211.13367#S2.SS1) · [Implementation](../../scripts/dommaschk_kam/bounce_screen.py)

| Screen | Result on refinement |
| --- | --- |
| Midpoint of the common mirror-height range, j = 2.74354295 | At 128 launch phases the action residual was below 1.4 × 10⁻⁹. Near α = 2.8108 and 0.36725 a local maximum crosses the mirror height. On refining the launch, the turning point jumps by about 0.09 rad and the prescribed action lies in the gap between two bounce classes. Retire this full-circle branch. |
| Deeper well, j = 1.35992219 | At h = 1.05959233 and 1.06010928 the roots lie respectively in u = [0.50588, 0.52725] and [0.45344, 0.47437] on the sampled phases. The minimum paired separation is 0.0523 in launch coordinates. Two successive 16-fold local angular refinements reduce the largest turning-point steps to about 0.0005 rad. |

On the second strip, 0.44 ≤ u ≤ 0.54, all sampled phases and a full height window passed the mirror test on the interpolated traces. The fine grid used 9 radial launches and 128 phases, with 1,536 steps per half trace. The minimum centre and endpoint field-strength margins were 0.01463 and 0.00494. On the trace in the selected height range, the smallest oriented derivative in geometric angle was 0.0007864. At the two energies the smallest radial action secant was 0.81566 and the two face margins exceeded 0.0110. These margins do not account for interpolation error or variation between sampled launches. The full run includes the original failed selection, local refinements, input hashes, solver versions and an independently solvable quadratic well. [Numerical record](../../scripts/dommaschk_kam/results/bounce_screen_20261123.json)

## What would certify this result

1. Enclose the launches, the transverse flux form, and the field lines out to both ends of the trace window. Establish strictly oriented crossings whenever |B| is in the height window. Centre and endpoint bracketing then yields exactly two simple roots, with the interval between them accessible. A positive change of clock relates geometric-angle derivatives to arclength derivatives. [Turning-point criteria](../../PlasmaLean/Theory/Kinetic/MirrorWellCriterion.lean)
2. Bound j and its transverse derivative on the continuous strip at both heights. A positive derivative and strict face inequalities at the target action give one winding graph at each height. Strict ordering and periodicity give a uniform positive separation. With a lower derivative bound m, a certified action residual e gives radius error ≤ e/m. The derivation needs one continuously identified well at each height. [Graph and radius-error theorems](../../PlasmaLean/Theory/Geometry/PeriodicLevelGraphs.lean)
3. For the physical band, identify the return section and reduced dynamics globally, including possible repeat representations of a well, and compare the true trajectory and the reduced one over the proposed horizon. Establish the area form, clock, annular tangency and error budget in N-51. Then apply the declared distribution and axis-distance observable of N-53 separately to thermal ions and electrons. A choice of field scale, length scale, population, coverage, excursion and horizon is deferred. [Acceptance predicate](hamiltonian-bounce-band-test.md)
