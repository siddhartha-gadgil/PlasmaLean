# Two regular mirrors and a prescribed action on a Dommaschk launch cell

[N-60](dommaschk-local-action-graphs.md) constructs two separated root arcs on each of the two symmetry sectors.

[N-59](dommaschk-phase-faces.md) checks the two radial faces on six launch sectors.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-57 |
| Kind | Computation and mathematical method for N-54 and N-56 |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-33 and N-52 for the actual profiles, N-53 for regular mirror births, N-54 for the fixed action, N-56 for the field and initial strip |
| Dependency requirement | Oriented field-line continuation from the launch to its first mirror on each side, the arclength density, and bounds on the one-way action. |
| Produces | A continuous interval of regular mirror heights and a unique height at the prescribed action for each launch in a small cell. Reusable theorems for trajectory error, arclength, inversion by height and differentiation with respect to a launch parameter. |
| Difficulty | A local well can be certified with a low-degree reference trajectory. Extending a fixed-action strip around the full phase circle requires control of variations between well-separated launches. |
| Status | Local candidate conclusions externally checked. The general existence, reparametrization and action lemmas are verified in the default Lean build. |
| Lean evidence | `dist_le_rational_step`, `regularMirrorBirth_of_parametrized_crossings`, `action_eq_well_of_crossings`, `unique_height`, `hasDerivAt_action`. |
| Audit evidence | Independent step sizes, constant-field and polynomial fixtures, signed material derivatives, both allowed and forbidden regions, and a deliberately enlarged cell that loses its certificate. |
| Patched by | [N-61, Lean replay and physical launch theorem](dommaschk-mirror-certificate-replay.md) |
| Last updated | 23 November 2026 |

## Which launches and what is proved

Use the physical Dommaschk field in candidate units, with the interpolated C-to-A launch cut of N-54. Take |α| ≤ 2⁻³⁵ in geometric radians and |u−0.49| ≤ 2⁻²². The two screening heights are h₁ = 1.0595923312168822 and h₂ = 1.0601092782791866. For every launch in this cell and every height in [h₁,h₂], the accessible segment containing the launch has a simple turning point on each side. The action j is the integral of √(2(h−‖B‖)) with respect to arclength **once** between these points. This is the scaled action convention of N-54. [Original action and mirror classes, Burby–MacKay–Naik §2.1](https://arxiv.org/html/2211.13367#S2.SS1) · [Launch and field definitions](dommaschk-launch-collar.md)

| Height | First root on each side, in absolute geometric-angle displacement | Enclosure of j over all launches |
| --- | --- | --- |
| h₁ | [159/32, 319/64] | [1.32513, 1.33227] |
| h₂ | [41/8, 329/64] | [1.37004, 1.37752] |

These bounds use steps of 1/64 radian. The outward derivative of ‖B‖² exceeds 0.0047908 wherever the field strength meets the height interval. The coordinate trajectory error stays below 2.777 × 10⁻⁷ in the Euclidean norm of (R,z). Repeating the calculation with a 1/32 step gives wider brackets that still separate the two actions from the target. The test includes both directions without relying on symmetry. [Mirror checker](../../scripts/dommaschk_kam/bounce_mirror_pilot.py) · [Action checker](../../scripts/dommaschk_kam/bounce_action_pilot.py)

For each launch, exactly one height between h₁ and h₂ realizes j = 1.3599221876644974. Integrating the positive part on a fixed trace bracket equals integrating between the first two turning points because the outer intervals are forbidden. The integrand is continuous in height even at a turning point. The positive arclength density and strict accessibility at the launch make the integral strictly increasing. The two endpoint actions then give existence and uniqueness by the intermediate value theorem. The theorem chooses a height at fixed launch. Constructing winding curves at fixed height requires varying the launch radius and covering every phase. [Action and inversion theorems](../../PlasmaLean/Theory/Kinetic/MirrorHeightAction.lean)

## Widening the phase interval

Transferring each birth along its field line to a common azimuth φ=0 extends the phase half-width from 2⁻³⁵ to **2⁻¹⁶ radians**, a factor of 524,288, with the same radial interval. If L(φ,u) is the launch chart, propagate the difference e between the true trace and L during the short transfer. Starting from e(α)=0 leaves only the difference between the actual field-line slope and the chart derivative to enclose. Throughout the transfer the field strength is below 1.043853. The launch and its image at the common section are therefore inside the same well. After this transfer the long trace uses a single absolute field phase for all births.

At the same 1/64 step, the enclosed actions over this larger cell are **[1.32063,1.33712] at h₁** and **[1.36405,1.38459] at h₂**. Both still strictly bracket j=1.3599221876644974. With the absolute azimuth measured from the common section the lower root lies on each side in |φ|∈[317/64,161/32], the upper in |φ|∈[81/16,167/32]. Relative to the actual birth one must widen each bracket by its phase half-width. The whole height window has outward squared-strength derivative >0.001801. A 1/32 step on this larger cell does not certify the upper crossing. [Common-section verification](../../scripts/dommaschk_kam/bounce_common_section.py) · [Machine-readable cross-checks](../../scripts/dommaschk_kam/results/bounce_mirror_cell_20261123.json)

## How the calculation is checked

A floating-point field trace proposes degree-seven polynomial segments. All subsequent acceptance decisions use outward-rounded integer or rational arithmetic. Each segment bounds the residual of its polynomial against the real field equation, the mismatch between neighbouring proposals, and the largest eigenvalue of the symmetric part of the spatial Jacobian on the trial tube. This one-sided bound controls changes in Euclidean distance even when the skew part of the Jacobian is large. Positive radius and toroidal field component keep the field-line equation regular. The rational radius estimate closes strictly inside the tube on each successful step. Lean proves the general comparison and continuation results. The concrete dyadic data and their transfer to each physical field line are checked by the external script. [Trajectory error and continuation](../../PlasmaLean/Theory/Fields/LogNormTrajectory.lean) · [Zgliczyński, §2.5, logarithmic norms in validated ODE integration](https://ww2.ii.uj.edu.pl/~zgliczyn/papers/ks/c1lohner.pdf)

Along a trace in geometric angle the arclength density is R‖B‖/Bφ. Lean constructs its increasing arclength clock from positivity on the finite interval. The derivative sign of ‖B‖² at a positive mirror height has the same sign in arclength as the derivative of ‖B‖ in geometric angle. For action quadrature the checker divides each step into eight subintervals. It encloses both the speed and the positive square-root integrand everywhere on each panel, including panels traversing a turning point. [Arclength and physical field direction](../../PlasmaLean/Theory/Kinetic/MirrorArclength.lean)

## A reusable transverse derivative

Let Q be the gap under a square root, A the arclength density and a,b two simple roots of Q with Q>0 between them. Write Q(s)=(s−a)(b−s)H(s). A divided difference extends H continuously through both roots, with endpoint values Q′(a)/(b−a) and −Q′(b)/(b−a). It has a positive minimum on the closed interval. For the change of variable s=a+L sin²θ, L=b−a, 0≤θ≤π/2, the derivative of the action with respect to a launch parameter p has the regular integrand

$$
2L^2\sin^2\theta\cos^2\theta\,A_p\sqrt H + A Q_p/\sqrt H .
$$

The partial derivatives are at fixed trace coordinate s. For the scaled physical action use Q=2(h−‖B‖). The endpoint-motion terms integrate to zero. Lean proves the differentiated integral under explicit regularity and domination hypotheses on the family. Candidate work still has to verify those hypotheses and the sign of the integrated transverse derivative. A double-root fixture shows why simplicity is essential. The source also gives a complementary procedure switching to signed parallel velocity near an individual mirror. [Regularization and derivative theorems](../../PlasmaLean/Theory/Kinetic/MirrorAction.lean) · [Burby–MacKay–Naik, Appendix I.2](https://arxiv.org/html/2211.13367#A9.SS2)

## Reproduction and limits

```sh
env OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_mirror_pilot.py --step 1/64
env OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_action_pilot.py --step 1/64
env OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/bounce_action_pilot.py --common-section
```

The birth-centred commands default to step 1/32. The common-section commands default to 1/64. At that resolution the enlarged half-widths 2⁻²⁴ in phase and 2⁻¹⁷ in radius lose the proof. The lower bound on the squared-strength derivative becomes negative and the upper crossing cannot be bounded from above by the end of the trace. Widening only the radial half-width to 2⁻¹⁹ still certifies the mirrors. The pilot cell covers a small part of the sampled strip and provides no lower bound on the fraction of a thermal population. The common-section result motivates propagating first variations around other launch phases and testing the action on the two radial faces. Covering one field period with cells as narrow as the larger pilot would take over 100,000 cells in angle alone. A wider validated tube or a geometric monotonicity estimate would be more informative than a direct replication at this width. Physical operating scales and targets are open by user decision. [Full-strip requirements](dommaschk-mirror-screen.md)
