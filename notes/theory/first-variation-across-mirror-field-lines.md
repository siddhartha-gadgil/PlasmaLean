# First variation of mirror action across field lines

At fixed mirror height $h$, let $f_s(t)$ be field strength along a field line with launch label $s$, and let $w_s(t)$ be its physical arclength density in a common time coordinate. The field-line derivative of the clipped longitudinal action has separate contributions from the two observables. Put $q(t)=\sqrt{2(h-f_{s_0}(t))_+}$. Then at a regular base label,

$$
J'(s_0)=\int_a^b \left(\dot w(t)q(t)-\frac{w_{s_0}(t)\dot f(t)}{q(t)}\right)\,dt.
$$

Both contributions vanish on the forbidden side under the clipped convention. Values at the two turning points do not affect the integral. This is a launch-label derivative at fixed height. The earlier identity $\partial_h J=T$ varies height on a fixed field line. [First variation and sensitivity bounds](../../PlasmaLean/Theory/Kinetic/MirrorActionVariation.lean) · [Height derivative](mirror-action-flight-identity.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-118 |
| Title | First variation of the physical mirror action across field lines |
| Kind | Candidate-independent analytic proof |
| Addresses | G-6, G-10, Q-1, Q-16, Q-19, Q-35 |
| Depends on | N-85, N-93, N-104 |
| Dependency requirement | The weighted-gap formula, square-root secant inequality, and inverse-gap integrability at transverse contacts. |
| Produces | A launch derivative including both field strength and changing arclength, and an upper bound from action and flight time. |
| Difficulty | A turning point moves with the label and the derivative of parallel speed is singular there. The domination estimate is taken at the base field line. |
| Status | Verified in the default Lean library |
| Lean evidence | MirrorActionVariation.hasDerivAt_integral_sqrt, transverse_window, first_variation and abs_variation_le. |
| Audit evidence | The declarations use the standard Lean axiom set. |
| Last updated | 25 November 2026 |

## Hypotheses and proof

Use a common compact interval $[a,b]$ and define $P_s(t)=2w_s(t)^2(h-f_s(t))$. The arclength density is nonnegative. The two profiles are continuous on the time window for labels near $s_0$. At almost every time the base weight is positive, the base strength differs from $h$, and the profiles have the stated label derivatives. Assume a fixed-base secant bound $|P_s(t)-P_{s_0}(t)|\le C(t)|s-s_0|$ for nearby labels, almost everywhere, with $C/\sqrt{|P_{s_0}|}$ integrable. Two simple zeros, one in each half of the window and no others, suffice for the null-zero-set and integrability conditions when $P_{s_0}$ and the nonnegative majorant $C$ are continuous. The simple-zero derivatives here are with respect to the time coordinate. [Two-crossing criterion](../../PlasmaLean/Theory/Kinetic/MirrorActionVariation.lean)

Since $w_s\sqrt{2(h-f_s)_+}=\sqrt{(P_s)_+}$, the scalar inequality $|\sqrt{u_+}-\sqrt{v_+}|\sqrt{|v|}\le|u-v|$ bounds all the difference quotients by the same base-profile majorant. Almost-everywhere differentiation and dominated convergence give $\int \dot P/(2\sqrt{(P_{s_0})_+})$. Expanding $\dot P$ yields the displayed formula. When the window contains a single accessible component with forbidden caps, the integral is the action between its first mirrors. [Clipped scalar estimate](../../PlasmaLean/Theory/Kinetic/MirrorActionTransverse.lean) · [First-well identification](../../PlasmaLean/Theory/Kinetic/MirrorActionEnvelope.lean)

## A quantitative target for C2

If $|\dot w|\le A w$ and $|\dot f|\le B$, the integral triangle inequality gives

$$
|J'(s_0)|\le A J(s_0)+B T(s_0).
$$

Here $T=\int w/q$ is the one-way flight time. The comparison theorem takes integrability of these quantities and of the variation integrand. The identity also allows cancellation between arclength and strength contributions when absolute-value bounds are too large. To use it for QA2R, the family must vary a physical transverse flux or field-line label, and its two observable derivatives must be controlled on that family. The current height derivative and the positive-volume birth theorems do not supply these transverse derivatives. Converting an action derivative into radial drift also requires the guiding-centre reduction in the selected coordinates. [Action comparison](../../PlasmaLean/Theory/Kinetic/MirrorActionComparison.lean) · [Cylindrical tangent controls](cylindrical-action-sensitivity.md)

## Replay

~~~bash
lake --wfail build PlasmaLean.Theory.Kinetic.MirrorActionVariation
lake env lean scripts/check_axioms.lean
~~~
