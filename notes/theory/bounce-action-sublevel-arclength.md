# Bounce action from sublevel arclength

Fix a mirror height $h$ and a well with finite arclength measure $\mu$. Let $B$ denote field strength, and write $L(b)=\mu\{x:B(x)\le b\}$ for the arclength below each threshold. Use the project's single-passage normalization
$$
J(h)=\int \sqrt{2(h-B(x))_+}\,d\mu(x).
$$
A forbidden part of a bracket contributes zero. On a trace parametrized by $t$ with nonnegative arclength density $w(t)$, Lean identifies this expression with the existing `MirrorHeightAction.action` using $d\mu=w(t)\,dt$. The field profiles in the comparison can live on different parameter spaces. [Lean module](../../PlasmaLean/Theory/Kinetic/MirrorSublevelAction.lean) · [Mirror-height action](../../PlasmaLean/Theory/Kinetic/MirrorHeightAction.lean)

## The geometric estimate

Take an almost-everywhere lower bound $b_0$ on both fields and $h\ge b_0$. Set $V=\sqrt{2(h-b_0)}$. Integrating first over the parallel speed gives
$$
J(h)=\int_0^V L(h-v^2/2)\,dv.
$$
Indeed, for $v>0$, the local speed reaches $v$ exactly when the field strength is at most $h-v^2/2$. The endpoint $v=0$ has zero integration measure. This is the layer-cake formula and it allows plateaus in the field strength.

If $|L_1(b)-L_2(b)|\le\varepsilon$ at every $b\in[b_0,h]$, then
$$
|J_1(h)-J_2(h)|\le \varepsilon V.
$$
Equal sublevel lengths give equal actions. The factor $V$ is sharp: take two segments of unequal arclength with the same constant field $b_0$. Their action difference is their length difference times $V$.

Suppose the field and arclength measure vary with a real field-line label $\alpha$. If, uniformly over the thresholds, the sublevel lengths differ from those at $\alpha_0$ by at most $K|\alpha-\alpha_0|$ near $\alpha_0$, then at a point of differentiability
$$
|\partial_\alpha J(\alpha_0,h)|\le K V.
$$
An absolute bound on the length discrepancy gives the action-difference estimate. The derivative estimate requires the additional label dependence just stated. [Exact geometric motivation](https://arxiv.org/abs/1112.5725) · [Research question N-69](stellarator-conditions-and-geometric-questions.md)

## Application boundary

For a stellarator, the two measures must describe corresponding physical wells. The result provides a way to use arclength data without identifying individual positions across the two field lines. The candidate application still needs well continuation over launch phase, a quantitative sublevel bound, and a connection from the derivative of the action to the radial motion of the guiding centre. The Dommaschk field-line proofs currently supply a different input, namely certified positions along the magnetic field. [Physical trace](dommaschk-one-radian-and-signed-trace.md) · [Guiding-centre averaging](guiding-centre-averaging.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-72 |
| Title | Bounce action from sublevel arclength |
| Kind | Mathematical theorem |
| Addresses | G-10, Q-35 and the well-geometry question in N-69 |
| Depends on | N-69 for the research target, the project's mirror action definition, and Mathlib's finite-interval layer-cake theorem |
| Dependency requirement | Finite arclength, measurable field profiles, a common lower bound and sublevel discrepancies on the relevant heights. The derivative conclusion also requires a local label bound and differentiability. |
| Produces | Exact arclength representation, sharp action comparison, equality for equimeasurable profiles and a label derivative estimate. |
| Difficulty | The proof avoids singular differentiation in the well height by integrating over speed. The physical application still requires uniform profile data. |
| Status | Verified in the default Lean library. |
| Lean evidence | `Kinetic.MirrorSublevelAction.action_trace`, `action_eq_integral_sublevel`, `action_difference_le`, `action_eq_of_sublevels`, `abs_action_derivative_le` and `flat_wells_attain_bound` in that namespace. |
| Audit evidence | The default axiom audit includes these six entry points. |
| Last updated | 24 November 2026 |
| Additional results | N-73 gives finite node-length tests and the mesh correction. [Finite-sample theory](finite-sublevel-action-comparison.md) |
