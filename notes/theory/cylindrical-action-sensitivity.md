# Action sensitivity for two angle-parametrized curves

Suppose two curves are written in cylindrical coordinates as $(R(t),t,Z(t))$ and $(S(t),t,W(t))$. Their arclength densities are the norms of the actual Cartesian velocities. At any common differentiability point the difference between the two densities is at most

$$\sqrt{(R-S)^2+(R'-S')^2+(Z'-W')^2}.$$

In the orthonormal cylindrical frame the first tangent has components $(R,R',Z')$, up to ordering. Both curves use the same frame at a common angle, so the bound follows from the reverse triangle inequality. Concentric circles attain equality. A circle and a helix can have the same position at one angle and different speeds there. Transverse slope changes about a circle of positive radius $r$ satisfy the stronger bound $0\le\sqrt{r^2+u^2+v^2}-r\le(u^2+v^2)/(2r)$. [Cartesian tangent and sharp examples](../../PlasmaLean/Theory/Kinetic/CylindricalActionSensitivity.lean)

Let $J$ denote the integral of $\sqrt{2(h-B)_+}$ against physical arclength over $[a,b]$. Suppose changing the strength profile while retaining the first curve's arclength changes $J$ by at most $E$. Assume the replacement profile has lower bound $B_0$ almost everywhere and the Euclidean discrepancy of the three tangent components above is at most $\eta$ in the open interval. Under the measurability and integrability assumptions in `physical_action_window`, the action difference for the two actual curves is bounded by

$$E+\sqrt{2(h-B_0)_+}\,(b-a)\,\eta.$$

The theorem uses interior derivatives, so segment joins and turning points can be endpoints of integration. In a constant-strength field, two concentric circles attain the coefficient of $\eta$. [Physical finite-window theorem](../../PlasmaLean/Theory/Kinetic/CylindricalActionSensitivity.lean) · [Action with changing arclength](mirror-action-changing-arclength.md)

For the Dommaschk physical angular velocity $V_\phi$, a same-angle estimate $\lVert V_\phi(x)-V_\phi(y)\rVert\le L\lVert x-y\rVert$ bounds the arclength-density difference by $\sqrt{1+L^2}\lVert x-y\rVert$ where both radii and toroidal field components are positive. An application across birth labels requires this full velocity discrepancy, separation of the two field lines and the fixed-density field-profile error $E$. A one-sided logarithmic norm certifies growth of the tube and gives only that part of the needed information. [Physical density theorem](../../PlasmaLean/Design/DommaschkArcDensitySensitivity.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-93 |
| Kind | Candidate-independent geometric inequality with a physical specialization |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-85, N-87, N-88 |
| Dependency requirement | Common angular parameter, integrable tangent components and a fixed-density profile error estimate. |
| Produces | Sharp pointwise and finite-window action bounds using actual Cartesian velocities. |
| Difficulty | Certify small spatial velocity and fixed-density field discrepancies on neighboring physical wells. |
| Status | General theorem in the default Lean library. Physical specialization compiled on demand. |
| Lean evidence | `CylindricalActionSensitivity.physical_action_window`, `circle_action_attains`, `DommaschkArcDensitySensitivity.density_lipschitz`. |
| Audit evidence | All public theorems checked with only standard axioms. |
| Last updated | 25 November 2026 |
