# A measured action-drift budget for a first radial exit

At the reference upper height \(h_U\) the two radial faces already have true birth-centered first-well actions on the original nested embedded QA2R tori. For every \(|\phi|\le 2^{-19}\), every physical measurement on the inner face \(u=0.470\) is strictly less than \(J_*-21/10000\); every one on the outer face \(u=0.478\) strictly exceeds \(J_*+19/10000\). Both faces have at least one such measurement. A measurement uses the actual Cartesian arclength action between the first mirrors around the original birth at \(\phi\). ODE uniqueness makes the inequalities apply also to an independently chosen trajectory through that birth. The two completed endpoint paths suffice for this statement. [Physical face theorem](../../PlasmaLean/Design/DommaschkPhysicalActionExit.lean) · [Quantitative endpoint estimates](radial-sector-prescribed-action-band.md)

Let \(r,\phi,J\) be a radial label, a phase and a scalar observation along a proposed motion on \([0,T]\). Suppose \(r\) is continuous and starts in \((0.470,0.478)\). Up to and including any possible first radial exit, suppose \(|J(t)-J(0)|\le d\). If the path reaches either radial face, its phase there must belong to the certified sector and its observed value there must equal a physical first-well action at \(h_U\) through the original birth on that face. Then
\[
  |J(0)-J_*|+d\le 19/10000
  \quad\Longrightarrow\quad
  0.470<r(t)<0.478\quad (0\le t\le T).
\]
To prove it, take a first radial boundary hit. The drift bound puts its observation in the closed interval \([J_*-19/10000,J_*+19/10000]\), whereas each measured physical boundary value is strictly outside that interval. Strict face margins allow equality in the budget. [First-exit theorem](../../PlasmaLean/Theory/Geometry/ActionFaceBarrier.lean)

A bounded correction provides a second set of hypotheses. Suppose, while the radius lies in the closed strip,
\[
 (J+\varepsilon g)'=\varepsilon^2 k,\qquad |g|\le G,\quad |k|\le K,\quad K\ge0.
\]
One may use \(d=2|\varepsilon|G+T\varepsilon^2 K\). The correction identity, its quantitative bounds and identification of the observed action at a possible exit are conditions for a physical guiding-centre application. The phase condition also limits this test to passages whose potential radial exit occurs in the measured sector. No full-period first-well theorem or 332-row propagation for intermediate radii is required for this implication. [Oscillatory correction estimate](../../PlasmaLean/Theory/Geometry/AveragedConfinement.lean)

## Replay

```sh
lake build PlasmaLean.Design.DommaschkPhysicalActionExit
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_sector_faces.py \
  --exit-faces --flow /tmp/plasma-n171-flow.json --output /tmp/plasma-n199-measured.json
```

The independent birth-centered face theorem `DommaschkPhysicalActionExitOn391_328_48_16_48_16_8_5.from_nested_tori` has key `0bb8dcbc2d715246797c58b7ccc170d0cc85e33b6de0f1a0e59e21637fef9ca4`. Its kernel audit uses only `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-199 |
| Kind | Candidate-specific measured first-exit criterion |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-58, N-162, N-171, N-182, N-188 |
| Dependency requirement | True birth-centered first wells on the two faces, short-window ODE uniqueness and a pathwise action-drift or corrected-derivative bound. |
| Produces | An explicit closed drift budget 19/10000 for the first radial exit test on the QA2R small sector. |
| Status | Physical face bounds and the exit implication verified. Application to a guiding-centre population requires field-to-orbit identification and a drift estimate. |
| Lean evidence | `DommaschkPhysicalActionExit.of_endpoint_witnesses`, `.stays_inside`, `.stays_inside_of_correction` and the generated common-torus instance. |
| Last updated | 25 November 2026 |
