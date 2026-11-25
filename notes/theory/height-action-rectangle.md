# A rectangle of prescribed heights and actions on the radial birth sector

On the same pair of original embedded QA2R tori, a joined field line from every initial position in the four section seed balls suffices for the following result. Choose any continuous height \(H(\phi)\) and action \(j(\phi)\) satisfying
\[
 |H(\phi)-h_U|\le 10^{-7},
 \qquad J_*-11/10000\ \le j(\phi)\le\ J_*+9/10000.
\]
There is a compact connected set of true launch parameters \((\phi,u)\) covering every phase \(|\phi|\le2^{-19}\). Each birth in that set has two simple first mirrors at height \(H(\phi)\) and physical action exactly \(j(\phi)\). The set stays a positive radial distance from both \(u=47/100\) and \(u=239/500\). Constant prescriptions realize every point of the closed height–action rectangle. Its widths are \(1/5000000\) and \(1/500\). [Connected physical crossing](../../PlasmaLean/Design/DommaschkSectorHeightCrossings.lean) · [Original action faces](radial-sector-prescribed-action-band.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-192 |
| Kind | Quantitative parameter continuation and connected first-well actions |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-104, N-167, N-171, N-179, N-181, N-183, N-186 and N-188 |
| Input | `DommaschkRadialRibbonMirrorBand.Through` on the canonical widened packets for all four seed balls. |
| Produces | Joint continuity of both first mirrors and their physical action in phase, radius and height, the true height derivative, and connected physical level sets for every continuous pair of prescriptions in the rectangle. |
| Status | Static analysis and the instantiated two-parent theorem have passed the Lean kernel. The common long ODE trajectories remain an explicit hypothesis. |
| Lean evidence | `DommaschkSectorHeightAction.at_height`, `lipschitz`, `DommaschkSectorHeightCrossings.family_of_paths`, `crossing`, and `DommaschkRadialHeightActionRectangle.from_nested_tori`. |
| Audit evidence | The final proof uses only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Quantitative comparison

The fixed reference values are \(h_U=5300546391395933/5000000000000000\) and \(J_*=6799610938322487/5000000000000000\). On the larger N-186 height band \([h_U-1/50000, h_U+1/30000]\), fix one certified trajectory and integrate the clipped action over \([-331/64,331/64]\). Both outer regions are strictly forbidden at that height, so its fixed-window action equals its true first-well action. The nonzero slopes at both mirror points give the ordinary derivative of this action with respect to height. Its value is the one-way flight time between those same mirrors, computed with the norm of the actual Cartesian path derivative. This holds at every height, including both boundary heights. [Height derivative and physical time](../../PlasmaLean/Design/DommaschkSectorHeightAction.lean) · [Underlying two-mirror derivative](../../PlasmaLean/Theory/Kinetic/MirrorActionTransverse.lean)

The uniform flight bound \(14<T<10000\) therefore gives \(|J(h)-J(h')|\le10000|h-h'|\) throughout that band. At the reference height, the inner radial face has action strictly below \(J_*-21/10000\) and the outer one strictly above \(J_*+19/10000\). A height displacement of at most \(10^{-7}\) costs at most \(1/1000\) of action on either face. The strict inequalities survive at all four edges and corners of the displayed rectangle. [N-186 flight estimate](radial-ribbon-mirror-height-band.md) · [N-188 physical endpoint inequalities](radial-sector-prescribed-action-band.md)

## Shared physical family

The path is chosen from the original interpolated birth at each \((\phi,u)\) before the height is chosen. Continuous dependence of the Cartesian field-line ODE on this moving birth yields joint continuity of field strength and arclength density in phase, radius and path angle. Applying the simple-first-well continuity theorem on the product with the entire N-186 height band gives jointly continuous signed endpoints \(L,R\) and action. Every launch phase in the allowed interval belongs strictly to its corresponding first well. [Moving birth and sector observables](../../PlasmaLean/Design/DommaschkSectorAction.lean) · [Continuity of first wells](../../PlasmaLean/Theory/Kinetic/ContinuousFirstWellAction.lean)

For any two continuous prescriptions in the smaller rectangle, compose this joint family with the selected height. The resulting continuous physical action minus the selected target is negative on the inner radial face and positive on the outer face. The rectangle level-crossing theorem produces the connected compact set, and compactness supplies the positive radial margin. Each prescription pair may have its own connected set. The theorem makes no single-valued radial selection or probability claim. [Planar level-crossing theorem](../../PlasmaLean/Theory/Geometry/RectangleLevelCrossing.lean)

## Reproduction

Reproduce the authenticated N-186 and N-188 receipts and then run the following commands. The verifier imports the original path implication and endpoint-face theorem into one Lean process. It chooses the tori from the endpoint-face theorem and applies the height-band result to the entries on those same tori. No new polynomial field evaluation is required.

```bash
lake build PlasmaLean.Design.DommaschkSectorHeightCrossings
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_radial_height_action_crossings.py \
  --band /tmp/plasma-n186-height-band.json --faces /tmp/plasma-n188-faces.json \
  --output /tmp/plasma-n192-height-action.json
```

The parent keys are `a4b9d0cde92051b9905b4adbfd7d9b91f5a33721ecec3eeaf7eb90307d987968` and `9ad6a7ca85047b3659a563e2c7cda7cdaa2d43496b9358b9443736e246b46edd`. The combined proof key is `3eae0924c19cd587da81a90484f0afdeeb6c3e272ffc500660ee6c43263bc894`. [Physical composition driver](../../scripts/dommaschk_kam/verify_radial_height_action_crossings.py)
