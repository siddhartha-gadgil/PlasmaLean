# A radial first-exit bound with varying mirror height

On the original phase-zero birth chart, the two independent completed endpoint calculations give a first-exit test for every \(h\in[h_U-1/500000,h_U]\) and \(|\phi|\le 2^{-19}\). The true birth-centred first-well action at \(u=47/100\) is at most \(1146552112157123/844424930131968\). At \(u=239/500\) it is strictly greater than \(j_*+19/10000-452(h_U-h)\). These inequalities apply even when an observer independently selects its solution and first-well contacts. The endpoint proofs use one and the same pair of original embedded invariant tori. [Physical and first-exit theorems](../../PlasmaLean/Design/DommaschkHeightBandActionExit.lean)

| Field | Value |
| --- | --- |
| ID | N-206 |
| Kind | Physical inequality and conditional pathwise confinement theorem |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-202 outer-face response, N-199 independent original face observations, the pilot whole-height action cap, and the first-exit and corrected-action lemmas |
| Produces | A two-face certificate for every phase and height in the stated rectangle, plus a closed first-exit action-drift budget of \(249/250000\) |
| Status | Lean-verified for independent original endpoint field lines. The pathwise conclusion requires the stated physical observations and action-drift budget |
| Lean evidence | `DommaschkHeightBandActionExit.of_endpoints`, `stays_inside`, `stays_inside_of_correction`, and generated `from_nested_tori` |
| Audit evidence | The original endpoint and corrected-action declarations use `propext`, `Classical.choice` and `Quot.sound` |
| Updated | 2026-11-25 |

## Physical endpoint bounds

The calibrated inner trajectory has two actual first contacts inside \([-325/64,325/64]\) for every height in the larger original archived band. Its lower-height first wells already satisfy the upper-height action cap. The ODE on the closed well identifies the archived cylindrical density with the norm of the Cartesian field-line derivative. At the outer endpoint, the transverse outward branches put both first contacts inside \([-327/64,327/64]\), and the checked upper bound of 452 on the derivative of the action with respect to height controls the change from \(h_U\). ODE uniqueness compares both strength and Cartesian density for any other enclosed physical line through the same birth. Uniqueness of the first contacts then identifies its observed integral. The independently observed contacts can initially be specified without a search-window restriction. [Outer derivative and flight time](../../PlasmaLean/Design/DommaschkOuterFaceFlight.lean) · [Original inner bounds](../../PlasmaLean/Design/DommaschkActionFlightFloor.lean)

## First exit at a varying height

Suppose a continuous radius \(u(t)\) starts strictly between \(47/100\) and \(239/500\). At each potential first boundary contact up to \(T\), require that the actual birth phase is in the specified sector, its mirror height is in the closed band above, and the measured \(J(t)\) equals the one-way Cartesian field-line action in the first well around that birth. A qualifying observation uses a true physical line through the birth, enclosed on \([-327/64,327/64]\). The height and phase at different times may be different. The two endpoint ODE solutions suffice for this test.

If \(|J(0)-j_*|+d\le 249/250000\) and \(|J(t)-J(0)|\le d\) until a possible first exit, then the radius remains strictly between the two faces throughout \([0,T]\). At the lowest permitted height, the outer lower bound is exactly \(j_*+249/250000\) before the strict inequality is applied. The inner upper bound is already below \(j_*-21/10000\). Thus equality in the stated drift budget is allowed. The same result follows if \(J+\varepsilon g\) has derivative \(\varepsilon^2 k\) in the strip, \(|g|\le G\), \(|k|\le K\), and \(|J(0)-j_*|+2|\varepsilon|G+T\varepsilon^2K\le249/250000\). Establishing this drift estimate and the physical observations for a particular particle population remains a separate dynamical question. [First-exit proof](../../PlasmaLean/Theory/Geometry/ActionFaceBarrier.lean) · [Witness replay](../../scripts/dommaschk_kam/verify_height_band_action_exit.py)

## Replay

~~~sh
lake build PlasmaLean.Design.DommaschkHeightBandActionExit
.venv-ws/bin/python scripts/dommaschk_kam/verify_height_band_action_exit.py \
  --outer /tmp/plasma-n202-outer-flight.json --output /tmp/plasma-n206-height-exit.json
~~~

The authenticated parent key is `c5cbf2b552dd27ba47bf8a82c059efc5b0a761d3a7f4ece7290106bf001014d6`. The final witness and corrected-action audit key is `76f1bfcad190200dc620e9f7b04414c15b0f63508c44395aac1f5fccca5bc976`.
