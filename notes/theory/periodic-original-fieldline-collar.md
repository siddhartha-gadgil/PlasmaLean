# A signed nonturning field-line collar for every original QA2R birth

Take the original \(C,A\) torus interpolation at fixed poloidal parameter zero, any \(u\in[11/25,27/50]\), and any real geometric azimuth \(\phi\). A single field-line trajectory through this birth exists for every signed angular displacement \(-1/256\le t\le1/256\). It satisfies
\[
 \|B(X(t))\|<h_L-1/1000,\qquad
 |R(t)-R(0)|\le |t|/6,\qquad |z(t)-z(0)|\le |t|/6.
\]
In particular, each coordinate moves by at most \(1/1536\) in this interval. The same nested embedded invariant tori work for every launch. A version taking the two Q-16 closeness witnesses directly permits composition on a named pair. [Signed collar theorem](../../PlasmaLean/Design/DommaschkPeriodicBirthCollar.lean)

The Cartesian position has the exact specified initial point and is continuous on the closed interval. At every interior time, including launch, its ordinary derivative is the autonomous velocity
\[
 \frac{X_1^2+X_2^2}{X_1 B_2(X)-X_2 B_1(X)} B(X).
\]
The denominator is positive throughout the closed interval. Increasing \(t\) follows the magnetic field at positive arclength speed. The two-coordinate ODE has a derivative within the full closed clock even at its endpoints. [Cartesian transfer](../../PlasmaLean/Design/DommaschkPeriodicCollarCartesian.lean)

## Why the enclosure holds between launches

N-198 bounds the true birth radius and height around three-harmonic functions of its original angle. Keep that angle as the common Taylor variable. Widen the radius and height bounds by \(T/6\), with \(T=1/256\). Each double-angle sine and cosine changes by at most \(2T=1/128\) between launch and observation. All three physical polynomials \(D,n_R,n_Z\) and the compensated polynomial \(D-h_L R^7\) use those widened errors. The check covers points throughout each trial box, before any assertion about where the physical trajectory goes. [Original chart and its errors](periodic-original-birth-strength.md)

Twenty-five closed sectors cover the periodic birth angle. Their exact enclosures give \(R>1/2\), \(D>0\), \(|n_R/D|,|n_Z/D|\le1/6\), and strict negativity of the physical squared-strength gap at \(h_L-1/1000\). The smallest denominator bound is approximately \(0.463798\). The largest component ratio allowance is approximately \(0.153140\). The least remaining squared-gap margin after lowering the height is approximately \(0.00003962\) on \([104/64,112/64]\). [Sector certificates](../../scripts/dommaschk_kam/verify_periodic_birth_collar.py)

For example, the unsplit sector \([96/64,112/64]\) gives a positive gap allowance of about \(0.00119637\), which fails the certificate test. Dividing it at \(104/64\) gives strictly negative allowances on both closed halves.

The field-line ODE is smooth on these regular boxes. Its exact velocity belongs to the certified component interval. Starting at the true birth, \(x_0+s v\) therefore stays inside the spatial box for every \(s\in[0,T]\) and every admissible velocity \(v\). The rectangular ODE existence theorem supplies an enclosed forward solution and an enclosed backward solution. Reversing the backward clock and gluing at their identical initial state yields one differentiable field line with the stated bounds. [Validated ODE step](../../PlasmaLean/Design/DommaschkBounceFlowStep.lean) · [Signed clock gluing](../../PlasmaLean/Design/DommaschkMirrorTwoSided.lean)

N-56 previously enclosed a longer signed collar through \(\pm1/8\) using external directed arithmetic and subdivision along the flow. Its longer endpoint, the first mirror pair for arbitrary phase, and the periodic action-face inequalities remain separate verification steps. The clock here is geometric angle and the coordinate excursion uses the candidate length convention. Physical operating targets remain open. [External full-period collar](dommaschk-launch-collar.md)

## Replay

~~~sh
lake build PlasmaLean.Design.DommaschkPeriodicCollarCartesian \
  PlasmaLean.Design.DommaschkGroupedHarmonicGap PlasmaLean.Design.DommaschkCoreClearance \
  PlasmaLean.Design.DommaschkDyadicHorner PlasmaLean.Design.DommaschkGroupGapRadius \
  PlasmaLean.Design.DommaschkPairedActionProfiles
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/verify_periodic_birth_collar.py --output /tmp/periodic-collar.json
~~~

The complete producer audits `DommaschkPeriodicOriginalCollar.full_period`, `.original_collar`, and `.cartesian_field_line`. Its `--screen` option checks only the exact rational sector choices. The optional `--fields-only --field-spans START STOP` mode can precompute disjoint angular ranges using the same content-addressed artifacts.

The accepted family key is `88eb438064c11deaab0929ea2c8f82fa328629938221d7333a82f940e6378280`. Independent verification reproduced the final receipt byte-for-byte. The 180 audited packages include 100 physical polynomial evaluations. Their recorded compile-and-audit times sum to 1,457 seconds. The largest single process used 4,977,976 KiB. All three final declarations and the five generic field and ODE transfer lemmas use only `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-203 |
| Kind | Uniform physical ODE and field certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-56, N-61, N-114, N-177, N-198 |
| Dependency requirement | Certified original launch profiles, smooth identified physical field, compensated strength and positive denominator on swept boxes, and a two-sided ODE joining theorem. |
| Produces | A signed nonturning geometric-angle collar on the complete original phase and radius annulus, with explicit coordinate and strength bounds and an autonomous Cartesian field-line lift. |
| Status | Original-torus family result, signed physical ODE and Cartesian field line verified across all 25 sectors. |
| Lean evidence | `DommaschkPeriodicBirthCollar.outward`, `.at_original`, `.from_period`, `Passage.cartesian` and generated `DommaschkPeriodicOriginalCollar.cartesian_field_line`. |
| Audit evidence | Standard axioms for all final and transfer declarations, byte-identical replay, and a wider exact sector rejected before subdivision. |
| Last updated | 25 November 2026 |
