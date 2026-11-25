# Every original deep-strip birth lies below the lower mirror height at every azimuth

On one pair of nested embedded QA2R invariant tori, fix the poloidal parameter at zero and interpolate their cylindrical coordinates with any label \(11/25\le u\le27/50\). For every real geometric azimuth \(\phi\), the actual field at the resulting Cartesian birth point satisfies
\[
 \lVert B(X(u,\phi))\rVert < h_L
   = 5297961656084411/5000000000000000 < h_U .
\]
The interpolation uses both corrected torus profiles at the same original \(\phi\). The result covers the complete circle, including each angle outside the two \(1/16\)-radian sectors of N-196. It also applies to any separately chosen pair with the same Q-16 closeness certificates. [Original chart and full-period transfer](../../PlasmaLean/Design/DommaschkPeriodicBirthCover.lean)

## Enclosing the original chart

The original packed grids give 161 signed toroidal frequencies for each of four coordinate profiles. The reference radius and height use the central label \(49/100\) and the frequencies \(-3,\ldots,3\). Folding each pair leaves a cosine series for radius and a sine series for height. The discarded modes, the variation \(|u-49/100|\le1/20\), and the certified \(10^{-12}\) KAM error of each torus give the uniform bounds
\[
 |R-R_{\rm ref}(\phi)|\le1/1200,\qquad |z-z_{\rm ref}(\phi)|\le1/3800 .
\]
These hold directly at the requested angle. Only the reference harmonics and the field’s double-angle inputs are reduced modulo \(\pi\). This preserves the identity of the actual birth at every representative of the angle. [Checked Fourier bounds](../../PlasmaLean/Design/DommaschkPeriodicBirthFourier.lean)

## Physical field check

Thirteen closed rational intervals cover \([0,202/64]\), hence \([0,\pi]\). On each interval the three harmonics of both coordinates and the double angle in the field use a common normalized time. Lean checks the trigonometric Taylor models against an independently rounded centre and analytic remainders. Four signed harmonic-Horner evaluations give \(D,n_R,n_Z\) and \(D-h_LR^7\). All radii are positive and the compensated expression satisfies
\[
 R^2(D-h_LR^7)\bigl(2D-(D-h_LR^7)\bigr)+n_R^2+n_Z^2
 = R^{16}\bigl(\lVert B\rVert^2-h_L^2\bigr)<0 .
\]
The largest of the thirteen outward gap bounds is \(-3004608594231896301956/2^{80}\), about \(-0.00249\), on \([112/64,128/64]\). The proof includes the entire radial strip in each of the thirteen evaluations. [Checked physical field producer](../../scripts/dommaschk_kam/verify_periodic_birth_strength.py)

N-56’s separate external calculations give the sharper launch ceiling \(1.048\), a signed magnetic flux bound and a two-sided nonturning segment through \(|\phi-\phi_{\rm birth}|\le1/8\). The present full-period Lean result concerns strength at the original birth. A periodic prescribed-action separator still needs a regular first well throughout the chosen annulus and opposite action inequalities on its two radial faces. At the opposite symmetry section the narrow pilot faces fail the action test. The wider \([0.44,0.54]\) faces remain a full-period numerical proposal. [External launch and flow bounds](dommaschk-launch-collar.md) · [Opposite action obstruction and wider bracket](opposite-section-excludes-pilot-action-strip.md)

## Replay

~~~sh
lake build PlasmaLean.Design.DommaschkPeriodicBirthCover \
  PlasmaLean.Design.DommaschkGroupedHarmonicGap PlasmaLean.Design.DommaschkCoreClearance \
  PlasmaLean.Design.DommaschkDyadicHorner
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/verify_periodic_birth_strength.py --output /tmp/periodic-birth.json
~~~

The generated module `PeriodicBirthFamilyCache.DommaschkPeriodicOriginalBirths` exports `full_period` and `original_births`. Apply `DommaschkPeriodicBirthCover.at_original` to `full_period` for a named pair of corrected profiles. The same command with `--screen` runs only the exact rational preflight.

The accepted family key is `ce6bed6b9de9e0074b88f779a654961c2f70f75508148f9a56492f5a243b5a0c`. An independent invocation reproduced the final receipt byte-for-byte. The 96 imported or generated packages include 52 field evaluations, 13 coordinate and harmonic joins, and the final full-period composition. Their recorded compile-and-audit times sum to 807 seconds. The largest single process used 4,823,172 KiB. Both exported declarations use only `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-198 |
| Kind | Full-period candidate field certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-56, N-61, N-135, N-177, N-196 |
| Dependency requirement | Original Q-16 strip closeness, the packed signed Fourier columns, harmonic Taylor remainders and the three identified QA2R field polynomials. |
| Produces | True Cartesian birth strength below both selected heights for all original deep-strip radii and every real phase on one common embedded pair. |
| Status | The true launch chart and the physical field on a full period are covered by Lean proof certificates. |
| Lean evidence | `DommaschkPeriodicBirthFourier.birth_error`, `.low_eq`, `DommaschkPeriodicBirthCover.at_original`, `.from_period` and generated `DommaschkPeriodicOriginalBirths.original_births`. |
| Audit evidence | Source-bound rational input and model checks, original-field identification and independent declaration axiom audits. |
| Last updated | 25 November 2026 |
