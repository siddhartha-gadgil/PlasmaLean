# Radial variation at the physical section-zero pilot birth

At the QA2R birth with interpolation label \(u=47/100\) and azimuth \(\phi=0\), Lean proves that the physical field strength decreases with \(u\) at a rate of at least \(1/144\), and that the physical arclength density increases with \(u\). The result uses the same nested embedded tori as the eight signed traces of N-120. The two inequalities provide initial data for the pointwise action criterion in N-123. [Birth derivatives](../../PlasmaLean/Design/DommaschkPilotBirthVariation.lean) · [Action criterion](pilot-radial-action-slope-criterion.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-124 |
| Title | Physical radial tangent and signed observable derivatives at the pilot birth |
| Kind | Proof and exact numerical certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-120, N-123, Q-16 launch closeness, the pilot field and spatial-Jacobian certificates |
| Dependency requirement | Physical torus profiles within the proved Fourier errors, all endpoint traces from their section entries, and nine checked spatial field models on the pilot's first trial tube. |
| Produces | The initial value for the radial variational equation and both birth inequalities on the common eight-endpoint torus pair. |
| Difficulty | The radial parameter moves the initial point on two implicitly specified physical surfaces. The field evaluation must cover every true birth and tangent allowed by their KAM errors. |
| Status | Verified |
| Lean evidence | DommaschkBirthVariation.birth_derivative, geometry, pilot_numerators, observable_slopes, pilot_of_close, line_of_section and common_pilot. |
| Audit evidence | The instantiated eight-endpoint physical_birth theorem uses propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |

## The tangent belongs to the same birth as the field line

Write \(p_C(\phi)=(R_C(0,\phi),Z_C(0,\phi))\) and \(p_A(\phi)=(R_A(0,\phi),Z_A(0,\phi))\) for the two true torus profiles at poloidal phase zero. At fixed toroidal angle the birth is \(x(u,\phi)=(1-u)p_C(\phi)+u p_A(\phi)\). For every \(u,\phi\), its exact cylindrical tangent with respect to \(u\) is \(p_A(\phi)-p_C(\phi)\). At the pilot's section centre the approach to the section has duration zero. The physical line through this precise \(x(47/100,0)\) retains its original forward and backward tube lists and both terminal ellipsoids, through \(391/64\) radians in each direction. [Birth geometry](../../PlasmaLean/Design/DommaschkBirthVariation.lean) · [Physical line from the section](../../PlasmaLean/Design/DommaschkPilotBirthVariation.lean)

Each true profile coordinate carries its own certified \(10^{-12}\) KAM error at section zero. Evaluating the checked rational Fourier moments and enclosing both errors gives

| Quantity at birth | Proved enclosure in normalized candidate coordinates |
| --- | --- |
| \(R\) | \(0.99548672 \le R \le 0.99548675\) |
| \(Z\) | \(\lvert Z\rvert\le 10^{-12}\) |
| \(\partial_u R\) | \(0.01045982\le\partial_u R\le 0.01045983\) |
| \(\partial_u Z\) | \(\lvert\partial_u Z\rvert\le 2\cdot10^{-12}\) |

## Signed physical derivatives

Define \(f(u)=\lVert B(R(u),0,Z(u))\rVert\) and \(w(u)=R(u)f(u)/B_\phi(R(u),0,Z(u))\), the arclength per radian on the physical field line through the birth. The final theorem supplies two classical derivatives on the full label line at \(u=47/100\) with

\[
  f'(47/100)\le -1/144,\qquad
  0<w'(47/100),\qquad
  -w(47/100)/32\le w'(47/100).
\]

The proof specializes the three physical field models and their six spatial partial derivatives to the initial normalized time \(-1\) of the pilot's first slab. The spatial coordinate model admits the entire KAM birth enclosure. With \(D=R^7B_\phi\), the derivative of \(f^2\) has denominator \(R^{17}\) and numerator at most \(-100701606257525/2^{52}\). The derivative of \(w^2\) has denominator \(D^3\) and numerator at least \(98070345339236/2^{52}\). The same interval calculation gives \(D>0\) and \(f<3/2\). Positivity and the square-root chain rule give the signed inequalities for \(f\) and \(w\). Python emits integer endpoints for the interval products. Lean checks each enclosure and the identities with both physical observables. [Exact arithmetic](../../PlasmaLean/Design/DommaschkBirthVariationBounds.lean) · [Analytic transfer](../../PlasmaLean/Design/DommaschkBirthVariation.lean)

## Remaining first-well variation

N-123 needs the same inequalities throughout the accessible first well at fixed geometric angle. On each signed branch the next input is an enclosure of the solution \(Y\) of \(Y'=D_xF_{\rm flow}(t,x(t))Y\), initialized with the certified \(p_A(0)-p_C(0)\). The field-jet test in N-124 applies to any fixed-angle differentiable variation once its true trajectory and tangent are enclosed. A radial action derivative bound for the whole well still depends on this propagation and the differentiated-family hypotheses in N-118. [First-well criterion](pilot-radial-action-slope-criterion.md)

## Replay

The first two commands check the input model arithmetic and all static Lean declarations. The final command binds the birth to a concrete authenticated eight-endpoint checkpoint family. The N-120 receipt used here has 391, 48, 16, 5, 12, 5, 5 and 5 slabs in each direction, in endpoint order. Its reproduction commands are in N-120. [Common eight-endpoint family](eight-signed-traces-on-common-tori.md)

~~~bash
python3 scripts/dommaschk_kam/emit_birth_variation.py
LEAN_NUM_THREADS=1 lake build PlasmaLean.Design.DommaschkPilotBirthVariation
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/verify_birth_variation.py \
  --family /tmp/plasma-common-endpoint-traces-extended.json \
  --output /tmp/plasma-radial-birth.json
~~~

The accepted declaration is `DommaschkPilotBirth391_48_16_5_12_5_5_5.physical_birth`. Its receipt key is `c7c7ba3ab60389167296f235d1e6aefdf468dd8460dfffffc241f8d96067f38c`.
