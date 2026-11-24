# A toroidal field floor over the full pilot envelope sharpens first-mirror flight times

The QA2R candidate satisfies $B_\phi(R,\phi,z)>7/8$ throughout $7/8\le R\le1$, $|z|\le5/64$, for **every real geometric angle** $\phi$. For each N-99 birth at the phase-zero pilot with radial interpolation parameter $47/100$, the resulting normalized one-way flight time exceeds **14** throughout the closed mirror-height band and is below **592** on its closed upper half. The bounds concern the physical flight between the two first mirrors on the same signed trajectory. [Global field theorem](../../PlasmaLean/Design/DommaschkToroidalEnvelope.lean) · [Physical time statements](../../PlasmaLean/Design/DommaschkSharpFlightBounds.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-106 |
| Title | An all-angle toroidal field floor and sharper physical flight-time bounds |
| Kind | Analytic proof and exact spatial certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-96, N-98, N-99, N-103 |
| Dependency requirement | Exact QA2R sparse polynomials and harmonic identities, the signed envelope, the N-99 physical first-well branches and N-103 core/collar integral estimates. |
| Produces | A field and arclength bound uniform in angle and space, a candidate-independent weighted branch-time bound, and a checked all-birth one-way flight inequality. |
| Difficulty | The full angular variation needs a positive residual after subtraction of the desired floor. The reciprocal speed has integrable singularities at both mirrors. |
| Status | Verified |
| Lean evidence | DommaschkToroidalEnvelope.cylBphi_lower, DommaschkToroidalFieldBounds.density_upper, MirrorActionEnvelope.branch_time_upper, DommaschkSharpFlightBounds.of_passage and the ground DommaschkSharpFlightBounds325.from_birth. |
| Audit evidence | The 13 local declarations and ground certificate use only propext, Classical.choice and Quot.sound. The generated all-angle checker reproduces byte-for-byte. |
| Last updated | 25 November 2026 |

## Uniform toroidal field

Put $u=R-29/32$. The physical identity $D(u,z,\cos 2\phi,\sin 2\phi)=R^7 B_\phi(R,\phi,z)$ turns the desired floor into positivity of $D-(7/8)(29/32+u)^7$. Subtracting the radial polynomial in the constant angular harmonic preserves the cancellation before enclosing the values. The checker proves that the seven channel polynomials, expanded at their common angle, give exactly this shifted sparse polynomial. For each spatial rectangle it evaluates their nested Horner forms by outward-rounded integer interval operations with scale $2^{52}$. It uses $1$ for the constant harmonic and $[-1,1]$ for each genuine trigonometric factor. [Harmonic interval soundness](../../PlasmaLean/Design/DommaschkHarmonicBoxes.lean) · [Exact spatial proof generator](../../scripts/dommaschk_kam/emit_toroidal_envelope.py)

Ten closed rectangles cover $[-1/32,3/32]\times[-5/64,5/64]$. The smallest certified lower endpoint of the shifted polynomial is exactly $23135832346878/2^{52}$, about $0.00513719$. As an independent upper obstruction, direct evaluation of the unshifted sparse field at a point of this envelope gives $B_\phi(1,\pi/2,0)=2387710247/2500000000=0.9550840988$. A uniform lower bound of one would therefore be false. [Ten-cell kernel witness](../../PlasmaLean/Design/DommaschkToroidalEnvelope.lean) · [Exact boundary point](../../PlasmaLean/Design/DommaschkToroidalEnvelopeTest.lean)

## From field strength to flight time

Write $f=\lVert B\rVert$ and $w=R f/B_\phi$. The orthonormal cylindrical component identity implies $f\ge B_\phi>7/8$. On the part accessible at height $h$, $w\le 8h/7$. For any $h\le h_U$, the clipped parallel speed satisfies $\sqrt{2(h-f)_+}<61/100$. The first mirrors lie on opposite sides of the section, each past outward angle $316/64$, and the physical density is at least $7/8$. Consequently

$$
 T>\frac{2(316/64)(7/8)}{61/100}>14 .
$$

This holds also at the lower endpoint $h_L$. [Field strength, speed and density bounds](../../PlasmaLean/Design/DommaschkToroidalFieldBounds.lean) · [Certified mirror branches](dommaschk-mirror-height-band.md)

For an outward branch, let $s$ be its mirror angle at $h_L$ and $r$ its mirror angle at $h$. The general upper estimate uses a density ceiling $W$, reciprocal-speed ceiling $A$ on the core $[0,s]$, and collar majorant $D/\sqrt{r-t}$ for reciprocal speed on $(s,r)$. It gives

$$
 T_{\rm half}\le sWA+2WD\sqrt{r-s}.
$$

On the upper half of the height band, N-99 supplies $f<h_L$ before $s$ and the squared-strength slope bound $1/400$ on the outer branch. These imply $A=45$ and $D=21$. Setting $W=8h_U/7$ and using $s<325/64$, $\sqrt{r-s}\le3/8$, gives $T_{\rm half}<296$ on each signed half. Both halves belong to the same field line through the actual interpolated birth. The resulting mirror-to-mirror upper bound is $592$. The height endpoints are the archive rationals $h_L=5297961656084411/5000000000000000$ and $h_U=5300546391395933/5000000000000000$. The time units are those of the dimensionless archive. [Reusable weighted bound](../../PlasmaLean/Theory/Kinetic/MirrorBranchTimeUpper.lean) · [Earlier N-103 bounds](quantitative-first-mirror-flight-times.md)

## Replay

The global field and analytic bounds build from tracked sources. The application additionally takes the N-99 through-birth receipt and its cached proof imports.

~~~bash
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/emit_toroidal_envelope.py \
  --output /tmp/replayed-toroidal-envelope.lean
cmp /tmp/replayed-toroidal-envelope.lean PlasmaLean/Design/DommaschkToroidalEnvelope.lean
lake build PlasmaLean.Design.DommaschkSharpFlightBounds PlasmaLean.Design.DommaschkToroidalEnvelopeTest
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_sharp_flight_bounds.py \
  --passage /tmp/plasma-mirror-height-passage-325.json --output /tmp/plasma-sharp-flight-325.json
~~~

The signed N-99 passage key is 9c00a57de9e2b1b2cc49b184ca9862539bc1c68c69f74d7c45fefcf531bb9809. The ground N-106 certificate key is b893c20ec558501b82892a6f3cfe05cdb38e7d7385df583a6e95ddcc3927995a for archive SHA-256 203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d. [Ground replay driver](../../scripts/dommaschk_kam/verify_sharp_flight_bounds.py)
