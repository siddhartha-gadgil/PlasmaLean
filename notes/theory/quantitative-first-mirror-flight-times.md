# Numerical bounds on one-way flight time between the physical mirrors

At the QA2R pilot launch $u=47/100$, every admitted toroidal angle and every height in the closed archive band satisfy **$T>237/40=5.925$** in dimensionless one-way flight time. Throughout the upper half of the band, **$T<34000$** as well. Both inequalities concern the integral between the actual first mirrors on the trajectory through the original birth. The estimate at the lower end of the band remains one-sided. Dimensional time requires the physical length, field and particle scales. [Physical theorem](../../PlasmaLean/Design/DommaschkMirrorFlightBounds.lean)

## Where the bounds come from

In the angular coordinate let $w(t)$ be the Cartesian arclength density, $f(t)=\lVert B\rVert$, and $v(t)=\sqrt{2(h-f(t))}$. Then $T=\int_l^r w/v$. The certified bracket gives $r-l>632/64$, the cylindrical envelope gives $w\ge 7/8$, and the largest archive height gives $v\le 35/24$. Integrating the resulting lower bound $w/v\ge 3/5$ gives $T>237/40$. The two endpoints have zero measure and N-98 supplies integrability there. [First-turning-point geometry](dommaschk-first-mirrors-from-birth.md) · [Finite time at a transverse mirror](finite-transverse-mirror-bounce-time.md)

For the upper bound, write $s$ for the first mirror time at the lowest height $h_L$ and $r_h$ for the first mirror time at the chosen height on the same outward branch. Between $0$ and $s$, the field is below $h_L$. For $h\ge(h_L+h_U)/2$ this gives $v\ge 1/45$. Between $s$ and $r_h$, invert the certified displacement estimate for first mirrors. It gives
$$
\frac{1}{v(t)}\ \le\ \frac{21}{\sqrt{r_h-t}} .
$$
The second interval has length at most $9/64$. The arclength density obeys $w\le68$ inside the well, using $R^7 B_\phi>1/64$, $R\le1$ and $f\le h_U$. The two elementary integrals on each side give less than 17000 per half-passage. The inverse-square-root bound accounts for the endpoint singularity explicitly. [Height-band displacement](dommaschk-mirror-height-band.md) · [Quantitative time comparisons](../../PlasmaLean/Theory/Kinetic/MirrorTimeActionBounds.lean)

A second reusable inequality gives $L^2\le JT$ for $L=\int w$ and $J=\int wv$ on the same passage. It assumes nonnegative density, positive interior speed, integrability of the three quantities, and $J>0$. An upper bound on whole-well action can therefore improve the lower flight-time estimate. [Length, action and time theorem](../../PlasmaLean/Theory/Kinetic/MirrorTimeActionBounds.lean)

## Reproduce

Use the nine closed-slab signed slope certificates and the first-contact report from N-99.

~~~bash
lake build PlasmaLean.Design.DommaschkMirrorFlightBounds
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_height_band.py \
  --slopes /tmp/plasma-band-mirror-slope{316..324}.json \
  --first-contacts /tmp/plasma-first-contacts-325.json \
  --output /tmp/plasma-mirror-height-band-325.json \
  --passage-output /tmp/plasma-mirror-height-passage-325.json \
  --time-output /tmp/plasma-mirror-flight-bounds-325.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-103 |
| Title | Numerical bounds on one-way flight time between the physical mirrors |
| Kind | Theorem and physical certificate |
| Addresses | G-6, G-10, Q-1, Q-16, Q-35 |
| Depends on | N-95, N-97, N-98, N-99 |
| Dependency requirement | Actual first-mirror paths, a positive arclength density, finite flight integrals and the outward displacement bound over the certified height band. |
| Produces | A lower bound for all pilot heights, a two-sided dimensionless time interval in the upper half of the band, and a reusable length–action–time inequality. |
| Difficulty | Inverse speed diverges at each turning point. The numerical collar estimate must hold up to those singular endpoints on the original field line. |
| Status | Verified on the admitted pilot launch family. |
| Lean evidence | MirrorActionEnvelope.half_time_upper, branch_collar_time_bound, length_sq_le_action_mul_time, DommaschkMirrorFlightBounds.of_passage, DommaschkMirrorFlightBounds325.from_birth. |
| Audit evidence | Ground kernel key d8516f5104fcaeee31f998f104202718a0faf76d28451ab6a57b37552f156b59. Axioms are propext, Classical.choice and Quot.sound. |
| Next action | Tighten the toroidal field and core-speed bounds, extend numerical upper times to the lowest heights, and combine a whole-well action upper bound with the length inequality. |
| Last updated | 25 November 2026 |
