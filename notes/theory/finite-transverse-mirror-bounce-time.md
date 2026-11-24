# Finite one-way time between the first physical mirrors

At the phase-zero QA2R launch $u=47/100$, **both first mirror wells have a finite, strictly positive one-way flight time** for every admitted birth angle $|\phi|\le 2^{-19}$. The same signed field line passes through the actual interpolated birth and supplies the arclength density for both integrals. This result uses the dimensionless field and the normalized parallel speed of the action archive. [Physical proof producer](../../scripts/dommaschk_kam/verify_first_mirror_bounce_times.py)

## The general theorem

**Compiled Lean theorem.** Let $l<c<r$. A continuous field-strength profile $f$ on $[l,r]$ satisfies $f(l)=f(r)=h$ and $f(t)<h$ for $l<t<r$. Assume the endpoint derivatives exist with $f'(l)<0<f'(r)$. Let $w$ be a continuous arclength density on $[l,r]$ with $w(t)>0$ for $l<t<r$. Then the following integrand is interval-integrable and its integral is strictly positive.

$$
T=\int_l^r \frac{w(t)}{\sqrt{2(h-f(t))}}\,dt .
$$

The explicit integrability conclusion matters because Lean assigns a value to the integral of a nonintegrable function. The theorem applies to any such profile and density. [General theorem and definition](../../PlasmaLean/Theory/Kinetic/MirrorBounceTime.lean)

Put $g=2(h-f)$. On $[l,c]$, the quotient $g(t)/(t-l)$ extends continuously to $t=l$ with value $g'(l)>0$. It is positive everywhere on this compact half-interval. Thus the integrand is the product of a bounded continuous function and $(t-l)^{-1/2}$ on its interior. Reflection about the right endpoint gives the analogous factor $(r-t)^{-1/2}$ on $[c,r]$. Both are integrable, and positivity on the interior gives $T>0$. The existing tangential example has a quadratic gap at the left root. Its reciprocal speed agrees with $1/t$ near that root and fails to be interval-integrable. [Formal positive result](../../PlasmaLean/Theory/Kinetic/MirrorBounceTime.lean) · [Tangential counterexample](../../PlasmaLean/Theory/Kinetic/MirrorActionEnvelope.lean)

## QA2R application

**Compiled Lean theorem.** There is one shared pair of nested Q-16 tori such that each admitted interpolated birth lies on a signed trajectory $y$ satisfying the time theorem for both heights. For each height the two first hits $l,r$ obey $l<\phi<r$. Along the same trajectory the profile is $f(t)=\lVert B(R(t),t,z(t))\rVert$ and the weight is the physical arclength per radian, $w(t)=R(t)\lVert B\rVert/B_\phi$. The positive spatial radius and toroidal field on the archived region make this density continuous and strictly positive. The signed transversality proof supplies the endpoint slopes in the increasing geometric angle. [Physical specialization](../../PlasmaLean/Design/DommaschkFirstMirrorBounceTime.lean) · [Arclength on the checked region](../../PlasmaLean/Design/DommaschkSignedTraceDensity.lean) · [Birth point and signed path](../../PlasmaLean/Design/DommaschkSignedBirthApproach.lean)

| Mirror height $h$ | Left first hit | Right first hit |
| --- | --- | --- |
| $5297961656084411/5000000000000000$ | $(-317/64,-316/64)$ | $(316/64,317/64)$ |
| $5300546391395933/5000000000000000$ | $(-325/64,-324/64)$ | $(324/64,325/64)$ |

Quantitative flight times remain open. A numerical upper bound requires control of the inverse speed through both endpoint neighborhoods and the interior. Conversion to seconds also requires physical length, field and particle scales. [First physical mirror contacts](dommaschk-first-mirrors-from-birth.md) · [Regular births on the physical field line](regular-mirror-births-and-components.md)

## Reproduce

Use the paired 325-slab trajectory and first-transverse-contact manifests produced by N-95. The checker validates the archived trajectory digest, expected module names, content keys and imported artifacts before replaying the proof.

```sh
lake build PlasmaLean.Design.DommaschkFirstMirrorBounceTime
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_first_mirror_bounce_times.py --paired /tmp/plasma-signed-checkpoint-325.json --contacts /tmp/plasma-transverse-first-birth-325.json --output /tmp/qa2r-first-bounce-times325.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-98 |
| Title | Finite one-way time between the first physical mirrors |
| Kind | Theorem and physical certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-95, N-97 |
| Dependency requirement | The normalized mirror speed, actual first-transverse signed contacts, genuine arclength density and identification of the interpolated birth on the same signed trajectory. |
| Produces | Interval integrability and positivity of the one-way mirror-to-mirror time, with both physical wells realized on every admitted Q0R470 birth trajectory. |
| Difficulty | The speed vanishes at both moving endpoints. Its reciprocal has integrable inverse-square-root singularities under the two strict slope conditions. |
| Status | Verified at both pilot heights. Quantitative time enclosures remain open. |
| Lean evidence | On demand. `LaunchWell.finite_bounce_time`, `DommaschkFirstMirrorBounceTime.of_contacts`, `DommaschkFirstBounceTimes325.from_birth`. |
| Audit evidence | Kernel content key `bfe2ec82d419c5c038a05ddf9198bc55882b94b93e38e2d3b0550a92a41d9bdc`. The concrete theorem uses only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |
