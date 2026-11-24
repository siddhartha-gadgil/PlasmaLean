# The accessible component and the actual regular mirror birth

At $u=0.470$, for every admitted initial angle $|\phi|\le 2^{-19}$, the actual interpolated physical birth point satisfies the contract predicate `RegularMirrorBirth` at both archived mirror heights. The same physical field line and the same nested Q-16 tori serve both heights. The predicates use arclength along the candidate field and simple turning points, with field strength strictly below the height between them. All lengths and field values here use the normalization of the QA2R model. [Ground proof producer](../../scripts/dommaschk_kam/verify_first_mirror_wells.py) · [Contract definition](../../PlasmaLean/Theory/Contract/TrappedBirthBand.lean)

**A general statement about wells.** Let $f$ be a real-valued function of one real parameter. Suppose $l<c<r$, both endpoints have value $h$, and $f<h$ throughout $(l,r)$. The connected component of $\{f<h\}$ containing $c$ is exactly $(l,r)$. If both outward derivatives at the endpoints are positive, the component of $\{f\le h\}$ containing $c$ is $[l,r]$. The proof uses order-connectedness on the real line. Positive outward secants give forbidden points arbitrarily near each boundary. Behavior farther down the field line is unrestricted. The example $f(t)=-(t^2-1)^2$, $c=h=0$, has strict component $(-1,1)$ and closed component $\mathbb R$, showing the role of boundary isolation. [Component theorems and counterexample](../../PlasmaLean/Theory/Kinetic/MirrorWellComponent.lean)

**From angle to arclength.** On the physical tube $R\ge7/8$ and the polynomial denominator exceeds $1/64$. The angular velocity is a positive continuous multiple of the unit magnetic field. The increasing arclength clock transfers the two opposite derivative signs and allows every point in the closed well to serve as the time origin. Thus the geometric component certifies the physical mirror predicate at every point between its endpoints. [Candidate specialization](../../PlasmaLean/Design/DommaschkFirstMirrorWell.lean) · [Arclength change of parameter](../../PlasmaLean/Theory/Kinetic/MirrorArclength.lean)

**From the section to the birth.** The construction first solves an approach from $\phi$ to section zero. The longer signed field line and that approach have a common terminal state. Local uniqueness along the signed trajectory and a reversal of the angular clock identify them at every approach time. In particular the signed line at angle $\phi$ passes through the original interpolated birth position. [Physical position identity](../../PlasmaLean/Design/DommaschkSignedBirthApproach.lean) · [Terminal-value uniqueness](../../PlasmaLean/Theory/Fields/ClosedIntervalODEUniqueness.lean)

The theorem supplies regular mirror births at **two heights** over a one-parameter set of positions. A trapping fraction requires a birth measure and a set of positive mass in the intended phase space. A C2 conclusion also requires quantitative control of radial drift or an equivalent transport bound.

## Reproduce

Using the paired trajectory and transverse first contacts from N-95, run

```sh
lake build PlasmaLean.Design.DommaschkFirstMirrorWell PlasmaLean.Design.DommaschkSignedBirthApproach
.venv-ws/bin/python scripts/dommaschk_kam/verify_first_mirror_wells.py --paired /tmp/qa2r-p325.json --contacts /tmp/qa2r-contacts325.json --output /tmp/qa2r-regular-births325.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-97 |
| Kind | Geometric characterization and physical contract specialization |
| Addresses | G-6, G-10, Q-1, Q-16, Q-35 |
| Depends on | N-60, N-91, N-95, N-96 |
| Dependency requirement | Signed first contacts and their slopes, positive oriented arclength, a regular physical domain and uniqueness of the approach. |
| Produces | Exact open and closed components and regular arclength mirror births at the original launch points for both heights. |
| Difficulty | Extend to a band of heights and spatial labels with controlled action and bounce dynamics. |
| Status | General theorems in the default library and concrete birth theorem compiled on demand. |
| Lean evidence | `DommaschkFirstWells325.regular_births`, `DommaschkFirstMirrorWell.identify`, `LaunchWell.transverse_component`, `LaunchWell.regular_at`, `DommaschkSignedBirthApproach.birth_position`. |
| Audit evidence | Concrete proof key `bb4c0ddd903e4f22734954bcae2125800717af1d37f32f4a5cdc7b3af1c08004`. Only the standard three axioms. |
| Last updated | 25 November 2026 |
