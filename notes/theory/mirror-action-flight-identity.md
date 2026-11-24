# The height derivative of first-well action is one-way flight time

Every admitted birth angle at the phase-zero QA2R pilot with radial interpolation parameter $u=47/100$ has one signed field line for which the derivative of the first-well action equals the physical one-way flight time at **every height** in the N-99 band. Between any two band heights the integral of that flight time is the exact action increment. The quantities use the normalized candidate field and the actual Cartesian arclength density. [Verified physical statement](../../PlasmaLean/Design/DommaschkMirrorBandFlightIdentity.lean) · [N-99 birth and first-mirror branches](dommaschk-mirror-height-band.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-104 |
| Title | The height derivative of first-well action is one-way flight time |
| Kind | Proof and certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-96, N-98, N-99 |
| Dependency requirement | Continuous signed field strength and Cartesian arclength density on the 325-row window, with the two transverse first mirrors and forbidden outer caps at each band height. |
| Produces | Absolute continuity and exact action increments on compact windows, differentiation at two simple mirrors, and an every-birth physical realization throughout the pilot height band. |
| Difficulty | The reciprocal parallel speed becomes unbounded at a regular turning point and the endpoints of the integration window move with height. |
| Status | Verified |
| Lean evidence | `MirrorActionFlight.compact_window`, `absolutelyContinuous_action`, `hasDerivAt_two_mirrors`, `DommaschkMirrorBandFlightIdentity.on_path`, and the on-demand `DommaschkMirrorActionFlight325.from_birth`. |
| Audit evidence | The local and ground certificates use only `propext`, `Classical.choice`, and `Quot.sound`. The ground key and reproduction commands appear below. |
| Last updated | 25 November 2026 |

## Any continuous trace on a compact interval

Let $f$ be field strength and $w$ the arclength density on $[a,b]$. Define the clipped action and reciprocal-speed integral by

$$
J(h)=\int_a^b w(t)\sqrt{2(h-f(t))_+}\,dt,
\qquad
T(h)=\int_{\{a\le t\le b:\ f(t)<h\}}
\frac{w(t)}{\sqrt{2(h-f(t))}}\,dt .
$$

For continuous $f,w$, $J$ is absolutely continuous on each finite height interval and $T$ is locally integrable in height. For all oriented endpoints $i,j$,

$$
J(j)-J(i)=\int_i^j T(v)\,dv .
$$

In particular $J'(h)=T(h)$ for almost every height. These statements allow arclength atoms and flat bottoms. For a fixed field value $x$, the height integral of the clipped reciprocal speed from $i$ to $j$ equals $\sqrt{2(j-x)_+}-\sqrt{2(i-x)_+}$. Integrating the absolute value in height first proves product integrability on the rectangle, including its diagonal singularities. At an exceptional height the spatial integral can fail to exist as a finite physical flight time. Lean's total integral convention assigns a value there and the almost-everywhere assertion is insensitive to that assignment. [Compact-window proof and exact scalar primitive](../../PlasmaLean/Theory/Kinetic/MirrorActionFlight.lean)

## A derivative at a specified height

For a single simple level crossing $f(r)=h$ on a compact interval, the divided difference $(f(t)-f(r))/(t-r)$ extends continuously at $r$ with nonzero value $f'(r)$. Its absolute value stays away from zero on that interval when $r$ is the only crossing. Consequently $1/\sqrt{|h-f(t)|}$ has an integrable inverse-square-root singularity on **both sides** of the crossing. The clipped scalar estimate

$$
\left|\sqrt{p_+}-\sqrt{q_+}\right|\sqrt{|q|}\le |p-q|
$$

then dominates the action difference quotients by $2|w(t)|/\sqrt{|2(h-f(t))|}$. Dominated convergence proves $J'(h)=T(h)$. At two transverse first mirrors, split the positional window at the birth and apply this argument on each half. The outer caps are forbidden, so $T(h)$ equals the genuine integral between the mirrors. Only the two individual spatial derivatives at the crossings enter the argument. [Two-mirror derivative and forbidden-cap theorem](../../PlasmaLean/Theory/Kinetic/MirrorActionTransverse.lean)

The unit-length trace $f=0,w=1$ gives $J(h)=\sqrt{2h_+}$. The derivative equals reciprocal speed at each $h\ne0$. At $h=0$ no finite derivative exists, although the integral identity still holds across zero. This verifies the need for a stronger hypothesis to claim pointwise differentiability. [Positive, forbidden and flat-critical tests](../../PlasmaLean/Theory/Kinetic/MirrorActionFlightExamples.lean)

## Physical pilot

The N-99 inputs fix $|\varphi|\le 2^{-19}$, $u=47/100$, the signed angular window $[-325/64,325/64]$, and

$$
h_L=\frac{5297961656084411}{5000000000000000},
\qquad h_U=\frac{5300546391395933}{5000000000000000}.
$$

The physical field line is selected once for each admitted birth angle. At every real $h\in[h_L,h_U]$, the two first mirrors on that line bound a finite, strictly positive one-way flight time. The clipped action on the full angular window equals the physical action between those moving mirrors. Its ordinary derivative is their one-way flight time. At $h_L,h_U$ this derivative is taken on the ambient clipped action, which supplies the corresponding one-sided derivative of the restricted physical family. The same-window reciprocal-speed integral equals that first-mirror flight integral at each intermediate height. This identifies the integrand in the exact action increment above and requires no new numerical table. [Physical composition](../../PlasmaLean/Design/DommaschkMirrorBandFlightIdentity.lean) · [Original trajectory and units](dommaschk-mirror-height-band.md)

## Replay

With the N-99 passage receipt and its content-addressed imports present, run

```bash
lake build PlasmaLean.Theory.Kinetic.MirrorActionFlightExamples \
  PlasmaLean.Design.DommaschkMirrorBandFlightIdentity
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_action_flight.py \
  --passage /tmp/plasma-mirror-height-passage-325.json \
  --output /tmp/plasma-mirror-action-flight-325.json
```

The N-99 passage key is `9c00a57de9e2b1b2cc49b184ca9862539bc1c68c69f74d7c45fefcf531bb9809`. The ground action/flight theorem has key `de7a8d692d16af989d6f6b085d52661a9cdea05cae84a06b8b45397880b30726` for archive SHA-256 `203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d`. [Replay driver](../../scripts/dommaschk_kam/verify_mirror_action_flight.py)
