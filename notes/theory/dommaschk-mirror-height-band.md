# First mirror times and physical action throughout the pilot height band

For each admitted phase-zero QA2R birth at radial interpolation parameter $u=47/100$, one physical trajectory has two transverse first mirrors for **every** height $h$ in the closed band $[h_L,h_U]$. Each mirror moves continuously outward as height increases. The one-way physical action between them is continuous and strictly increasing in $h$. Every height gives a regular arclength mirror birth and a finite, strictly positive one-way flight time on that same trajectory. [Signed branches](../../PlasmaLean/Design/DommaschkSignedMirrorBand.lean) · [Physical action](../../PlasmaLean/Design/DommaschkMirrorBandAction.lean) · [Physical passage](../../PlasmaLean/Design/DommaschkMirrorBandPassage.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-99 |
| Title | Transverse first mirrors and physical action across a closed band of heights |
| Kind | Proof and certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-81, N-95, N-96, N-97, N-98 |
| Dependency requirement | Both endpoint first contacts on the same 325-row signed Q-16 path, its certified physical field, radius and arclength, the original position and harmonic certificates, and the endpoint regular-well and finite-time implications. |
| Produces | Two ordered Lipschitz first-mirror functions, a continuous strictly increasing true action, and regular births with finite positive one-way flight times over the continuum of heights. |
| Difficulty | A level can occur at any of the eight internal numerical slab boundaries. A true two-sided derivative and a validated closed enclosure must hold together at such a point. |
| Status | Verified |
| Lean evidence | On demand. `DommaschkMirrorHeightBand325.from_birth` and `DommaschkRegularMirrorHeightBand325.from_birth`. The reusable declarations are listed below. |
| Audit evidence | The local analytic declarations and the generated kernels report only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The two application keys appear below. |
| Last updated | 25 November 2026 |

## One path for all heights

The launch phase satisfies $|\phi|\le 2^{-19}$. With the pair of nested Q-16 tori fixed, the theorem chooses a signed physical field line through the prescribed interpolated birth. The choice precedes the quantifier over $h$. Write $f(t)=\lVert B(R(t),t,z(t))\rVert$ on the signed geometric-angle clock and use the exact levels

$$
h_L=\frac{5297961656084411}{5000000000000000},\qquad
h_U=\frac{5300546391395933}{5000000000000000}.
$$

For each outward branch, let $s$ denote positive elapsed angle and let $f_\pm(s)=f(\pm s)$. There is a strictly increasing map $\tau_\pm:[h_L,h_U]\to(316/64,325/64)$ satisfying $f_\pm(\tau_\pm(h))=h$. Each is the first occurrence of its level starting at zero and the unique occurrence on the entire closed search interval. The continuation of the same outward branch past its mirror has strength strictly greater than $h$ up to $325/64$. The endpoints $h_L,h_U$ inherit their narrower brackets from N-95. [Candidate-independent inverse theorem](../../PlasmaLean/Theory/Kinetic/MirrorHeightBand.lean) · [Earlier endpoint brackets](dommaschk-first-mirrors-from-birth.md)

The lower bound for the outward derivative of squared strength is $k=1/400$ on the open interval $(316/64,325/64)$, including its internal seams. Consequently $f_\pm'(\tau_\pm(h))>1/(800h)$ and

$$
 k\,|\tau_\pm(h)-\tau_\pm(j)|\ \le\ |h^2-j^2|,
 \qquad
 |\tau_\pm(h)-\tau_\pm(j)|\ \le\ 800h_U |h-j|.
$$

The second inequality gives continuity through both boundary heights. The parameter in those derivatives and displacement bounds is outward *angle*. The estimate remains valid at heights attained exactly at a slab boundary. [Inverse displacement](../../PlasmaLean/Theory/Kinetic/MirrorHeightBand.lean)

## Nine closed-slab certificates

Rows 316 through 324 have width $1/64$ each. On each row the calculation reuses the authenticated positive-branch sparse field and spatial derivatives and certifies the remaining six derivatives with respect to the harmonic input variables. Its rational Taylor models bound the numerator of the outward derivative of $f^2$ after subtracting $kR^{17}D$, where $D=R^7B_\phi>0$. Row 316 admits the stronger bound $1/128$. The other eight rows certify $1/400$. The full Taylor enclosure is used at each input. Reflection of the negative branch is checked against its actual center polynomial and its own output radius. [Slope proof generator](../../scripts/dommaschk_kam/verify_mirror_slopes.py)

At an internal boundary, the solution of the signed ODE on the full path has an ordinary derivative. Either adjacent closed-slab certificate can then supply the slope inequality there. Bounds proved only on the two open halves would leave an intermediate height uncovered. For example $g(t)=2t+|t|$ has positive slopes on both sides and has no derivative at zero. [Joining closed-slab rates](../../PlasmaLean/Design/DommaschkSignedMirrorBand.lean)

## Complete-well consequences

The two physical mirror coordinates are $-\tau_-(h)$ and $\tau_+(h)$. The strict and closed accessible components containing the section are the open and closed intervals with these endpoints. At the original interpolated birth the physical arclength curve satisfies the contract's regular-mirror condition for that $h$. The one-way integral of physical arclength density divided by $\sqrt{2(h-f(t))}$ is finite and positive. This assertion applies to every height in the band; a numerical upper bound on flight time has yet to be established. [Physical components and arclength](../../PlasmaLean/Design/DommaschkFirstMirrorWell.lean) · [Flight-time theorem](../../PlasmaLean/Design/DommaschkFirstMirrorBounceTime.lean)

Let $X(t)=(R(t)\cos t,R(t)\sin t,z(t))$ and $W(t)=R(t)f(t)/B_\phi(t)$. The true one-pass action satisfies

$$
 \int_{-\tau_-(h)}^{\tau_+(h)}
  \lVert X'(t)\rVert\sqrt{2(h-f(t))}\,dt
 =
 \int_{-325/64}^{325/64}
  W(t)\sqrt{\max\{2(h-f(t)),0\}}\,dt .
$$

The closed ends of the larger angular window may only supply a one-sided path derivative. The proof uses the continuous physical density $W$ on that window and the ordinary Cartesian derivative throughout the interior of the moving-root well. Both outer caps have zero clipped integrand. The birth sector is already accessible at $h_L$, and its arclength density is positive. These facts give strict increase of the physical action as a function of height. The result concerns one fixed radial launch parameter in the dimensionless model. Comparing the action across launch parameters, extracting a numerical universal time bound and choosing SI operating conditions are separate questions. [Fixed-window equality](../../PlasmaLean/Design/DommaschkMirrorBandAction.lean)

## Reproduce

The analytic theorems are `MirrorHeightBand.exists_branch`, `DommaschkSignedMirrorBand.branches`, `DommaschkMirrorBandAction.family` and `DommaschkMirrorBandPassage.on_path`. For the nine numerical witnesses prepare the existing shared-power forward Jacobians for rows 316–324 from the N-95 replay, using the tracked pilot archive with SHA-256 `203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d`. The only final imported trajectory receipt is N-95's 325-row proof of first contacts at both levels. The two verifiers check upstream artifact hashes and compiler-produced certificates. A missing closed row fails the complete-height request before Lean starts. [Assembly and actual-birth producer](../../scripts/dommaschk_kam/verify_mirror_height_band.py)

```bash
LEAN_NUM_THREADS=1 lake build PlasmaLean.Design.DommaschkMirrorBandPassage
for i in {316..324}; do
  OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_slopes.py \
    --index "$i" --part closed-tube --output "/tmp/plasma-band-mirror-slope$i.json" || exit 1
done
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_height_band.py \
  --slopes /tmp/plasma-band-mirror-slope{316..324}.json \
  --first-contacts /tmp/plasma-first-contacts-325.json \
  --output /tmp/plasma-mirror-height-band-325.json \
  --passage-output /tmp/plasma-mirror-height-passage-325.json
```

The raw signed branches have content key `cbc98f80c06f8025f89fed9551428c2fe7bb4d1f194bcd9f48a9aea4fdc81c09`. The through-birth theorem with regular wells, finite flights and the action family has content key `9c00a57de9e2b1b2cc49b184ca9862539bc1c68c69f74d7c45fefcf531bb9809`.
