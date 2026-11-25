# Positive radial measure for approximate first-well actions

Let $P$ be a compact metric parameter space, let $a<b$, and let $F:P\times[a,b]\to\mathbb R$ be continuous. For every $\varepsilon>0$ there is a single $\ell>0$ with the following property. For every $p\in P$ and **every** value $j$ attained by $F(p,\cdot)$, the set

\[
 W(p,j,\varepsilon)=\{r\in[a,b]:|F(p,r)-j|<\varepsilon\}
\]

contains a closed interval of length $\ell$. Its one-dimensional Lebesgue measure is therefore at least $\ell$. The same $\ell$ works for targets chosen independently in different fibers, including discontinuous choices and fibers with many exact roots. [General theorem](../../PlasmaLean/Theory/Geometry/UniformRadialWindow.lean)

## Why the interval survives at an endpoint

Compactness gives a uniform continuity radius $d>0$ for the tolerance $\varepsilon$ over the entire product. Take $\ell=\min(b-a,d/2)$. If $x$ is any radius at which $F(p,x)=j$, put $c=\min(x,b-\ell)$. The closed interval $[c,c+\ell]$ lies inside $[a,b]$, contains $x$, and each of its radii is at distance at most $\ell<d$ from $x$. The construction also applies when $x=a$ or $x=b$. Taking Lebesgue measure of this interval proves the bound. [Interval construction and measure inequality](../../PlasmaLean/Theory/Geometry/UniformRadialWindow.lean)

If a radial Lipschitz constant $L>0$ is known on the fiber, the proof gives the explicit length

\[
 \ell=\min\left(b-a,\frac{\varepsilon}{2L}\right).
\]

For $L=0$ it gives the entire interval of length $b-a$. A common $L$ gives these lengths uniformly over parameters. The general theorem uses uniform continuity whenever a radial derivative bound is unavailable.

## Physical specialization

Use the N-192 compact phase–height space as $P$, and the original birth parameter $u\in[47/100,239/500]$ as the radial interval. The observable is the integral of the physical action **between the two first mirrors of the same field line** born at $(\phi,u)$. Its joint continuity follows from the equality of this integral with N-192's continuous action on the full physical three-coordinate family. Strict bounds on the two radial faces and the intermediate value theorem give attainment for every admissible height and target separately. [Physical first-well action](../../PlasmaLean/Design/DommaschkRadialActionWindows.lean) · [Height–action rectangle](height-action-rectangle.md)

Fix any action tolerance $\varepsilon>0$. One positive radial length works at every $|\phi|\le 2^{-19}$, for every $|h-h_U|\le10^{-7}$ and every $J_*-11/10000\le j\le J_*+9/10000$. Both $h$ and $j$ can be chosen independently at each phase. A uniform sample of $u$ assigns the qualifying radii probability at least $\ell/(1/125)$, since the sampling interval has length $1/125$. This sampling statement concerns the radial interpolation parameter conditional on the other coordinates. A thermal birth probability additionally needs the physical distribution of launch positions, velocities and energies. The available inequality for the height derivative concerns a different coordinate. The candidate's uniform radial length is existential here. [Physical specialization](../../PlasmaLean/Design/DommaschkRadialActionWindows.lean)

The checked implication `DommaschkRadialFirstWellActionWindows.from_nested_tori` takes the two original embedded invariant tori and the N-192 family condition on the four through-going signed paths. Its proof key is `dd9b067e6bac447b23bd7843a89465e1929bb0a1a5222509a7dc28ec9608d868`. The same generator consumes the fully grounded N-192 proof to discharge that path condition. [Physical binding and axiom audit](../../scripts/dommaschk_kam/verify_radial_action_windows.py)

## Reproduction

```sh
lake build PlasmaLean.Design.DommaschkRadialActionWindows
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_radial_action_windows.py \
  --rectangle /tmp/plasma-n192-height-action.json --faces /tmp/plasma-n188-faces.json \
  --output /tmp/plasma-n201-windows.json
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_radial_action_windows.py \
  --rectangle /tmp/plasma-n192-unconditional.json --faces /tmp/plasma-n188-faces.json \
  --wait --output /tmp/plasma-n201-unconditional.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-201 |
| Kind | Candidate-independent quantitative theorem and physical application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-188, N-192, compact uniform continuity and the length of a Lebesgue interval |
| Produces | An interval and lower radial Lebesgue mass common to every fiber and attained target, an explicit Lipschitz bound, and the first-well specialization on one original torus family |
| Status | The generic results, physical face application and original-tori implication are kernel-checked. |
| Lean evidence | `UniformRadialWindow.uniform`, `.lipschitz`, `.HasInterval.volume`, `DommaschkRadialActionWindows.of_faces`, and `DommaschkRadialFirstWellActionWindows.from_nested_tori` |
| Audit evidence | Five declarations checked with `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |
