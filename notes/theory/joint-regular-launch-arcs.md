# One guiding-centre time for two radii and all launch phases

The complete central arcs at radial labels $0.470$ and $0.478$ share one positive local vacuum guiding-centre time, even with continuously many launch phases on one original pair of embedded QA2R tori. At the inner label the observation covers $|t|≤316/64$. At the outer label it covers $|t|≤317/64$. The conclusion takes the union of the physical birth states from both arcs before choosing the duration. [Joint-family theorem](../../PlasmaLean/Design/DommaschkJointLaunchArcs.lean) · [Single-radius result and model contracts](common-time-across-pilot-launches.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-160 |
| Title | One guiding-centre time for two radii and all launch phases |
| Kind | Theorem and physical application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-127, N-147, N-150, N-154 |
| Dependency requirement | Both radial labels need a genuine signed field-line passage from the common torus family and regular first-mirror branches on both sides. The physical application uses the 391-pair inner path and at least 328 signed pairs at the outer label. |
| Produces | A single positive local guiding-centre time and open controlled set for all phases, both radial families, both velocity signs and the whole chosen energy-height rectangle. |
| Status | Kernel verified through both original physical births, across the complete 391-pair inner trace and 328-pair outer trace. |
| Lean evidence | `DommaschkJointLaunchArcs.simultaneous`, `DommaschkJointLaunchArcs.two_families` and `DommaschkJointRegularLaunchArcs.from_family`, with `DommaschkTwoRadiusRegularArcs391_328_48_16_48_16_8_5.through_both_births` as the physical instance. |
| Audit evidence | The three standalone generic declarations, the two-radius implication and the final physical theorem use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## The two families

Once the tori are fixed, each $|φ_0|≤2^{-19}$ has an inner trajectory $y_{φ_0}$ and an outer trajectory $z_{φ_0}$. At $t=φ_0$ the trajectories pass through the original torus interpolations at $u=47/100$ and $u=239/500$ respectively. Both satisfy their signed physical ODE. The calibrated action and flight-time information is retained on the inner trajectory. For every Cartesian point of either specified central arc and every archived height, the position-height pair lies inside the open regular-birth set. [Regular births on a signed arc](compact-regular-birth-arcs.md) · [Physical two-radius proof](../../scripts/dommaschk_kam/templates/joint_regular_launch_arcs.lean.tpl)

Fix $m>0$, $q≠0$, $0<e_0≤e_1$ and an excursion limit $d>0$. One $T>0$ serves the union of all the signed guiding-centre seeds, at both radii, all admitted launch phases, all points of their central arcs, all heights $h_L≤h≤h_U$ and all energies $e_0≤e≤e_1$. The support must contain all these lifted seeds in its interior, the energy cut must contain $[e_0,e_1]$ in its interior, and the pitch cut must contain $1/h$ in its interior for every allowed $h$. The time is chosen before the support and the cuts. They determine an open set $W$ contained in the physical trapped reference and containing every lifted seed. Its orbits exist up to $T$. Every partial orbit of duration at most $T$ stays within the specified displacement cap relative to its initial position and satisfies the regular-denominator condition. Under the open-positive sampling hypothesis and a measurable finite reference, the covered fraction is positive. The theorem supplies an existential $T$ and fraction. Numerical values and an operating point in physical units remain open.

The field-line selection can depend on $φ_0$. All points from both selected families lie in the compact cylindrical envelope $7/8≤R≤1$, $|z|≤5/64$. This is the same Cartesian enclosure used for the pilot. Every azimuth has a representative in $[-π,π]$, which fits inside its original angle chart. Closed velocity and magnetic-moment bounds put every lifted seed in one compact regular set. Intersecting its open control neighborhood with the trapped reference gives the one $W$. The proof needs no continuous choice of field lines over the phase interval. It quantifies the two specified radial interpolation labels. A continuum of radial labels would require additional birth evidence.

## Reproduction

The field and slope inputs are the original second-radius branch certificates. The prepared implication can be checked before a joined outer trajectory arrives.

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkJointLaunchArcs
.venv-ws/bin/python scripts/dommaschk_kam/verify_joint_regular_launch_arcs.py \
  --regular-arcs /tmp/plasma-n147-regular-arcs-192.json \
  --output /tmp/plasma-joint-regular-launch-arcs-prepared.json
```

The second-radius branch-to-regularity theorem has key `439bb8c98a8824927ec3d6de41b4c07cd323d0126cc89c29766c80474bc74ffd`. The checked physical implication has key `04dd3f4c625e5794b40fe89e48c8f456731b38bc5f4b143045b97a8948304002`. It checks in 3.44 seconds with a peak of 4.66 GiB. The driver accepts the original common-family receipt for an unconditional application only when it confirms both physical birth arcs, including at least 328 signed outer slab pairs. [Reproduction driver](../../scripts/dommaschk_kam/verify_joint_regular_launch_arcs.py)

For the actual two-radius result, first attach the two regular populations to the accepted 328-pair common physical family, then audit the common-time conclusion.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_regular_birth_arcs.py \
  --well /tmp/plasma-q0r478-first-well-lower-bridge.json \
  --calibrated /tmp/plasma-calibrated-at-328.json \
  --output /tmp/plasma-n147-regular-arcs-328.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_joint_regular_launch_arcs.py \
  --regular-arcs /tmp/plasma-n147-regular-arcs-328.json --require-both \
  --output /tmp/plasma-joint-regular-launch-arcs328.json
```

| Physical evidence | Kernel key |
| --- | --- |
| Signed outer trajectory, 328 slabs each way | `c284137760b356ec5f200f47bf84afabe6bed28e3f760610bf4b0722dba4e369` |
| Both outer first mirrors at every archived height | `530e7e4f34666a851d01e0b455e63e33cc30cce20d4171518e66126d9af1bbf7` |
| Calibrated original tori at the final checkpoint | `9e130b3ebade5ab449924412c0dbed6131e185edaf4599a8479eff9205cf0b63` |
| Two actual regular populations on those tori | `10b1df807917ba6f4617e91b728270cd2c526f3f60a3d384afcfe7b8c57ebeb0` |
| Common guiding-centre duration through both original births | `258d04a812a96db9664271d4bf4b8f2c2923ff55b21944e939b6f91d8e6e37df` |

The final proof and its kernel axiom audit took 61.82 seconds on one worker with peak resident memory of 23.81 GiB. A negative test with the 192-pair outer receipt rejected the request for the two physical families.

The separate original-birth margin replay at this final checkpoint continues to certify $\lVert B\rVert<h_L-1/270000$ on $|t|≤317/64$ of the longer outer trajectory, and the two further margins on the 48-pair and 16-pair paths at $0.523$ and $0.531$. Its accepted family key is `3144c90d5e77a869ed6ffaf20147af8855497d8faff20443aaca6941b40ba82a`. [Phase-zero physical margins](common-original-birth-margins.md)
