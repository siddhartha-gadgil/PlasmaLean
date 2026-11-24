# Positive trapped-reference mass in the original five birth coordinates

For the QA2R pilot, the predeclared guiding-centre reference population contains a nonempty open set in the five coordinates $(x,v_\parallel,\mu)$ for each strict sign of $v_\parallel$. This holds for any symbolic mass $m>0$, any positive energy $e$, and each height $h$ in the closed N-99 band, provided the energy cut contains $e$ in its interior and the pitch cut contains $1/h$ in its interior. Both signed populations have positive five-dimensional Lebesgue volume. More generally, every birth measure that charges nonempty open sets assigns positive mass to each signed population’s interior. [Contracted reference population](../../PlasmaLean/Theory/Contract/TrappedBirthBand.lean) · [Ground theorems](../../scripts/dommaschk_kam/verify_trapped_birth_coordinates.py)

The pointwise theorem uses the same nested Q-16 tori for all admitted original angles $|\phi|\leq 2^{-19}$. Set $x$ to their actual interpolated Cartesian birth at $u=47/100$. The two signed physical reference branches realize the following exact coordinates:

$$
\mu=\frac e h,\qquad
v_\parallel=\pm\sqrt{\frac{2(e-\mu\|B(x)\|)}{m}} .
$$

The field strength at this birth is strictly less than $h$ throughout the whole pilot height band. Thus $\mu>0$ and both parallel velocities are nonzero. The Hamiltonian $H=m v_\parallel^2/2+\mu\|B(x)\|$ equals the prescribed $e$, the mirror height $H/\mu$ equals $h$, and the pitch $\mu/H$ equals $1/h$. The contract’s physical units are mass in kilograms, $H$ in joules, $\mu$ in joules per tesla and $\mu/H$ in inverse tesla. The QA2R height bounds use the field’s model normalization. The proof does not choose a device scale, species, energy spectrum or birth law. [Physical Hamiltonian](../../PlasmaLean/Theory/Kinetic/GuidingCentreLittlejohn.lean) · [Construction and exact identities](../../PlasmaLean/Theory/Contract/TrappedBirthCoordinates.lean)

For the pilot, N-114 places $(x,h)$ in the interior of the regular-mirror position–height set. Near either constructed phase-space birth, $H$, $H/\mu$ and $\mu/H$ are continuous because the field norm is continuous and the two denominators are strictly positive. Taking the inverse images of the mirror neighborhood and the energy and pitch interiors gives an open neighborhood in all five original coordinates. Any additional support cut whose interior contains the constructed point can be intersected with that neighborhood. The ground positive-mass statements use, in turn, the whole positive parallel-velocity half-space and the whole negative half-space for the support. [Cartesian mirror neighborhoods, N-114](cartesian-open-regular-pilot-births.md) · [Candidate specialization](../../PlasmaLean/Design/DommaschkTrappedBirthCoordinates.lean)

This proves qualitative positive mass of the eligible reference. A numerical trapped fraction still requires a specified measure, normalization and quantitative mass bounds. Radial excursion and survival to a chosen confinement time require information about the subsequent guiding-centre dynamics; these claims remain open.

## Reproduction

Use the verified height-band passage from N-99. Its content key is `9c00a57de9e2b1b2cc49b184ca9862539bc1c68c69f74d7c45fefcf531bb9809`.

```bash
lake build PlasmaLean.Design.DommaschkTrappedBirthCoordinates
.venv-ws/bin/python scripts/dommaschk_kam/verify_trapped_birth_coordinates.py \
  --passage /tmp/plasma-mirror-height-passage-325.json \
  --output /tmp/plasma-trapped-reference-325.json
```

The three ground declarations passed the Lean kernel and axiom audit in two independent build directories with key `40a38ad33b1100f2042f145fc43297e3cd5b6b823ee6eb30367eb32d566dc6db`. The first composition took 6.021 seconds with a peak resident set of 7,837,876 KiB. Replaying N-114 with the shared driver retained its original key `e3b0d295e97d…`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-117 |
| Title | Positive trapped-reference mass in the original five birth coordinates |
| Kind | Physical theorem and ground certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-100, N-112, N-114 |
| Dependency requirement | Strictly submirror physical field strength at the admitted pilot birth, continuity of the field norm there, and an open position–height neighborhood of regular births. |
| Produces | Genuine local open sets and positive mass of the contracted reference in Cartesian position, parallel velocity and magnetic moment for both signs, arbitrary positive mass/energy and symbolic open energy/pitch cuts. |
| Difficulty | Realize the specified Hamiltonian and reciprocal pitch with the original coordinates while keeping the two signs and the full five-dimensional topology. |
| Status | Compiled Lean theorem; ground assembly reproduced. |
| Lean evidence | `TrappedBirthCoordinates.lift_values`, `.lift_mem_interior`, `DommaschkTrappedBirthCoordinates.from_path`, `DommaschkThermalReference325.from_birth`, `.signed_positive_mass`, `.signed_positive_volume`. |
| Audit evidence | `propext`, `Classical.choice` and `Quot.sound` only. |
| Last updated | 25 November 2026 |
