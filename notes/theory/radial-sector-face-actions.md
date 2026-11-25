# Strict endpoint actions on both radial faces of the phase sector

There is one pair of nested, embedded QA2R invariant tori for which the two radial faces of the launch sector have opposite strict action inequalities at every $|φ|≤2^{-19}$. At the archived upper mirror height $h_U=5300546391395933/5000000000000000$, the first-well action on the inner face $u=47/100$ is strictly below $J_*=6799610938322487/5000000000000000$. On the outer face $u=239/500$ it is strictly above $J_*$. These inequalities hold for **any** family of enclosed physical trajectories through the original interpolated births, and for any first-well endpoints chosen on those two trajectories. [Physical sector-face theorem](../../PlasmaLean/Design/DommaschkSectorFaces.lean) · [Certified endpoint action comparison](upper-height-radial-action-secant.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-182 |
| Kind | Endpoint action inequalities on the boundary of the physical radial–phase rectangle |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-162, N-169, N-171 |
| Dependency requirement | The independently certified inner and outer first wells at the same height on the same embedded tori. The universal transfer uses the original launch positions and the physical ODE in the regular cylindrical window. |
| Produces | The four radial-tile entries, the radial first-well continuation comparison, and strict inequalities for arbitrary endpoint well witnesses, simultaneously at every admitted launch phase. |
| Status | Kernel verified for the two concrete QA2R endpoint actions. The proof gives the two boundary conditions required by a connected prescribed-action level-set argument. Realizing an entire physical sector also requires through-going signed trajectories at intermediate radii. |
| Lean evidence | `DommaschkSectorFaces.FaceSigns`, `of_endpoint_witnesses`, and `DommaschkSectorFacesOn391_328_48_16_48_16_8_5.from_entries` and `.from_nested_tori`. |
| Audit evidence | The reusable transfer and both generated physical theorems use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Quantifier order and physical transfer

The torus pair is fixed before the phase. For each phase, let $Y(u,t)$ be any radial family of QA2R angle-time trajectories with $Y(u,φ)$ equal to the original interpolated birth at that same phase and radius. Suppose each trajectory satisfies the signed ODE and the regular bounds $7/8≤R≤1$, $|z|≤5/64$ throughout $[-331/64,331/64]$. For any two first wells surrounding zero on the inner and outer trajectories, let their endpoints be $l,r$ and $L,R$ respectively. The theorem gives
$$
J(Y(47/100),l,r;h_U)<J_*<J(Y(239/500),L,R;h_U).
$$
The action uses the true Cartesian arclength density along the physical field line. The endpoint comparisons need neither continuity in the radial parameter nor a choice of common mirror times between the different radii. [Signed field ODE and action transfer](../../PlasmaLean/Design/DommaschkRadialFamilyContinuity.lean)

The independently verified inner trajectory has 391 signed slabs on each side, and the outer trajectory has 328. Their certified first wells lie within the common comparison interval $[-327/64,327/64]$. On each face the original position at $φ$ identifies the endpoint reference line with the selected family trajectory by uniqueness of the smooth field ODE within that interval. Their field strengths and true arclength densities agree throughout the first well. Uniqueness of the first connected well around zero then identifies any proposed pair of endpoints with the independently verified pair. This gives the strict actions on the selected family without extending the outer endpoint witness to row 331.

The same selected torus Fourier functions supply N-169’s tile entries at every radial parameter, N-171’s prescribed action or grazing alternative, and the two face signs. Thus a later topological argument can use all three on one physical sector. [Tile entry certificates](upper-radial-ribbon-entry-and-caps.md) · [Physical continuation](radial-field-line-continuation.md)

## Reproduction

First build the N-171 physical flow receipt with the command in that note. The verifier reads the already authenticated endpoint-trajectory reconstruction, including both original births, enclosures and action comparisons. A cap-sign receipt without endpoint actions was rejected. [Face verifier](../../scripts/dommaschk_kam/verify_radial_sector_faces.py) · [Generated theorem template](../../scripts/dommaschk_kam/templates/radial_sector_faces.lean.tpl)

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkSectorFaces
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_sector_faces.py \
  --flow /tmp/plasma-n171-flow.json --output /tmp/plasma-n182-sector-faces.json
```

| Checked dependency or result | Proof key |
| --- | --- |
| Original upper-height action comparison | `60e4464aad8a4b797c7c006fc20736f20defd348a3a39d2f5310fef75ee41d46` |
| Original radial family and endpoint entries | `3e0dc892ec8288711f16918a67cecc9e581ca2c1bdc9fce1aa5aad2828289542` |
| Strict face actions and the common embedded torus family | `f16e0b14ee714946883492db127474f9d0692eb82fd90355a050dacc834ef38d` |

The physical replay and axiom audit used one Lean worker for 49.64 seconds at 27.80 GiB peak resident memory.
