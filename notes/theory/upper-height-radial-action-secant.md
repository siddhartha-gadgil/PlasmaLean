# Equal-height radial action secant at the upper mirror height

For every phase-zero birth angle $|\phi_0|\le 2^{-19}$ there are two physical field lines, through the radial interpolants $u_i=47/100$ and $u_o=239/500$ on the same embedded QA2R tori. At the common height $h_U=5300546391395933/5000000000000000$ their one-way first-well actions satisfy

$$
 J_o(h_U)-J_i(h_U)>1/250,\qquad
 \frac{J_o(h_U)-J_i(h_U)}{239/500-47/100}>1/2 .
$$

Here $J(h)$ integrates $\sqrt{2(h-|B|)}$ against Cartesian arclength between the first two contacts with $|B|=h$ enclosing the birth section. At the upper height the pilot contacts occur at elapsed angles in $(324/64,325/64)$ in both directions. The second field line reaches its contacts in $(325/64,327/64)$. The two actions lie on opposite sides of the exact target $6799610938322487/5000000000000000$. [Pilot action](dommaschk-native-first-well-action-enclosure.md) · [Outer action](second-first-well-polynomial-floors.md)

## The same field lines throughout the comparison

The two nested embedded invariant tori are chosen before the birth angle. Both trajectory positions at $\phi_0$ equal the original interpolated births at that angle. The pilot retains its calibrated passage, action, flight-time and height-variation statements. The second trajectory retains its original signed ODE and both checked row lists. On these same curves, the earlier shifted-height theorem gives a gain greater than $1/375$ whenever both $h$ and $h+1/18000$ belong to the admitted height band. The independent upper-height calculation uses the physical integrals directly. [Shifted-height comparison](paired-first-well-actions.md) · [Original birth identification](../../PlasmaLean/Design/DommaschkPhaseZeroRegularBirth.lean)

Subtracting the pilot upper bound $1146552112157123/844424930131968$ from the outer lower bound $790254733800996141875465767/580284393415022003858964480$ gives the rational lower bound

$$
 \frac{2350121821065374123560487}{580284393415022003858964480}
 \simeq 0.004049948349006444.
$$

The radial spacing is $1/125$, giving a secant of at least $0.5062435436258055$ to the displayed precision. This finite difference concerns two specified radial labels. An intermediate birth of prescribed action would additionally require continuity of the first-well action, or a suitable continuation theorem, across the intervening radial interval. [Physical theorem and exact comparison](../../scripts/dommaschk_kam/templates/top_height_action_secant.lean.tpl)

## Reproduction

```bash
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
.venv-ws/bin/python scripts/dommaschk_kam/verify_top_height_secant.py \
  --well /tmp/plasma-n156-first-well.json --regular /tmp/plasma-n147-regular-arcs-328.json \
  --compared /tmp/plasma-compared325-at-328.json --output /tmp/plasma-n162-upper-secants.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-162 |
| Kind | Physical finite-difference bound |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-101, N-144, N-147, N-156 |
| Dependency requirement | A calibrated pilot and signed outer trajectory from the same embedded family, upper-height physical endpoint bounds, and the complete paired field comparison. |
| Produces | Endpoint signs and an upper-height secant above one half, with the shifted-height gains on the same two original lines. |
| Status | Kernel-verified for every admitted phase-zero birth angle on the common nested embedded tori. |
| Lean evidence | `DommaschkTopHeightSecant391_328_48_16_48_16_8_5.top_of_wells`, `.both_on_paths` and `.from_common_tori`. |
| Audit evidence | All three declarations were checked using only propext, Classical.choice and Quot.sound. The receipt key is `60e4464aad8a4b797c7c006fc20736f20defd348a3a39d2f5310fef75ee41d46`. |
| Last updated | 25 November 2026 |
