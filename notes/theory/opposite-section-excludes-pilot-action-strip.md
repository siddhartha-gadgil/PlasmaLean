# The original phase-zero radial bracket misses the action at the opposite section

The QA2R launch chart can supply low-field births over an entire field period. The obstruction to extending the existing radial action bracket around the circle occurs later, in the integral between the first mirrors. At the established upper height \(h_U=5300546391395933/5000000000000000\), the original birth well on **every** radius \(0.470\le u\le0.478\) has action above \(j_*+3/2000\) throughout \(|\phi-\pi/2|\le2^{-19}\), according to an exact directed-arithmetic replay. Thus the prescribed level cannot pass through this strip on the opposite sector. The action is the dimensionless one-way physical arclength integral at \(j_*=6799610938322487/5000000000000000\). [Seven physical interval calculations](../../scripts/dommaschk_kam/results/bounce_opposite_action_strip.json)

## Birth accessibility and well action

The original chart holds the geometric poloidal cut at zero and interpolates the C and A radii and heights there; \(\phi\) is the geometric toroidal birth phase modulo \(\pi\). N-56 checked \(\lVert B\rVert\le1.048<h_L<h_U\) on all 32,768 launch boxes over the full field period and all \(u\in[0.44,0.54]\), including the original Q-16 torus uncertainties. Its signed collar stays below the lower height for \(1/8\) radian after birth in either direction. This is an external all-phase enclosure. [Launch and collar verification](dommaschk-launch-collar.md)

The new calculation uses the original two packed Fourier seeds, both KAM error allowances, the same physical QA2R field and a transfer to the common \(\pi/2\) section. An outward-rounded moving-frame ODE enclosure is checked in each signed direction with step \(1/64\). The first hits are identified by the accessible core, outward slopes and forbidden caps. Each action step is split into 24 panels, with the physical arclength density \(R\lVert B\rVert/B_\phi\). The independent run at \(u=0.470\) alone gives the lower endpoint \(9458528569691664331/6917529027641081856\), exceeding \(j_*\) by more than \(0.00740\). [Physical checker](../../scripts/dommaschk_kam/screen_periodic_action_faces.py)

| Closed radial interval | Action lower bound rounded down | Excess above target rounded down |
| --- | ---: | ---: |
| [0.470, 0.471] | 1.361961 | 0.002039 |
| [0.471, 0.472] | 1.362844 | 0.002921 |
| [0.472, 0.473] | 1.363726 | 0.003804 |
| [0.473, 0.474] | 1.364609 | 0.004687 |
| [0.474, 0.475] | 1.365493 | 0.005571 |
| [0.475, 0.476] | 1.366375 | 0.006453 |
| [0.476, 0.478] | 1.361423 | 0.001501 |

The larger final tile has a wider numerical enclosure. One trial over the entire interval lost positivity of an intermediate Jacobian denominator, and a width-0.002 trial starting at 0.470 missed the action threshold. The narrower accepted tiles have shared endpoints. Lean proves the exact coverage, the margin for every archived rational floor, and exclusion for arbitrary moving labels confined to the old strip when their phase reaches the opposite sector. Its theorem assumes that the physical action satisfies those seven pointwise lower bounds. Reproducing those physical ODE and quadrature inequalities in the Lean kernel remains open. [Lean arithmetic and exclusion theorem](../../PlasmaLean/Design/DommaschkOppositeActionStrip.lean)

## A period-wide application

For the same upper height, the full-period survey sampled the wider constant faces \(u=0.44\) and \(u=0.54\). The largest sampled inner action was 1.348738 and the smallest sampled outer action was 1.419684 to six decimals. The corresponding margins were about 0.01118 and 0.05976. N-59 separately checked intervals around six phase centres on these wide faces by directed arithmetic. A full-period application of the annular theorem requires uniform oriented face bounds and joint continuity of the chosen physical first-well action throughout the enclosed parameter cylinder. The present checks cover parts of that cylinder. [Full-period numerical survey](../../scripts/dommaschk_kam/results/bounce_radial_variation_20261123.json) · [Validated partial faces](dommaschk-phase-faces.md) · [Annular criterion](connected-periodic-action-separator.md)

Phase-dependent radial faces also remain possible. At \(\pi/2\) the directed local study already encloses an upper-height root between 0.456 and 0.464. A reparametrization \(u=u(\phi,s)\) with \(u(\phi,0)<u(\phi,1)\) can use those radii if its face signs and periodicity are proved. Moving the birth along one field line within the same accessible first well preserves that well's arclength action. Selecting a different field line or another well requires its own continuity and endpoint identification. [Two local root brackets](dommaschk-local-action-graphs.md)

## Replay

~~~sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
"$py" scripts/dommaschk_kam/screen_periodic_action_faces.py --cover --output /tmp/opposite-strip.json
cmp /tmp/opposite-strip.json scripts/dommaschk_kam/results/bounce_opposite_action_strip.json
"$py" scripts/dommaschk_kam/screen_periodic_action_faces.py --output /tmp/opposite-single-birth.json
"$py" scripts/dommaschk_kam/bounce_launch_box.py
lake build PlasmaLean.Design.DommaschkOppositeActionStrip
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-190 |
| Kind | Physical obstruction to a fixed full-period action chart |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-56, N-59, N-60, N-180, N-185 |
| Dependency requirement | Original Fourier torus uncertainties, the original signed field-line ODE, first-mirror crossings and directed physical arclength quadrature on each tile. |
| Produces | A strict wrong-sign interval for every radius of the old strip near the opposite section, and a wider possible global chart. |
| Status | Physical action floors externally verified. Exact finite coverage, rational thresholds and the conditional obstruction kernel-verified. |
| Lean evidence | `DommaschkOppositeActionStrip.covers`, `.strict_margins`, `.excludes` and `.moving_label_excluded`. |
| Audit evidence | Each declaration uses only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |
