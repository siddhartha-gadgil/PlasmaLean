# Action variation between two physical QA2R first wells

Fix the original pair of nested embedded tori and a launch phase $|\phi_0|\le 2^{-19}$ about section zero. Lean constructs two signed field lines through the original radial interpolations $u_i=47/100$ and $u_o=239/500$. Choose the lines before choosing the mirror height. Let $J_u(h)$ be the single-passage integral of $\sqrt{2(h-|B|)}$ with respect to Cartesian arclength between the first backward and forward mirror points enclosing the birth. [First-well action and selected paths](../../PlasmaLean/Design/DommaschkPairedFirstWellAction.lean)

For every $h$ with $h_L\le h$ and $h+1/18000\le h_U$, the outer well at $h$ contains the pilot well at $h+1/18000$. At the **same** height the two actions satisfy

$$
J_{u_o}(h)-J_{u_i}(h)>1/375,\qquad
\frac{J_{u_o}(h)-J_{u_i}(h)}{u_o-u_i}>1/3.
$$

Here $h_L=5297961656084411/5000000000000000$ and $h_U=5300546391395933/5000000000000000$. The upper endpoint has independent absolute action enclosures. This secant measures variation between two radial interpolation labels. A particle transport bound would also require a connection to guiding-centre evolution. [Earlier conditional theorem](paired-first-well-actions.md) · [Upper-endpoint action floor](second-first-well-polynomial-floors.md)

The later equal-height theorem gives a stronger secant on every height of the closed band, including the upper strip. [Closed-band action comparison](closed-height-band-action-secant.md)

## How the finite inputs close the proof

The signed ODE extends 391 slabs in each direction on the pilot and 328 on its neighbor. Each slab spans $1/64$ radian. On the aligned interval $[-325/64,325/64]$, the outer physical strength is at least $1/18000$ lower and its Cartesian arclength density is at least $3999/4000$ of the inner density. The 325 original slab pairs on each clock cover the pilot well. These comparisons and the first-well integrals use the same two physical paths. [Paired field and speed estimates](full-paired-physical-profiles.md) · [Action comparison proof](../../scripts/dommaschk_kam/verify_paired_first_well_action.py)

On the outer line, the first 317 slabs on each side are below $h_L$. Ten subsequent slabs have outward squared-strength derivative greater than $1/400$. For every height in the closed band, each first contact occurs at an elapsed angle in $(317/64,327/64)$. The contacts at $h_L$ lie in $(317/64,318/64)$ and those at $h_U$ lie in $(325/64,327/64)$. Each branch moves by strictly between $7/64$ and $10/64$ from the lower to the upper height. [First-mirror branch and its inverse derivative](secondary-first-mirror-height-band.md)

The same embedded pair carries all eight original launch traces. At section zero their verified slab counts in each direction are 391, 328, 48 and 16 in increasing radius. At section $\pi/2$ the counts are 48, 16, 8 and 5. Together they give 1,720 signed ODE steps at this checkpoint. On the other two section-zero lines the simultaneous field-margin theorem reaches $48/64$ and $16/64$ in each direction. [Common birth and margin construction](common-original-birth-margins.md)

## Verification

| Generated proof | Content-addressed key |
| --- | --- |
| Signed second line from original birth, 328 slabs each way | `c284137760b356ec5f200f47bf84afabe6bed28e3f760610bf4b0722dba4e369` |
| Common eight-launch family | `e777f3902f196aa546ab113e5e82e0b02205e367539ee65ea21c749bab5c5abc` |
| Pilot calibration on that family | `9e130b3ebade5ab449924412c0dbed6131e185edaf4599a8479eff9205cf0b63` |
| Full 325-pair comparison attached to those lines | `5a38e646cc0f0686ff044c5a84d4cbf3fe94fda1e989191c88e986032f2b5067` |
| Equal-height first-well secant on the common tori | `50bb977a8b4f6b530625c5ecef4a59b03069db63bf239508d6b4732f1c65e0b4` |

Replay the final attachment with the saved lower-well, calibrated family and paired-profile receipts.

~~~bash
.venv-ws/bin/python scripts/dommaschk_kam/verify_paired_first_well_action.py \
  --well /tmp/plasma-q0r478-first-well-lower-bridge.json \
  --calibrated /tmp/plasma-calibrated-at-328.json \
  --compared /tmp/plasma-compared325-at-328.json \
  --output /tmp/plasma-whole-first-well-secant.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-161 |
| Kind | Physical application of N-144 |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-126, N-127, N-144, N-146, N-149, N-158 |
| Dependency requirement | The original second signed field line beyond both caps and the complete paired physical profiles on the same calibrated tori |
| Produces | Equal-height action gap and radial secant on chosen physical field lines, uniformly in the permitted birth phase and shifted height band |
| Status | Kernel verified on both original births |
| Lean evidence | `DommaschkComparedFirstWellsOn391_328_48_16_48_16_8_5.from_common_tori` |
| Audit evidence | The final physical declaration uses propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
