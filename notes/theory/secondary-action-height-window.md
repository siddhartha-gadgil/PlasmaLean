# A positive height interval for the second launch’s lower action

At the phase-zero QA2R launch parameter $u=239/500$, the same original 30,912 quadrature panels suffice to prove the strict lower action target throughout a closed interval ending at the prescribed upper height. Its width is $267/2^{27}$, approximately $1.9893\times10^{-6}$. The full first-well comparison requires the original upper-height physical cover and the first mirrors at the height of interest. A shorter integral is already verified on an actual trajectory from birth throughout the entire height interval. No additional field approximation or trajectory solve enters the height transfer. [Original action quadrature](secondary-native-lower-action-cells.md) · [Signed birth and cover](secondary-action-cover-from-birth.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-142 |
| Title | A positive height interval for the second launch’s lower action |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-127, N-134, N-138 |
| Dependency requirement | The exact shifted archive requires the original lower quadrature digits. The first-well target also requires the original physical core cover on the same field line, the first well at the new height, and ordinary continuity and nonnegativity on that well. |
| Produces | A lower-cover transfer under a change of height, a uniform squared-speed floor, two strict second-radius comparisons conditional on the original physical inputs, and a grounded 3,072-panel lower action throughout the wider interval. |
| Status | Kernel-verified on the stated domains. Both remaining full first-well inputs can be supplied independently. |
| Lean evidence | `LowerActionHeightShift.covers`, `DommaschkSecondaryActionHeight.first_well`, generated `DommaschkQ0R478ShiftedAction267.first_well`, and `DommaschkShiftedActionBirth267R032Of048.from_nested_tori`. |
| Audit evidence | The final physical and first-well theorems use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Reusing the physical cells

Let $H=5300546391395933/5000000000000000$, and write $f(t)$ for field strength and $w(t)$ for Cartesian arclength density. Each original cell bounds $w$ from below and supplies a nonnegative lower bound $g$ on $\max(2(H-f),0)$. For $h\ge H-\delta$ the same cell gives
$$
\max(g-2\delta,0)\le \max(2(h-f),0).
$$
The proof includes equality at the turning threshold and overlapping closed panel boundaries. Each new density digit is compared with the original, and each new squared-speed digit is bounded by the truncated natural subtraction of the corresponding original digit and the change in squared speed. Python proposes the integer square roots. Lean rechecks each proposed lower root by squaring it, checks all bounds against the original chronological records, and adds their contributions exactly. [Lower-cover height transfer](../../PlasmaLean/Certificates/LowerActionHeightShift.lean) · [Exact proof generator](../../scripts/dommaschk_kam/verify_secondary_action_height.py)

The two computations below use the original blocks $[5,649)$, with 322 elapsed slabs on either side of the section and 48 panels per slab. The design target is $J_*=6799610938322487/5000000000000000$.

| Maximum height decrease | Certified lower mass | Excess over target | Least shifted squared-speed digit |
| --- | --- | --- | --- |
| $2^{-19}$ | $574178976890867/422212465065984$ | $6.8158554\times10^{-6}$ | 25412 |
| $267/2^{27}$ | $2296704932228777/1688849860263936$ | $3.1715179\times10^{-7}$ | 25401 |

A digit represents $2^{-26}$ units of squared speed. Both minimum digits are positive, so the whole closed interval $[-322/64,322/64]$ has $f<h$. Any first mirrors $l<0<r$ at this height on the same path therefore satisfy $l<-322/64$ and $322/64<r$. Integrating the shifted rectangles on this core and using nonnegativity on the enclosing well gives $J_*<\text{lower mass}\le J([l,r],h)$. The abstract implication holds for every $h\ge H-\delta$ whenever those physical hypotheses are supplied. The N-127 mirror branch is limited to its established height band. The row cover and the true joined trajectory through the outer brackets are still needed to apply the full inequality to the second physical birth. [First-well implication](../../PlasmaLean/Design/DommaschkSecondaryActionHeight.lean) · [Second-launch mirror branch](secondary-first-mirror-height-band.md)

For the next grid width $268/2^{27}$, independent integer arithmetic with the same density digits and maximal downward-rounded speed digits gives an excess of $-2.4669325\times10^{-7}$. This measures the resolution and slack of this lower quadrature. The physical inequality at that width remains open.

## The actual short interval

The 32 signed row pairs of the original birth cover yield 3,072 verified shifted panels on the same increasing-angle field line. For every admitted birth angle on the original pair of embedded field tori, there is one signed trajectory through 48 slabs in each direction such that, simultaneously for every $h\ge H-267/2^{27}$,
$$
J([-1/2,1/2],h)\ge \frac{302688147275957}{1688849860263936}
\simeq 0.17922738687 .
$$
The weight is the norm of the derivative of the Cartesian trajectory. The birth approach, the two signed ODEs, and the estimate across all heights use the same section state and solution. [Physical attachment](../../scripts/dommaschk_kam/verify_secondary_action_height_birth.py) · [Geometric arclength identification](../../PlasmaLean/Design/DommaschkLowerActionPath.lean)

## Reproduction

Start with the N-138 32-pair physical cover on its 48-pair signed path. The complete height-transfer certificates can be checked independently of that path.

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkSecondaryActionHeight
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_height.py \
  --output /tmp/plasma-n142-q0r478-256.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_height.py \
  --ticks 267 --output /tmp/plasma-n142-q0r478-267.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_cover.py \
  --band /tmp/plasma-q0r478-all-height-branches.json --pairs 32 \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/048.json \
  --output /tmp/plasma-n142-original-birth032.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_height_birth.py \
  --height /tmp/plasma-n142-q0r478-267.json \
  --birth-cover /tmp/plasma-n142-original-birth032.json \
  --output /tmp/plasma-n142-q0r478-birth032.json
```

The original quadrature archive SHA-256 is `6e648c2368dafde467a2a1f52aea87383420cca865251222420d84ef2dff055c`. The 256-tick proof key is `c1f6d38c3f8cd5dd2f2b0b506ba3b3ab6d8520c2b4070b79513b822dbe63fa3b` and the 267-tick key is `9688ea88d914635f7dba6a049484e7b0555d79e00bd0a0a08fd8c3d499ceefa1`. Each took about 23 seconds with one Lean worker and approximately 3.1 GiB peak resident memory. The original physical birth key is `2f66ddc3fff4b8295abdf6a70572a919427da0b700e0e621dae20803ab67837d`. The shifted physical theorem has key `7f303e6c3d35f1d9bd47e45237b30dca77b03f077dc59ff482a1aa2ca9bb4edb`, with 10.8 seconds and 6.13 GiB peak resident memory.
