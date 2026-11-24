# First-mirror locations and a strict action floor near the upper height

At the phase-zero QA2R launch parameter $u=239/500$, every first mirror for $h\in[H-267/2^{27},H]$ lies less than $1/512$ radian from the upper-height mirror on its own outward branch. Here $H=5300546391395933/5000000000000000$. A signed physical trajectory that reaches beyond $327/64$ therefore has both first mirrors in the outward interval $(2599/512,327/64)$ throughout this height range. The same trajectory then has one-way Cartesian action strictly exceeding $43/100$ throughout the range. These implications have been kernel-checked with the original phase-zero archives. Their application to the actual second birth awaits its signed passage through the outer brackets. [Earlier mirror branches](secondary-first-mirror-height-band.md) · [Lower action under a height change](secondary-action-height-window.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-145 |
| Title | First-mirror locations and a strict action floor near the upper height |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-127, N-135, N-138, N-141, N-142 |
| Dependency requirement | The signed second-radius physical trajectory must reach past the 327th row boundary. The strict $43/100$ floor already has all its field and quadrature inputs. The strict design target also requires the original 322-pair physical quadrature cover. |
| Produces | A uniform displacement estimate, both first-mirror locations, and a strict first-well action from the genuine central mass and outer field gap. |
| Status | Verified for every qualifying signed passage. The final 328-pair birth application is monitored independently. |
| Lean evidence | `DommaschkSecondaryHeightCollar.time_near_upper`, `MirrorActionEnvelope.action_add_shoulders`, `DommaschkQ0R478ShiftedFirstWell.from_passage`, and `DommaschkQ0R478ShiftedFirstWellShoulders.from_passage`. |
| Audit evidence | The physical conclusions use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## A strict lower bound on the actual 192-pair birth

The signed trajectory has already reached $[-3,3]$ at $u=239/500$. For every admitted birth there is one physical solution on which every $h\ge H-267/2^{27}$ simultaneously satisfies

$$
J([-3,3],h)\ge\frac{67575608917579873}{211106232532992000}>\frac8{25}.
$$

This uses the same 32-pair inner quadrature and the certified field clearance on the remaining 160 rows on each side. The equality between the closed integral and the Cartesian derivative integral is proved by pointwise agreement on the open interval. Thus the certificate only needs the within-derivative at either endpoint. This conclusion applies to the actual incoming trajectory before the first-mirror brackets are reached. The 192-pair quantitative path key is `77632ea4f6f57f8a7c27568fd48c02830f9082f05a041191455929dc2f9e6e78`. The three physical action theorems have key `4ee1481ee3ced78b0ff8d70ad9f6375603a0c5672556f7dd6602c1603d7ebad2`, with 18.87 seconds and 10.22 GiB peak resident memory. [Closed trace integral](../../PlasmaLean/Design/DommaschkIncomingHeightAction.lean) · [Birth application](../../scripts/dommaschk_kam/verify_incoming_height_action.py)

Usage from the repository root, after the N-141 and N-142 commands and the 192-pair physical checkpoint, is

```sh
lake build PlasmaLean.Design.DommaschkIncomingHeightAction
.venv-ws/bin/python scripts/dommaschk_kam/verify_incoming_height_action.py \
  --observation /tmp/plasma-projected-q0r478-192.json \
  --shifted-birth /tmp/plasma-n142-q0r478-birth032.json \
  --output /tmp/plasma-incoming-height-action192.json
```

## Where the first roots occur

The certified branch at the secondary radius gives $(1/400)|t(h)-t(H)|\le H^2-h^2$ for each signed outward time. Throughout the new window, $H^2-h^2<1/(400\cdot512)$. At $H$ each first hit has outward time greater than $325/64$. The inverse branch therefore keeps its first hit beyond $325/64-1/512=2599/512$ even without an action cover. This places the 317-pair incoming field estimate and the 322-pair quadrature window strictly between the actual first mirrors when the signed trajectory reaches the brackets. The two branches use one trajectory, with backward time reversed at the launch. [Height-window displacement](../../PlasmaLean/Design/DommaschkSecondaryHeightCollar.lean) · [Signed passage](../../scripts/dommaschk_kam/templates/secondary_shifted_well.lean.tpl)

## Integrating the outer intervals

On $[-32/64,32/64]$, the original N-138 physical cells and the N-142 height transfer give one-way action at least
$$
M_{32}=302688147275957/1688849860263936.
$$
The full signed N-135 field estimate gives $f<h_L-1/270000$ on $[-317/64,317/64]$. Therefore $\sqrt{2(h-f)}>161/5000$ in both outer intervals $[-317/64,-32/64]$ and $[32/64,317/64]$ for every height in the proposed window. The physical arclength density there is at least $7/8$, as follows from positive cylindrical radius and the norm of the physical derivative. Ordinary integral additivity on adjacent intervals now gives
$$
J([l,r],h)\;\ge\;M_{32}
   +2\frac{317-32}{64}\frac78\frac{161}{5000}
   \;>\;\frac{43}{100}.
$$
The inner integral appears once. Each outer integral uses the physical field bound on the same solution. The proof identifies the weight with the true Cartesian derivative on the complete well. The uniform lower floor applies to every height simultaneously for each admitted birth. [Adjacent integral estimate](../../PlasmaLean/Theory/Kinetic/MirrorActionShoulders.lean) · [Physical assembly](../../scripts/dommaschk_kam/templates/secondary_shifted_shoulders.lean.tpl)

| Inputs available on the long physical trajectory | First-well conclusion across the height interval |
| --- | --- |
| Physical 32-pair original action cover | $J\ge M_{32}\simeq0.17922738687$ |
| The same cover and the strengthened 317-pair incoming field archive | $J>0.43$ |
| Original 322-pair lower action cover | $J\ge2296704932228777/1688849860263936>6799610938322487/5000000000000000$ |

The first two rows have complete local input certificates. The final row requires verification of the remaining native physical action cells. The signed-path application in each row also requires the 328-pair trajectory receipt. No physical length, time, birth law or thermal fraction is fixed by these dimensionless results.

## Reproduction

Run N-135, N-138 and N-142 to produce their receipt files. The first three commands below verify both implications without a completed long trace. The final command attaches the strict $43/100$ result to every admitted birth on the same pair of embedded tori once the 328-pair signed receipt is available.

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkSecondaryHeightCollar PlasmaLean.Theory.Kinetic.MirrorActionShoulders
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_shifted_well.py \
  --upper-well /tmp/plasma-q0r478-first-well-lower-bridge.json \
  --shifted-birth /tmp/plasma-n142-q0r478-birth032.json \
  --output /tmp/plasma-q0r478-shifted-first-well-bridge.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_shifted_well.py \
  --upper-well /tmp/plasma-q0r478-first-well-lower-bridge.json \
  --shifted-birth /tmp/plasma-n142-q0r478-birth032.json \
  --clearance /tmp/plasma-n135-q0r478-317.json \
  --output /tmp/plasma-q0r478-shoulder-first-well-bridge.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_shifted_well.py \
  --upper-well /tmp/plasma-q0r478-first-well-lower-bridge.json \
  --shifted-birth /tmp/plasma-n142-q0r478-birth032.json \
  --clearance /tmp/plasma-n135-q0r478-317.json \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/328.json \
  --output /tmp/plasma-q0r478-strict-shoulder-action328.json
```

Use `--full-cover` with the original, authenticated 322-pair physical cover to check the strict design target on the 328-pair birth path. The basic first-well proof key is `c4d62ce53906c773a200c7d2d13873a37789f53db08e9a2ec3ead5c3d2fef288`. The strict $43/100$ proof key is `2c4d8ed862ebeb215bf7dc933aa475f44fe400765193b63a9b0f91ea2beb226e`. These applications took 6.14 and 6.24 seconds respectively with one Lean worker and about 6.2 GiB peak resident memory. [Workstation verifier](../../scripts/dommaschk_kam/verify_secondary_shifted_well.py)
