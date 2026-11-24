# A whole-well action cap bounds the physical flight time at every mirror height

For every QA2R birth in the phase-zero sector $|\phi|\le 2^{-19}$ at radial interpolation parameter $u=47/100$, the dimensionless one-way time $T(h)$ between the first two mirrors satisfies

$$
T(h)>\frac{9006443340496896}{163793158879589}>54.98668
\qquad(h_L\le h\le h_U).
$$

At the upper height the narrower mirror brackets give

$$
T(h_U)>\frac{9468238224162816}{163793158879589}>57.80606.
$$

The same physical trajectory satisfies **$T(h)<264$** and $J(h)\le 1146552112157123/844424930131968$ throughout the closed height band. At each height all three inequalities refer to precisely the same two first mirrors. [Flight-time proof](../../PlasmaLean/Design/DommaschkActionFlightFloor.lean) · [Physical action cap](dommaschk-native-first-well-action-enclosure.md) · [Rowwise upper time budget](rowwise-first-mirror-flight-budget.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-116 |
| Title | A whole-well action cap bounds physical one-way flight times |
| Kind | Proof and certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-101, N-103, N-106, N-108, N-109 |
| Dependency requirement | True transverse first mirrors and integrable one-way flight over a band, an upper action bound on the same path, a lower arclength density and the physical mirror brackets. |
| Produces | Two-sided uniform flight-time bounds and a common action cap on the closed height band of the phase-zero pilot, and a reusable signed-path restriction theorem. |
| Difficulty | The height, the original birth, the moving first mirrors and the upper action certificate must refer to one physical field line. |
| Status | Verified |
| Lean evidence | On demand. `LaunchWell.time_floor_of_action_cap`, `Path.take_through`, `DommaschkActionFlightFloor.join_bounds`, `DommaschkActionFlightFloor326.shorter` and `DommaschkActionFlightFloor326.from_birth`. |
| Audit evidence | The audited declarations use only `propext`, `Classical.choice` and `Quot.sound`. The final application was compiled in two independently allocated caches. |
| Last updated | 25 November 2026 |

## A general flight-time inequality

**[Lean]** Let $l<c<r$ be the first-mirror well containing a launch at $c$ and height $h$. On this time window let $f$ be the field strength, $w$ the physical arclength density, and $v(t)=\sqrt{2(h-f(t))}$. Suppose $f,w$ are continuous, $f<h$ in the interior, $w\ge m>0$ there, $w/v$ is interval-integrable, $r-l>d\ge0$, and $J=\int_l^r wv\le C$ with $C>0$. Then

$$
T=\int_l^r\frac{w}{v}>\frac{(dm)^2}{C}.
$$

Indeed, the physical length $L=\int_l^r w$ exceeds $dm$. The integrands of both $J$ and $T$ are positive inside the well, and the length–action inequality gives $L^2\le JT\le CT$. Integrability of $w/v$ handles the two singular turning points. [Length–action inequality](../../PlasmaLean/Theory/Kinetic/MirrorTimeActionBounds.lean) · [Action-cap theorem](../../PlasmaLean/Design/DommaschkActionFlightFloor.lean)

## Application to the signed field line

**[Lean]** The two levels are $h_L=5297961656084411/5000000000000000$ and $h_U=5300546391395933/5000000000000000$. The proof starts from the 326-slab-per-direction trajectory carrying N-101. Restricting it to its first 325 rows preserves the function $y$ and its starting point. At the last retained clock the moving frame and reference centre agree with the stored exit ellipsoid. The nine N-99 signed slope pairs on rows 316 through 324 therefore apply to the original trajectory. This gives the regular arclength birth, a finite positive flight time and the continuous strictly increasing first-well action from N-99. [Signed path restriction](../../PlasmaLean/Design/DommaschkSignedTracePrefix.lean) · [Closed-height first mirror branches](dommaschk-mirror-height-band.md)

**[Lean]** On the full closed window $[-325/64,325/64]$, the N-101 Cartesian derivative density agrees with $w=R\lVert B\rVert/B_\phi$. Every moving first well is contained in this window. Extending the integral of the nonnegative clipped speed to the full window and raising the height to $h_U$ put $J(h)$ below the N-101 rectangle sum. The polar-coordinate identity gives $w\ge R\ge 7/8$. For all heights the two first mirrors are separated by more than $632/64$ radians. At $h_U$, uniqueness of the launch-connected well identifies them with the N-101 contacts, separated by more than $648/64$ radians. Substituting these two widths into the general inequality gives the stated bounds. [Physical density on the signed path](../../PlasmaLean/Design/DommaschkSignedTraceDensity.lean) · [Toroidal field and earlier flight bounds](toroidal-field-and-flight-bounds.md)

**[Lean]** The 316 checked central row budgets also apply to the restricted trajectory. The central time on its two sides is below 224, and the two collars together add less than 40. Uniqueness of a launch-connected first well identifies both endpoints from this integral budget with those used in the lower bound. The final theorem quantifies one trajectory before choosing the height, then gives its regular passage, the N-101 whole-well action enclosure, and both time bounds. [316-row integration](rowwise-first-mirror-flight-budget.md) · [Same-path application](../../scripts/dommaschk_kam/verify_action_flight_floor.py)

This is a time for a single passage from one mirror to the other in the dimensionless model. Dimensional flight time needs the physical operating point. A radial confinement time also needs control of drift across field lines.

## Reproduce

Use the authenticated N-99 nine-row height-band receipt, the complete N-101 first-well receipt and the 316-row physical flight-budget receipt. The driver checks their artifact hashes, recompiles the 326-path application and audits its declarations.

```sh
LEAN_NUM_THREADS=1 lake build PlasmaLean.Design.DommaschkActionFlightFloor \
  PlasmaLean.Design.DommaschkSignedTracePrefix
.venv-ws/bin/python scripts/dommaschk_kam/verify_action_flight_floor.py \
  --band /tmp/plasma-mirror-height-band-325.json \
  --well /tmp/plasma-native-first-well326.json \
  --ceiling /tmp/plasma-row-flight-budget-325.json \
  --output /tmp/plasma-action-flight-bounds326.json
```

| Receipt | Content key |
| --- | --- |
| N-99 signed slopes | `cbc98f80c06f8025f89fed9551428c2fe7bb4d1f194bcd9f48a9aea4fdc81c09` |
| N-101 actual first-well action | `e6e025e1ccba98eb4df7de15697cf820b6564dd88475764027cea45ddc89b4a5` |
| N-109 rowwise flight budget | `c4ac967fe45011cc979a5ed6f869d7ae636ebb70a6448e6d249bc823957bc75a` |
| N-116 joint first-well bounds | `b6ac397c407f40fe6a6be95626647eeff6df1d8333393ca9f168498293aa4474` |
