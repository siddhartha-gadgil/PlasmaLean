# One-way flight time across the whole first-mirror height band

For the QA2R launch at radial interpolation parameter 47/100, poloidal parameter zero and geometric birth angle $|\varphi|\le 2^{-19}$, the dimensionless time $T$ from the first left mirror to the first right mirror satisfies **$14<T<4450$** for every height in the closed archive band, including its lower endpoint. On the upper half N-106 also gives **$T<592$**. Both mirrors, the arclength weight and the central integral belong to the same physical field line. The thermal birth distribution and the dimensional time scale remain open. [Flight-time inequality](../../PlasmaLean/Design/DommaschkFullBandFlightBounds.lean) · [Earlier upper-half estimate](toroidal-field-and-flight-bounds.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-108 |
| Title | A bound for the whole pilot first-mirror flight-time band |
| Kind | Exact certificate and integral estimate |
| Addresses | G-6, G-10, Q-1, Q-16, Q-35 |
| Depends on | N-84, N-98, N-99, N-103, N-106 |
| Dependency requirement | Signed physical pre-mirror enclosures, one regular passage, the nine squared-strength slope certificates and the all-angle toroidal field bound. |
| Produces | A uniform submirror clearance on the central interval, an upper bound for the time spent in both outer collars and a numerical time interval at every height. |
| Difficulty | At the lowest height the earlier central clearance was only qualitative. Each time integrand also has two singular endpoints. |
| Status | Verified |
| Lean evidence | DommaschkCoreClearance.of_gap, DommaschkFullBandFlightBounds.on_path, and the generated DommaschkFullBandFlight325.from_birth. |
| Audit evidence | The signed core and the physical application both report only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |

## Central clearance and endpoint collars

Write $h_L=5297961656084411/5000000000000000$, $h_U=5300546391395933/5000000000000000$, $f(t)=\lVert B(x(t))\rVert$ and $a=316/64$. Replaying the 316 signed slabs requires 317 distinct polynomial enclosures because the final slab is split. The least margin below zero for the cancelled polynomial $R^{16}(f^2-h_L^2)$ is $9805062521428029113/1208925819614629174706176$, about $8.11056\times10^{-6}$. On $0\le R\le1$ subtracting $1/270000$ from the test height raises the polynomial by less than $1/125000$. Lean consequently proves $f(t)<h_L-1/270000$ throughout $[-a,a]$ on the actual signed path. [Clearance lemma](../../PlasmaLean/Design/DommaschkCoreClearance.lean) · [Row proof builder](../../scripts/dommaschk_kam/verify_core_clearance.py)

For $h_L\le h\le h_U$, the central parallel speed $\sqrt{2(h-f)}$ is at least $1/368$. The arclength density $w=R f/B_\phi$ is at most $8h_U/7$. Each remaining collar extends from $a$ to an outward contact $r<325/64$ in its own signed coordinate. The outward slope of $f^2$ is greater than $1/400$. It bounds the reciprocal parallel speed by $21/\sqrt{r-t}$ in that collar. Integration shows that each collar contributes less than 20. In particular, a sharper bound on the central integral can be substituted directly into the following inequality for the same path and height. [Signed slope and first passage](dommaschk-mirror-height-band.md) · [Integral comparison](../../PlasmaLean/Design/DommaschkFullBandFlightBounds.lean)

$$
T(h)<40+\int_{-a}^{a}\frac{w(t)}{\sqrt{2(h-f(t))}}\,dt.
$$

## Replay

Start with the N-84 pre-mirror rows, the signed physical 325-slab receipt and the N-99 height-band passage receipt. All three stages authenticate their inputs. The row stage may use multiple workers on the workstation.

~~~bash
lake build PlasmaLean.Design.DommaschkFullBandFlightBounds
.venv-ws/bin/python scripts/dommaschk_kam/verify_core_clearance.py \
  --range 0 315 --workers 3 --output /tmp/plasma-core-clearance-316.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_submirror_prefix.py --core \
  --paired /tmp/plasma-signed-checkpoint-325.json --length 316 \
  --signs /tmp/plasma-core-clearance-316.json --output /tmp/plasma-core-submirror316-of325.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_full_band_flight.py \
  --core /tmp/plasma-core-submirror316-of325.json --passage /tmp/plasma-mirror-height-passage-325.json \
  --output /tmp/plasma-full-band-flight-325.json
~~~

For archive SHA-256 `203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d`, the signed core receipt is `65e7c6c08e7b87afbd5352b0de92cbefb002d62b86986d043ca01160f2573212`. The through-birth flight-time receipt is `93a23b4d823e85e24ac31cf4f814679888c11eda4acbc22c41ef80d947a5bfb2`. [Physical application builder](../../scripts/dommaschk_kam/verify_full_band_flight.py)
