# A common mirror-height interval on the four radial birth ribbons

For every joined QA2R trajectory following one of the four original radial tube sequences through the two caps, the two first mirrors persist on the closed interval
\[
 H=[h_U-1/50000,\ h_U+1/30000],\qquad
 h_U=5300546391395933/5000000000000000.
\]
The interval has width \(1/18750\). The same curve and the same pair of inverse functions work for all its heights. Every birth phase with \(|\phi|\le2^{-19}\) lies strictly between these first contacts. For the normalized, arclength-weighted mirror-to-mirror flight, \(14<T<10000\) at every height, including both endpoints. [Analytic and physical proof](../../PlasmaLean/Design/DommaschkRadialMirrorHeightBand.lean) · [Original one-height result](radial-ribbon-through-cap-signs.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-186 |
| Kind | Quantitative height persistence of physical first mirrors |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-106, N-169, N-172, N-175, N-179 and N-181 |
| Input | A single enclosed solution tracking the first 332 forward and backward rows of a canonical tile, or the corresponding through theorem for every initial position in each of the four seed balls. |
| Produces | Two strictly increasing outward mirror-time functions, unique first contacts and signed derivatives at every height, a uniform angular Lipschitz bound, and a uniform bound on the normalized one-way flight time. |
| Status | All incoming, collar and cap implications have passed the kernel. The rectangle-level birth statement takes the common full ODE trajectory certificate as its remaining input. |
| Lean evidence | `DommaschkRadialRibbonMirrorBand.on_tubes`, `from_entry`, `from_nested_tori`, and `DommaschkRadialMirrorHeightBand.Verified`. |
| Audit evidence | The finite proof packages and the combined theorem use `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Numerical margins

The 16 incoming harmonic groups cover rows 0–316 on both clocks for all four tiles, giving 2,536 physical row bounds. Each original bound \(g\le G<0\) is on \(g=R^{16}(|B|^2-h_U^2)\). If the group supplies \(R\le r\), the exact check for a lower test height \(k\) is \(G+r^{16}(h_U^2-k^2)<0\). This certifies the stronger field ceiling \(k=h_U-1/48000\). The limiting group covers rows 307–316 and has \(r=57/64\). Its original bound fails the more demanding test at drop \(1/40000\). The retained clearance below the bottom of \(H\) is \(1/1200000\). [Physical group transfer](../../PlasmaLean/Design/DommaschkGroupGapRadius.lean) · [Exact arithmetic producer and original-row attachment](../../scripts/dommaschk_kam/verify_radial_ribbon_height_band.py)

All eight exterior caps independently pass at \(h_U+1/30000\). The proof rebuilds the endpoint gap at that height using the archived row-330 output enclosure and the three physical field polynomials. The fourth tile fails the same enclosure test at rise \(1/20000\). These failures describe the resolution of the certificates. The lower archive height \(h_L\) is outside \(H\). [Original cap calculation](../../scripts/dommaschk_kam/verify_radial_ribbon_caps.py)

## First mirrors and flight

On each outward clock the previously certified 112 signed collar rows give \(d|B|^2/dt>1/16384\) throughout \((317/64,331/64)\), including the joins. At every \(h\in H\) both first contacts are strictly within this collar. Their outward elapsed angles \(t_\pm(h)\) obey
\[
 |t_\pm(h)-t_\pm(j)|\le 34740\,|h-j|.
\]
The signed field slope is strictly below \(-1/(32768h)\) at the left mirror and strictly above \(1/(32768h)\) at the right. Each intermediate interpolated birth, for radial parameter \(47/100\le u\le239/500\), is identified with its own absolute-phase point on the line using the original approach to its section seed. The choices of the two nested embedded invariant tori precede the choices of radius and phase. [Inverse-branch theorem](../../PlasmaLean/Theory/Kinetic/MirrorHeightBand.lean) · [Birth identification](../../PlasmaLean/Design/DommaschkRadialSectionAction.lean)

With \(f=|B|\), the time integrand is \(w/\sqrt{2(h-f)}\), where \(w\) is the norm of the true Cartesian path derivative. In the well, \(w\le (8/7)h<5/4\). On the incoming core, \(1/\sqrt{2(h-f)}\le775\). On either outward collar the integrand is bounded by \(165/\sqrt{t_\pm-t}\). This integrable estimate and the collar width \(14/64\) give a time below 5,000 on each side. For the lower bound, \(w\ge7/8\) while the parallel speed is at most \(61/100\). The certified time is in the normalized dynamics. An interpretation in seconds would require physical scales. [Toroidal field and density bounds](../../PlasmaLean/Design/DommaschkToroidalFieldBounds.lean) · [Flight integrals with simple endpoints](../../PlasmaLean/Theory/Kinetic/MirrorBounceTime.lean)

## Action implications

At \(h_U\) the certified inner action is at least 0.00213 below the prescribed target and the outer action at least 0.00191 above it. A sufficiently small common height interval therefore preserves both inequalities once one uses the clipped fixed-window action continuity on the two endpoint lines. For example, the pointwise square-root estimate gives an action modulus \((662/64)(5/4)\sqrt{2|h-h_U|}\): the integrands can differ only where at least one level is accessible, where the density has the indicated bound. At \(|h-h_U|\le 2^{-28}\) this is less than 0.00112. This calculation identifies a narrower sufficient window for a subsequent endpoint-action theorem. The certificate here covers mirrors and flight throughout \(H\). [Two original action enclosures](upper-height-radial-action-secant.md) · [Clipped fixed-window action](../../PlasmaLean/Theory/Kinetic/MirrorHeightAction.lean)

## Reproduction

The original packet digest is `c4f65ab5d7727fc5fdbae645c6924ecde6b474f521663a8b1b9de6be8d45a486`. Replay the N-169, N-172 and N-181 inputs first, then run the driver below. Each worker runs one Lean process. The driver authenticates the old source and object files, reuses the original field models, checks each row's time and spatial enclosure, and verifies the aggregate theorem's axioms.

```bash
lake build PlasmaLean.Design.DommaschkRadialMirrorHeightBand
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_radial_ribbon_height_band.py \
  --ribbon /tmp/plasma-n169-four-ribbons.json --incoming /tmp/plasma-n172-incoming.json \
  --caps /tmp/plasma-n169-caps.json --packets /tmp/plasma-n169-packets.json \
  --orientation /tmp/plasma-n181-through-cap.json --workers 2 \
  --output /tmp/plasma-n186-height-band.json
```

The N-181 orientation family has key `94d766bf455298a2ad003c9809cc650a50503608d2663a9ce355876ec81f4f16`. The final N-186 key is `a4b9d0cde92051b9905b4adbfd7d9b91f5a33721ecec3eeaf7eb90307d987968`.
