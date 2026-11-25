# A physical travel clock on the nonturning segment of each original birth

For every radius and phase in the original small QA2R launch rectangle, let \(y\) be its certified field line. Fix any \(h\) in the entire archived height interval. On the angular segment \([-59/32,59/32]\), the normalized signed time measured from the birth phase \(\phi\) is
\[
 t(\theta)=\int_\phi^\theta
 \frac{\lVert\gamma'_y(s)\rVert}{\sqrt{2(h-\lvert B(\gamma_y(s))\rvert)}}\,ds .
\]
Here \(\gamma_y\) is the Cartesian space curve. The integrand includes its actual Cartesian derivative. On this interval it is continuous and lies between \(1/2\) and \(15\). For any \(a\le b\) in the segment,
\[
 (b-a)/2\le t(b)-t(a)\le15(b-a).
\]
Thus the clock is continuous and strictly increasing. Every time between the two endpoint times has a unique angular position. In particular **every** original birth admits every signed time \(|\tau|\le966655/1048576\), approximately 0.921874, on this same segment. This common time holds for all radial labels, all admitted phases and every archived height. It describes the nonturning, normalized parallel mirror motion along the fixed field line. It supplies no physical scaling or estimate of cross-field guiding-centre drift. [Clock and bounds](../../PlasmaLean/Design/DommaschkRadialPassingTime.lean) · [Physical ODE and speed floor](radial-passing-speed-core.md)

The upper rate follows from the positive parallel-speed floor and a toroidal field bound for the Cartesian arclength density. The lower rate follows from positive cylindrical radius and the upper archived height. Additivity of the interval integral yields the elapsed-time bounds, and the intermediate value theorem and strict increase give existence and uniqueness of the position. The common time radius is \((59/32-2^{-19})/2\), allowing the birth phase to be at either edge of its admitted sector. [Original-birth composition](../../scripts/dommaschk_kam/verify_radial_passing_time.py)

## Replay

```sh
lake build PlasmaLean.Design.DommaschkRadialPassingTime
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_passing_time.py \
  --core /tmp/plasma-n191-core128.json --output /tmp/plasma-n194-physical128.json
```

The original-birth theorem `DommaschkRadialPassingTime128Core118.from_nested_tori` has key `2fa9f99694e99a51281401ead335e62424a2fab40104bc6888bcc7d38152220f` and uses only `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-194 |
| Kind | Quantified normalized parallel travel on a physically verified field line |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-191 and the Cartesian arclength and toroidal field bounds |
| Dependency requirement | True signed ODEs, a positive parallel-speed floor and the two archived height bounds. |
| Produces | A two-sided, strictly increasing physical travel clock with a uniform time interval and a unique angular position for every elapsed time. |
| Status | Unconditional Lean theorem on the indicated angular and height intervals. |
| Lean evidence | `DommaschkRadialPassingTime.duration`, `.clock_on`, `.times_about_birth` and the generated common-torus theorem. |
| Last updated | 25 November 2026 |
