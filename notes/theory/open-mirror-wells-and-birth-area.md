# Persistence of mirror wells and the area of certified births

## A transverse well persists in a family

Let $P$ be a topological parameter space, let $a<c<b$, and let $F(p,t)$ be the field strength on a trace. Assume that $F$ and its time derivative are jointly continuous on $P\times[a,b]$. A pair $(p,h)$ passes the following test.

- The two caps have strength strictly above $h$, and the launch at $c$ has strength strictly below $h$.
- At every contact with $h$ on $[a,c]$ the time derivative is negative. At every contact on $[c,b]$ it is positive.

**The passing pairs form an open subset of $P\times\mathbb R$.** Each pair supplies two first turning points enclosing the launch. A single passing pair therefore yields a positive-measure set for any measure that assigns positive mass to nonempty open sets. The time derivative may vanish at the bottom of the well. [Openness and measure theorems](../../PlasmaLean/Theory/Kinetic/MirrorWellPersistence.lean)

For the proof, consider the triples $(p,h,t)$ where the profile equals $h$ and the derivative has the wrong sign or is zero. On each half of the time interval this is a closed set. Projecting away the time coordinate preserves closedness because the half-interval is compact. The strict cap and launch inequalities are open as well. The first-contact theorem then identifies the two endpoints of the well. [First-contact theorem](../../PlasmaLean/Theory/Kinetic/MirrorWellCriterion.lean)

The height may itself be a continuous function $H(p)$ of the birth data. Pull back the open set along $p\mapsto(p,H(p))$. If the traces follow the oriented field with positive continuous speed, every parameter in this neighborhood gives a regular mirror birth in physical arclength. This gives a way to prove positive mass in a full birth chart once the family of physical field lines, its joint regularity, and one transverse bracket have been supplied. It gives no numerical size for that neighborhood. [Physical arclength corollary](../../PlasmaLean/Theory/Kinetic/MirrorWellPersistence.lean)

The translated parabola $F(p,t)=t^2+p$, with caps at $-1,1$ and launch at zero, passes exactly for $p<h<p+1$. Uniform strength errors alone give no corresponding persistence of the derivative signs. For $\varepsilon>0$, the smooth profile $g(t)=t^2-2\varepsilon\sin((t-1/2)/\varepsilon)$ differs from $t^2$ by at most $2\varepsilon$. At height $1/4$ it still passes through $t=1/2$, but its derivative there is $-1$. Lean checks the classification and the counterexample. [Formal examples](../../PlasmaLean/Theory/Kinetic/MirrorWellPersistence.lean)

## An explicit area at the QA2R launch

Fix the interpolated launch with radial label $u=47/100$ and poloidal launch parameter zero on the nested Q-16 tori. Use toroidal angle $\phi$ and mirror height $h$ as independent coordinates, with product Lebesgue measure. N-99 supplies one physical trace for each admitted angle, on the same pair of tori, before $h$ is chosen. The entire closed rectangle

$$
[-2^{-19},2^{-19}]\times
\left[\frac{5297961656084411}{5000000000000000},
      \frac{5300546391395933}{5000000000000000}\right]
$$

lies in the set of regular mirror births at the actual interpolated Cartesian positions. Its area is exactly

$$
\frac{1292367655761}{655360000000000000000}
\;\simeq\;1.9719965450\times10^{-9}.
$$

This is an explicit lower bound on the Lebesgue measure of the regular angle-height pairs in that two-dimensional parameterization. The proof multiplies the interval lengths and transfers the regular-birth predicate to the original launch position. A thermal birth fraction requires a birth law with radial, spatial and velocity variables and control of the corresponding measure. A radial-drift or confinement-time bound requires dynamical information after the mirror passage. [Area theorem](../../PlasmaLean/Design/DommaschkMirrorBirthArea.lean)

## Reproduce the pilot area

The inputs are the nine closed-slab proofs and the first contacts from N-99. The last step checks the area claim on the same nested tori.

```bash
lake build PlasmaLean.Design.DommaschkMirrorBirthArea
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/dommaschk_kam/verify_mirror_height_band.py \
  --slopes /tmp/plasma-band-mirror-slope{316..324}.json \
  --first-contacts /tmp/plasma-first-contacts-325.json \
  --output /tmp/plasma-mirror-height-band-325.json \
  --passage-output /tmp/plasma-mirror-height-passage-325.json \
  --area-output /tmp/plasma-mirror-birth-area-325.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-100 |
| Title | Persistence of mirror wells and the area of certified births |
| Kind | Theorem and physical certificate |
| Addresses | G-6, G-10, Q-1, Q-16, Q-35 |
| Depends on | N-95, N-97, N-99 |
| Dependency requirement | An oriented regular field-line chart for the abstract arclength conclusion. The common nested tori, original birth identification and all-height passage for the explicit pilot rectangle. |
| Produces | An open parameter-height criterion, a positive-measure criterion for a physical chart, a counterexample for uniform strength error alone, and an exact pilot angle-height area bound. |
| Difficulty | Contacts move and need derivative control on a compact bracket. A lower-dimensional area does not give a thermal birth fraction. |
| Status | Verified in the generic family and at the actual torus-interpolated pilot births. |
| Lean evidence | `MirrorWellPersistence.isOpen_bracket`, `regular_birth_measure_pos`, `uniform_profile_error_counterexample`, `DommaschkMirrorBirthArea.rectangle_area`, `of_passage`, `DommaschkRegularBirthArea325.from_birth`. |
| Audit evidence | Ground kernel key `604f00ac7c76251568e226e700b73726c11715f592daddfef1d2eca5b000f48a`. Axioms are `propext`, `Classical.choice`, and `Quot.sound`. |
| Next action | Certify transverse wells on a chart varying the spatial and velocity labels, with a specified birth distribution. |
| Last updated | 25 November 2026 |
