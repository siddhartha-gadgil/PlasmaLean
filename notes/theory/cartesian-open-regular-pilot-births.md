# Positive Cartesian position–height volume for QA2R regular mirror births

Fix the certified QA2R field $B$. Let $\mathcal R$ be the pairs $(x,h)\in\mathbb R^3\times\mathbb R$ for which the oriented unit-speed field line through $x$ has a regular mirror on each side at strength $h$. The physical contract requires strict sublevel strength inside the well and a nonzero, outward-directed strength derivative at each turning point. [Arclength birth contract](../../PlasmaLean/Theory/Contract/TrappedBirthBand.lean)

**Lean proves that every admitted original pilot birth at every height in the closed pilot band belongs to the four-dimensional interior of $\mathcal R$.** The nested Q-16 tori are common to all $|\phi|\leq 2^{-19}$. The physical position is their interpolated birth at $u=47/100$ and its original geometric angle $\phi$. The height ranges over

$$
\left[\frac{5297961656084411}{5000000000000000},
       \frac{5300546391395933}{5000000000000000}\right].
$$

In particular $\operatorname{vol}_4(\mathcal R)>0$. Any measure on Cartesian position and height that charges every nonempty open set assigns strictly positive mass to $\operatorname{int}\mathcal R$. A neighborhood exists even at either endpoint height, allowing small simultaneous perturbations of the three Cartesian coordinates and height. The result gives no numerical radius or mass fraction. Applying it to a thermal law requires a connection between that law’s velocity and magnetic-moment variables and the height. Long-time guiding-centre transport also remains open. [Ground theorem and replay](../../scripts/dommaschk_kam/verify_cartesian_mirror_births.py) · [Earlier angle–height area bound](open-mirror-wells-and-birth-area.md)

## A Cartesian ODE for the geometric-angle clock

Write $R^2=x_0^2+x_1^2$ and $A=x_0B_1-x_1B_0$. On the open set $U=\{R^2>0,\ A>0\}$ the autonomous velocity, physical speed and observable are

$$
V(x)=\frac{R^2}{A}B(x),\qquad v(x)=\frac{R^2}{A}\|B(x)\|,\qquad F(x)=\|B(x)\|.
$$

The physical QA2R field is smooth enough off the axis and $A>0$ excludes field nulls. Thus $V$ and $F$ are $C^1$ on $U$, $v$ is positive and continuous, and $V=v\widehat B$. In cylindrical coordinates $A=R B_\phi$. Positivity of the previously certified denominator puts the physical pilot in $U$. If $y(t)=(R(t),z(t))$ solves the original two-coordinate angular ODE, its Cartesian lift $X(t)=(R(t)\cos t,R(t)\sin t,z(t))$ satisfies $X'=V(X)$ there. The construction works at all azimuths, including a crossing of any chosen angular branch cut. [Cartesian velocity and physical ODE](../../PlasmaLean/Design/DommaschkCartesianAngleFlow.lean) · [QA2R field regularity](../../PlasmaLean/Design/DommaschkQA2R.lean)

## From one well to a neighborhood

The two branches from N-99 give the unique first outward root of $F=h$ in $(316/64,325/64)$, the strict signs before and after each root, and positive outward derivatives. On each side take the cap halfway from the root to $325/64$. Both caps have strength strictly above the height and lie strictly inside the checked ODE interval. The original birth angle lies between the roots. At every contact on the negative side the derivative with respect to signed angle is strictly negative, and on the positive side it is strictly positive. These facts supply a physical bracket at the original birth angle for the Cartesian flow $V$. The N-112 local persistence theorem then gives an open position–height neighborhood consisting of regular arclength births. [Height band, N-99](dommaschk-mirror-height-band.md) · [Cartesian bracket proof](../../PlasmaLean/Design/DommaschkCartesianMirrorBirth.lean) · [Local flow persistence, N-112](local-flow-persistence-of-physical-births.md)

## Reproduction

Use the N-99 through-birth height-band report. Its module is `DommaschkRegularMirrorHeightBand325` and its checked content key is `9c00a57de9e2b1b2cc49b184ca9862539bc1c68c69f74d7c45fefcf531bb9809`.

```bash
lake build PlasmaLean.Design.DommaschkCartesianMirrorBirth
.venv-ws/bin/python scripts/dommaschk_kam/verify_cartesian_mirror_births.py \
  --passage /tmp/plasma-mirror-height-passage-325.json \
  --output /tmp/plasma-cartesian-first-mirror-births.json
```

The final four theorems compiled in two separate output directories with key `e3b0d295e97dc98aaa91d93b1f26bb8d926b2c1152e2dda5e458d03b1df10fb9`. The first composition took 5.321 seconds and peaked at 7,839,872 KiB RSS. The three axioms reported for each declaration were `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-114 |
| Title | Positive Cartesian position–height volume for QA2R regular mirror births |
| Kind | Physical theorem and ground application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-95, N-97, N-99, N-100, N-112 |
| Dependency requirement | QA2R vacuum regularity, positive azimuthal denominator throughout the signed pilot tube, original physical births, first roots with sign and derivative control across the closed band, local flow persistence. |
| Produces | Every pilot birth at the admitted angles and heights belongs to the ambient interior of the regular mirror births. That interior has positive mass for any open-positive law on Cartesian position and height. |
| Difficulty | Transfer the signed-angle pilot to a smooth autonomous Cartesian velocity, preserve the original birth point, and place strict caps and derivatives on both sides of it. |
| Status | Compiled Lean theorem and independently reproduced ground certificate. |
| Lean evidence | `DommaschkCartesianAngleFlow.cartesian_ode`, `DommaschkCartesianMirrorBirth.flow_bracket`, `.neighborhood`, `DommaschkCartesianMirrorBirth325.from_birth`, `.nonempty_interior`, `.positive_mass`, `.positive_volume`. |
| Last updated | 25 November 2026 |
