# A prescribed first-well action or a grazing first mirror

Consider a connected parameter space $P$. Each parameter specifies a continuous field-strength profile $f_p(t)$ and arclength density $w_p(t)$ for $-b\le t\le b$. Both quantities are jointly continuous in parameter and time. The mirror height $h(p)$ is continuous. At every parameter assume $f_p(0)<h(p)$ and $h(p)<f_p(-b),f_p(b)$. Let $(l_p,r_p)$ be the component containing zero of the open sublevel set $f_p<h(p)$. Its endpoints are the first mirrors. Define the single-passage action by

$$
J(p)=\int_{l_p}^{r_p} w_p(t)\sqrt{2\big(h(p)-f_p(t)\big)}\,dt .
$$

**Theorem.** If $J(x)<j<J(y)$ for two parameters $x,y$, at least one of the following holds.

1. Some parameter has first-well action exactly $j$.
2. At some parameter, one of the two first mirrors is a local maximum of the field strength. A differentiable profile has zero outward derivative there.

The alternatives may both hold. The theorem places no restrictions on later mirror points or accessible pockets beyond either first contact. The ordinary endpoint signs suffice to construct the earliest contact on each clock. [Formal statement and proof](../../PlasmaLean/Theory/Kinetic/FirstWellContinuation.lean)

## Why the first mirror can be followed

Fix a parameter and a first mirror at outward time $\tau$. Any compact interval from the birth to a time strictly before $\tau$ stays strictly below the height. Joint continuity keeps that whole interval accessible at nearby parameters. If there are superlevel points arbitrarily close beyond $\tau$, any one of them stays superlevel at nearby parameters, putting an upper limit on the first-contact time. Together the two bounds give continuity at the chosen parameter. A positive outward derivative at the first mirror supplies the required superlevel points. An outward crossing can also have zero derivative.

If arbitrarily close superlevel points are absent, the field stays at most at the mirror height for an interval to the right of the contact. The first-contact property already gives a strict inequality on its left. This makes the contact a local maximum. When both first contacts cross outward everywhere, integrate the continuous clipped density up to the two continuous endpoint times and apply the intermediate value theorem. This argument only follows the component containing the birth. A merging-well example in Lean exhibits a jump in precisely that component’s action. [Verified example](../../PlasmaLean/Theory/Kinetic/MirrorActionEnvelope.lean)

## Application to the QA2R radial interval

At the upper archived height, the two original phase-zero births at $u=0.470$ and $u=0.478$ bracket the action target $j=6799610938322487/5000000000000000$. Lean has attached the theorem to the specific two field lines on the original nested embedded tori, for every allowed $|\phi_0|\le2^{-19}$. For any interpolating family agreeing with those endpoint lines and satisfying the continuous profile, density and cap hypotheses, either some **strictly intermediate** $u$ has action $j$, or a first mirror in the interval is a local maximum. For a physical application, the interpolating trajectories must come from the actual ODE and original births. The two endpoint actions alone leave this family to be supplied. Excluding a grazing first mirror on those lines suffices to obtain the prescribed action. [Physical alternative](../../PlasmaLean/Design/DommaschkRadialActionAlternative.lean) · [Actual endpoint actions](upper-height-radial-action-secant.md)

The generated declaration `DommaschkRadialActionAlternativeOn391_328_48_16_48_16_8_5.from_common_tori` has key `c5bb13c6cc215e4d00c0e6b12e0ec241df895f83c39098fdbb1394784ea7b1f6`. Its only external proof input is the checked upper-height secant on the same two lines. [Replay script](../../scripts/dommaschk_kam/verify_radial_action_alternative.py)

~~~bash
lake build PlasmaLean.Design.DommaschkRadialActionAlternative
.venv-ws/bin/python scripts/dommaschk_kam/verify_radial_action_alternative.py \
  --top /tmp/plasma-n162-upper-secants.json --output /tmp/plasma-n167-radial-alternative.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-167 |
| Kind | Candidate-independent first-well continuation theorem and conditional physical application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-69, N-144, N-159, N-162 |
| Dependency requirement | Joint continuity on a through-going capped family, with a strict action inequality on each of two original endpoint wells |
| Produces | Continuity at crossing first mirrors and a prescribed-action or local-maximum alternative |
| Status | Generic theorem proved. Physical endpoint inputs discharged. The continuous family with caps at every intervening QA2R label is an application hypothesis. |
| Lean evidence | `FirstWellContinuation.CappedFamily.target_or_localMax`, `FirstWellContinuation.continuousAt_time`, `FirstWellContinuation.action_split` and `DommaschkRadialActionAlternative.of_endpoint_wells` |
| Audit evidence | The generic and concrete declarations use only propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |
