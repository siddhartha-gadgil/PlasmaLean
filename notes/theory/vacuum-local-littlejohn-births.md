# Actual local Littlejohn orbits for both signs of the QA2R trapped population

For the QA2R pilot, Lean now proves that each of the two strictly signed trapped reference populations contains a nonempty open set of births with **genuine local guiding-centre solutions**. For every such birth $b=(x,v_\parallel,\mu)$ there are a time $T_b>0$ and a solution on the closed interval $[0,T_b]$ starting at $(x,v_\parallel)$ with magnetic moment $\mu$. The nonzero vacuum field and the strictly positive Littlejohn parallel denominator are certified throughout that interval. Both populations have positive five-dimensional Lebesgue volume; either population’s interior has positive mass for any birth law that charges every nonempty open set. [Ground theorem](../../scripts/dommaschk_kam/verify_local_littlejohn_births.py) · [Definition of the physical orbit](../../PlasmaLean/Theory/Contract/TrappedBirthBand.lean)

The species mass $m>0$, charge $q\ne0$ and attained energy $e>0$ are symbolic. As in N-117 the birth height $h$ can be anywhere in the closed pilot band. Its velocity and moment are the two exact lifts of a single original torus-interpolated birth, and its energy and pitch cuts contain $e$ and $1/h$ in their interiors. Additional support cuts may be imposed when their interiors contain the corresponding lift. The proof imposes no upper bound on $e$ for this local mathematical model. The size of the open sets, their numerical probability, a common application-scale time horizon, and radial drift over such a horizon remain open. Physical scales and target values are unspecified. [Five-dimensional reference populations, N-117](qa2r-trapped-birth-coordinates.md) · [Candidate local orbit contract](../../PlasmaLean/Design/DommaschkLocalLittlejohnBirth.lean)

## Why the effective parallel field stays positive

At a nonzero point of a differentiable, curl-free field $B$, the actual Fréchet-derivative curl product rule gives

$$
\nabla\times\widehat B
=\nabla(\|B\|^{-1})\times B .
$$

This vector is perpendicular to $B$. Consequently the Littlejohn effective field satisfies

$$
B^*_{\parallel}
=\widehat B\mathbin{\cdot}
  \left(B+\frac{mv_\parallel}{q}\nabla\times\widehat B\right)
=\|B\|>0 .
$$

The identity is pointwise and works for all parallel velocities. The generic Lean result uses the kernel’s vacuum-field contract on an open region and the bridge between its curl operator and the curl in the guiding-centre model. QA2R already satisfies this vacuum contract off the axis. The physical pilot and its neighboring seed points lie inside the nonvanishing part of that region. [Generic denominator identity](../../PlasmaLean/Theory/Kinetic/VacuumLittlejohnLocal.lean) · [Curl product rule](../../PlasmaLean/Theory/Fields/CurlProduct.lean) · [QA2R vacuum field](../../PlasmaLean/Design/DommaschkQA2R.lean)

The $C^2$ vacuum regularity makes the unit field, its curl and the gradient of the strength regular enough for the contracted Littlejohn velocity to be $C^1$ as a function of $(x,v_\parallel)$ at fixed $\mu$. Local ODE existence then gives a solution. Its continuity keeps it inside the open nonzero vacuum region for an initial positive closed interval, where the exact identity holds at every point. Intersecting this open spatial condition with the interior of the N-117 trapped reference preserves a neighborhood about each admitted signed pilot birth. This proves local dynamics in the actual position and velocity variables.

## Reproduction

Use the N-99 physical height-band passage `DommaschkRegularMirrorHeightBand325`, content key `9c00a57de9e2b1b2cc49b184ca9862539bc1c68c69f74d7c45fefcf531bb9809`.

```bash
lake build PlasmaLean.Design.DommaschkLocalLittlejohnBirth
.venv-ws/bin/python scripts/dommaschk_kam/verify_local_littlejohn_births.py \
  --passage /tmp/plasma-mirror-height-passage-325.json \
  --output /tmp/plasma-local-gc-populations325.json
```

The three ground declarations passed two separate kernel builds with content key `652152df93d1b02d8c01e16260815a496934b9d4d0c9c20e1bb91ed515865a8c`. The first assembly took 6.535 seconds with peak resident memory of 7,841,920 KiB. Its theorem audits reported `propext`, `Classical.choice` and `Quot.sound`.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-122 |
| Title | Actual local Littlejohn orbits for both signs of the QA2R trapped population |
| Kind | Vacuum guiding-centre theorem and physical ground certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-99, N-112, N-114, N-117 |
| Dependency requirement | Nonzero $C^2$ vacuum field on the launch region, the exact Hamiltonian and Littlejohn right-hand side, both signed pilot lifts in the trapped-reference interior, and local existence for a $C^1$ vector field. |
| Produces | The exact positive effective parallel field for all velocities and actual local guiding-centre trajectories on positive-mass open sets of the physical five-dimensional trapped reference. |
| Difficulty | Relate both curl conventions to cancel the effective correction, establish regularity of the actual right-hand side and retain nonzero denominators on the entire closed local interval. |
| Status | Compiled Lean theorem with independently reproduced ground assembly. |
| Lean evidence | `VacuumLittlejohnLocal.parallel_eq_norm`, `.vacuum_parallel`, `.velocity_smooth`, `.exists_orbit`, `DommaschkLocalLittlejohn325.from_birth`, `.positive_mass`, `.positive_volume`. |
| Last updated | 25 November 2026 |
