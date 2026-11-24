# A shared guiding-centre time for a compact family of trapped births

For the phase-zero QA2R pilot at $u=47/100$, every admitted original launch has a certified field line with a compact central Cartesian arc parametrized by $-316/64\le t\le316/64$. Fix one such line, a species with $m>0$ and $q\ne0$, a positive displacement limit $d$, and any closed energy interval $0<e_0\le e\le e_1$. Subject to the interior support and pitch conditions below, **one positive local time** works simultaneously for the entire arc, every energy in the interval, every height in the full certified mirror band, and both signs of parallel velocity. One open set of physical births admits that time, including a positive-radius closed neighborhood of the complete lifted family in the five-dimensional birth space. [Actual position-height arc](compact-regular-birth-arcs.md) · [Physical compact-family theorem](../../PlasmaLean/Design/DommaschkCompactLittlejohnArc.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-150 |
| Title | A shared guiding-centre time for a compact family of trapped births |
| Kind | Theorem and physical application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-117, N-122, N-125, N-147 |
| Dependency requirement | Local control for the vacuum Littlejohn ODE, the actual pilot’s full regular birth arc, and compatible support, energy and pitch cuts. A positive fraction additionally uses a specified open-positive law with a measurable finite reference. |
| Produces | Compact-family local orbit control, a uniform birth-space neighborhood, and the two-sign physical application to a continuous interval of positions, energies and heights. |
| Status | Lean verified, including the original admitted pilot births on the same certified embedded tori. |
| Lean evidence | `VacuumLittlejohnWindow.exists_control_compact`, `FamilyControl.thickening`, `compact_guidingCentreBand`, `DommaschkCompactLittlejohnArc.of_path`, `Window.measured` and `DommaschkCompactBirthArc391_192_48_5_48_8_5_5.pilot`. |
| Audit evidence | The nine reusable API theorems and the physical application report only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Compactness and the actual five-dimensional equation

Let $K$ be a compact set of guiding-centre births $(x,v_\parallel,\mu)$. Every position lies in the regular vacuum domain, and $K$ lies in the interior of the intended reference $R$. For each $d>0$ there are $T,\varepsilon>0$ and an open set $W\subseteq R$ containing the closed $\varepsilon$-neighborhood of $K$. Every birth in $W$ admits an orbit for the full time $[0,T]$. Every solution on any initial subinterval $[0,s]$, $s\le T$, has displacement less than $d$ at its endpoint, a nonzero field, and a positive parallel denominator equal to the field norm. The radial distance to any fixed axis changes by less than $d$ as well. [Compact-family proof](../../PlasmaLean/Theory/Kinetic/VacuumLittlejohnCompact.lean) · [Physical ODE and orbit control](../../PlasmaLean/Theory/Kinetic/VacuumLittlejohnWindow.lean)

The local ODE result supplies one open controlled neighborhood and duration around each seed. The property passes to subsets. At a union of two controlled sets, their open neighborhoods can be united and the shorter positive time serves both. Compact induction now gives one time on the whole family. Compactness inside that open set yields the additional uniform metric radius. No velocity or time sampling enters the proof. The dynamics are the project’s contracted guiding-centre equation in a vacuum field, using the guiding-centre model associated with Littlejohn’s variational formulation. [Littlejohn, Journal of Plasma Physics 29 (1983)](https://doi.org/10.1017/S002237780000060X) · [Project model and local hypotheses](vacuum-local-littlejohn-births.md)

## Which physical births are covered?

Write $X$ for the Cartesian image of the pilot’s full closed central arc, and let $h_L\le h\le h_U$ be the archived mirror-height band. Over $X\times[e_0,e_1]\times[h_L,h_U]$, each signed lift is
$$
(x,e,h)\longmapsto\left(x,\ \pm\sqrt{2(e-(e/h)|B(x)|)/m},\ e/h\right).
$$
The height stays positive, and the actual field strength is continuous on $X$. Both images are compact. Near each seed, N-147 supplies compatible trapped births on its velocity sign. The two compact images can share one duration and one open set. [Parameter lifts](../../PlasmaLean/Theory/Contract/TrappedBirthCoordinates.lean) · [Previous two-sign neighborhood](common-local-littlejohn-time.md)

The support $S$ must contain both entire lifted images in its interior. The interior of the energy cut must contain the closed interval $[e_0,e_1]$, and $1/h$ must belong to the interior of the pitch cut for every $h$ in the closed height band. These strict interior conditions allow the certified open set to include perturbations at the endpoints. An unrestricted-cut fixture at $m=q=1$ and $1\le e\le2$ verifies that the assumptions have a concrete instance. The physical theorem quantifies over all positive masses and nonzero charges one species at a time.

For an open-positive law $\nu$, both $W\cap\{v_\parallel>0\}$ and $W\cap\{v_\parallel<0\}$ have positive measure. If the complete trapped reference is measurable and has finite mass, the certified fraction is its actual ratio $\nu(W)/\nu(R)>0$. The guiding-centre band contract also takes a nonempty compact axis. The proof supplies no numerical lower bound on either this fraction or $T$. The witnesses may depend on the chosen original trajectory, species, cuts, energy bounds and displacement limit. A prescribed thermal horizon, a numerical thermal fraction, dimensional scales, and bounce-averaged radial transport still require additional estimates. [Positive-measure contract](../../PlasmaLean/Theory/Contract/TrappedBirthBand.lean)

## Reproduction

Use the accepted N-147 pilot birth receipt. No field polynomial, slope, or trajectory enclosure needs to be recomputed.

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkCompactLittlejohnArc
.venv-ws/bin/python scripts/dommaschk_kam/verify_compact_littlejohn_arc.py \
  --regular-arcs /tmp/plasma-n147-regular-arcs-192.json \
  --output /tmp/plasma-n150-compact-pilot.json
```

The N-147 birth key is `01beaeb882865dda4a68b774808970dfdf44160ae51fee471d2475c28f968dec`. The final physical proof has key `a5069b5d29602cc286113b70b825df77952942db66d395c17272daa2c81812f0`. Checking and auditing its one module took 18.54 seconds on one worker with 20.93 GiB peak resident memory, including the full original pilot imports. [Certificate application](../../scripts/dommaschk_kam/verify_compact_littlejohn_arc.py)
