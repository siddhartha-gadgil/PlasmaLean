# A common guiding-centre time across all pilot launch phases and central arcs

At radial label $u=47/100$, one pair of embedded nested QA2R tori supports every original launch angle $|φ_0|≤2^{-19}$. Choose a genuine signed field line through each launch. There is a choice of these lines such that **all their central arcs share one positive time** for local guiding-centre control. The time also serves both signs of parallel velocity, the whole archived mirror-height band, and any fixed closed positive energy interval simultaneously. The central arc of each line covers the absolute azimuths $-316/64≤t≤316/64$. The physical proof retains the original birth condition, both signed exits, and all 391 ODE slabs in each direction for each selected line. [Physical theorem](../../scripts/dommaschk_kam/templates/compact_every_launch_arc.lean.tpl) · [Previous per-launch result](compact-littlejohn-arc.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-154 |
| Title | A common guiding-centre time across all pilot launch phases and central arcs |
| Kind | Theorem and physical application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-106, N-147, N-150 |
| Dependency requirement | The physical regular pilot birth arcs, the certified regular cylindrical enclosure, and interior support, energy and pitch cuts. |
| Produces | One control time across the union of every selected central arc, and a uniform five-dimensional birth-space radius for the compact collection of original launches. |
| Status | Lean verified on the physical pilot at every admitted original phase. |
| Lean evidence | `VacuumLittlejohnWindow.common_enclosure_time`, `DommaschkCompactLaunchPhases.uniform_launches`, `DommaschkEnclosedLaunchArcs.uniform_enclosed`, and the two original-birth applications below. |
| Audit evidence | Eight reusable declarations and both generated physical declarations use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Order of the witnesses

Choose the two original tori and the family of field lines first. Fix a species with $m>0$ and $q≠0$, an energy interval $0<e_0≤e_1$, and any excursion limit $d>0$. There is a duration $T>0$ that works before any of the permitted support, energy or pitch cuts are chosen. Let $X$ be the union of the central Cartesian arcs. For every $x∈X$, $e∈[e_0,e_1]$, $h∈[h_L,h_U]$ and either sign, the intended support must contain the physical birth
$$
(x, v_∥, μ)=\left(x,\;±\sqrt{2(e-(e/h)|B(x)|)/m},\; e/h\right)
$$
in its interior. The interior of the energy cut contains $[e_0,e_1]$, and the pitch cut contains every $1/h$ in its interior. Under these conditions one open $W$ inside the trapped reference contains all those births. Each initial state in $W$ has a guiding-centre orbit up to $T$. Every solution on each initial subinterval through that time has displacement strictly less than $d$, a nonzero field, and a positive parallel denominator equal to the field norm. Each strict parallel-velocity sign has a nonempty open part of $W$. With an open-positive law and a measurable finite reference, the controlled fraction is the positive ratio of the measure of $W$ to the reference measure. The guiding-centre band contract also assumes a nonempty compact axis. [Precise window and measure theorem](../../PlasmaLean/Design/DommaschkCompactLittlejohnArc.lean)

## Why one time covers the whole union

The two torus embeddings make the original birth position a continuous function of $φ_0$. Its image of the closed phase interval is compact. Together with the closed energy-height rectangle and both signs, the original launches therefore admit a single positive metric radius in birth space inside a controlled open set. [Launch map and compactness](../../PlasmaLean/Design/DommaschkCompactLaunchPhases.lean)

The arc proof uses a different compact set. The archived ODE tubes enclose every point of each central arc in the Cartesian image of $7/8≤R≤1$, $|z|≤5/64$, $|t|≤316/64$. This entire enclosure is compact and stays in the regular vacuum domain by the strict toroidal field bound. Every lifted seed has $|v_∥|≤\sqrt{2e_1/m}$ and $0≤μ≤e_1/h_L$. The product of the spatial enclosure with these closed velocity and moment intervals is a compact set of regular initial states. The local vacuum ODE theorem gives one controlled duration on a neighborhood of that product. Intersect that neighborhood with the interior of the chosen trapped reference. The resulting open set contains the full union of lifted arcs by the individual birth theorems. This argument covers the selected family without requiring joint continuity in the parameters $(φ_0,t)$. A uniform perturbation radius for the full union would require a further argument controlling its distance from the boundary of the cuts. [Compact-enclosure theorem](../../PlasmaLean/Theory/Kinetic/VacuumLittlejohnEnvelope.lean) · [Physical enclosure and sign lifts](../../PlasmaLean/Design/DommaschkEnclosedLaunchArcs.lean)

The duration and fraction are existential. A numerical operating time, dimensional excursion cap, and prescribed thermal fraction remain open targets. The certified $391/64$ angular path length on each side and the local guiding-centre time use different parameters.

## Reproduction

Use the accepted N-147 original-birth receipt and one Lean worker.

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkEnclosedLaunchArcs
.venv-ws/bin/python scripts/dommaschk_kam/verify_uniform_launch_phases.py \
  --regular-arcs /tmp/plasma-n147-regular-arcs-192.json \
  --all-arcs --output /tmp/plasma-uniform-all-launch-arcs.json
```

| Kernel proof | Key | Wall time | Peak resident memory |
| --- | --- | ---: | ---: |
| N-147 original regular pilot births | `01beaeb882865dda4a68b774808970dfdf44160ae51fee471d2475c28f968dec` | | |
| All compact original phases, `original_phases` | `287f9c25abb6fd37fae9c0c43ce7940f45c08a6ea298574aa02a160598fc01b1` | 19.60 s | 20.91 GiB |
| All central arcs for every launch, `every_arc` | `335c33e08e07b619d863ae79f29bfbd5c6e76471f47a894c74c158abbd968d21` | 19.92 s | 20.93 GiB |

The import receipt records the exact common torus and regularity proofs. The replay introduces no new field enclosures. [Physical replay driver](../../scripts/dommaschk_kam/verify_uniform_launch_phases.py)
