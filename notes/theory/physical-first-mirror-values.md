# First-mirror height measure on physical QA2R field lines

At the phase-zero radius $u=239/500$, every admitted original launch angle $|φ_0|≤2^{-19}$ has a true signed field line with an earliest mirror in each direction at every $h∈[h_L,h_U]$. Almost every such height has positive outward derivative of field strength at both first contacts. The heights at which **both outward derivatives exceed $1/1250$** have Lebesgue measure at least $667367655761/2500000000000000$. This is at least 51.639% of the archived height band for uniformly sampled height on each fixed line. Both first-mirror clocks lie in $(317/64,327/64)$. The proof uses strict incoming signs and two high exterior caps on the original 328-pair path, together with the smooth vacuum field. [Physical theorem and source identification](../../PlasmaLean/Design/DommaschkPhysicalFirstMirrorValues.lean) · [Area formula and first-contact maps](first-mirrors-regular-values.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-164 |
| Title | First-mirror height measure on physical QA2R field lines |
| Kind | Physical application of the one-dimensional area formula |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-106, N-127, N-153, N-155, N-159 |
| Dependency requirement | A signed angular passage through the exterior caps, a strict incoming field bound on both sides and the regular spatial enclosure. The area estimate uses the physical ODE and positive toroidal field throughout the bracket. |
| Produces | Earliest mirrors for every band height, transverse first contacts at almost every height, and a quantitative Lebesgue measure of heights with two outward derivatives above a chosen threshold. |
| Status | Kernel verified at the original phase-zero outer birth. All four opposite-section area implications are kernel verified against their complete ordered incoming and exterior signs. Each requires its physical ODE passage to reach the exterior caps. |
| Lean evidence | `DommaschkPhysicalFirstMirrorValues.vector_differentiableOn`, `original_position`, `on_signed`, `from_passage` and `DommaschkFirstMirrorAreaQ0R478On391_328_48_16_48_16_8_5.from_common_tori`. |
| Audit evidence | The reusable laws and checked physical applications use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Signed clocks and the genuine birth

Let $α$ be the central section angle, including $α=π/2$. The physical path $y(t)=(R(t),z(t))$ uses signed elapsed azimuth $t$. The strength on its two outward clocks is
$$
f_+(s)=\lVert B(R(s),α+s,z(s))\rVert,\qquad
f_-(s)=\lVert B(R(-s),α-s,z(-s))\rVert.
$$
These are norms of the actual Cartesian field at the indicated cylindrical positions. The joined passage includes a short physical approach from the original torus interpolation at $φ_0$ to the central section. Uniqueness of the spatial ODE on the neighborhood covered by the first two tubes identifies the interpolation exactly with $y(φ_0-α)$. The proof retains this equality, the signed ODE, its two endpoint enclosures and every visited physical tube. The two functions of height record first contacts of this one trajectory.

Positive radius puts the Cartesian field inside the smooth vacuum domain. The cylindrical-to-Cartesian map is differentiable as a function of radius, true azimuth and vertical position. Composing that map and the field with the signed ODE supplies differentiability of the field vector on the bracket. The checked spatial envelope $7/8≤R≤1$, $|z|≤5/64$ gives $B_φ>7/8$ at every azimuth. Its norm is therefore differentiable there as well. The proof uses no sampled or certified field-strength slopes on these intervals. [Global toroidal-field estimate](../../PlasmaLean/Design/DommaschkToroidalFieldBounds.lean)

## What the area measures

For a fixed path, first-contact times increase strictly with height. A height having a shallow first contact is in the image of the part of the bracket where the absolute derivative is small. The one-dimensional area formula bounds the measure removed by a slope threshold $m$ times the sum of the two bracket widths. Here both widths are at most $10/64$, so the loss at $m=1/1250$ is at most $1/4000$.

The exceptional height set can depend on the field line. The argument proves an almost-everywhere statement for each individual launch, while the existence of first contacts holds at every height. The measured quantity is uniform height on the specified band. A thermal birth law on physical phase space would need its own transformation and support assumptions.

## Opposite section

The archived bounds use the absolute phases $π/2+s$ and $π/2-s$ separately. Each row number in the table is an angular count of sixty-fourths, and the two clocks at a given radius have the same numerical bracket.

| Label | Strict incoming bound through | High exterior cap at | Slabs in each bracket |
| --- | ---: | ---: | ---: |
| 0.456 | 320 | 328 | 8 |
| 0.464 | 321 | 329 | 8 |
| 0.509 | 326 | 335 | 9 |
| 0.517 | 326 | 336 | 10 |

All 2,656 signed position tubes up to these four exterior caps fit the regular spatial envelope. The exterior signs use the actual upper-height endpoint certificates at N-153. The earlier field-strength bounds come from the complete lower-height tube covers at N-155. At each opposite radius the remaining physical input is an ODE trajectory through the required exterior cap on both clocks. Its rows must agree with the original archived rows on each initial segment. Shorter physically certified opposite-section passages provide no crossing claim at these later times. [Physical cap and cover binding](../../scripts/dommaschk_kam/verify_physical_first_mirror_values.py)

## Reproduction

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_first_mirror_values.py \
  --endpoint q0r478 --caps /tmp/plasma-q0r478-mirror-caps.json \
  --incoming /tmp/plasma-q0r478-grouped-exclusion.json \
  --calibrated /tmp/plasma-calibrated-at-328.json --output /tmp/plasma-physical-area-q0r478.json
```

The actual phase-zero first-mirror height theorem has key `4b60374e0e0a83091f709b2585f482dc49c6f8a327c89f30fc7fef77e9a0c632`. Its two signed field-row certificates have keys `48b19b99346e51295d61e88895a8bf7cda815ce599c20ed6cb127aa8b9b3aad3` and `4a8b7ae9ff8a0a2d767f1b4f322cc21583ae4d205f4c8d5a11b911af950217ea`. Its passage implication has key `5c5b2495ec84e102954149a9d5bda04baef43a5bdbf88de4b8155f286056e989`. The final binding and axiom audit used one worker for 20.34 seconds, with 23.74 GiB peak resident memory.

```sh
for endpoint in q1r456 q1r464 q1r509 q1r517
do
  .venv-ws/bin/python scripts/dommaschk_kam/verify_physical_first_mirror_values.py \
    --endpoint "$endpoint" --caps "/tmp/plasma-n153-$endpoint.json" \
    --incoming /tmp/plasma-opposite-incoming-full.json \
    --output "/tmp/plasma-physical-area-$endpoint-full.json"
done
```

| Opposite label | Exterior caps and original row geometry | Full ordered signs and original-passage implication |
| --- | --- | --- |
| q1r456 | `bef8bb5dd27abf2c13168f2ca5addffa705afa384b7e1ec3c74ed9032f2b7ab4` | `cfd9d78f41c847114d4d252a3b215341b514888ac420c2882b8809766c08a9da` |
| q1r464 | `c24746690864e145eb24259d29379febfeb1fc5f09d217dd6ca0d3c9b1feec89` | `6658602cc8d2194a53d55d594d517380739c3ce7e4d38d4bd86b6cfe90c99c88` |
| q1r509 | `18b3b9d18f86829a63a428feaa04ec5dd97fa19f84cc6f3831601a9955583a01` | `945fd3044836d6cdfbc30a2cfd969c9637855b31b36646cf9f17ccb393c6019d` |
| q1r517 | `7d301c77cb933f27258981d8f5a0bb7811cb7d9389f7fb4dc412e2c9e19a4746` | `a5746c8704ce9b01d9e22e356fb8af7fd5730d046300ab878b5ed7b32112bc40` |

All four complete sign implications and the eight direction-specific geometry and high-cap modules were audited. Each reports the three standard axioms. The original signed position archives are read directly by the producer and kernel-evaluated against the spatial enclosure.
