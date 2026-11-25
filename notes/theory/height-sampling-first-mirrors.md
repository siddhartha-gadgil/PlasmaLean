# Sampling heights with two steep first mirrors

Fix an admitted original launch at the phase-zero radius $u=239/500$ and the signed QA2R field line supplied by N-164. Draw a height uniformly from the archived interval $[h_L,h_U]$. The probability that **both first mirrors** have outward field-strength derivative strictly greater than $1/1250$ is at least $667367655761/1292367655761$, or 51.6391%. Every admitted launch angle $|φ_0|≤2^{-19}$ has this guarantee. The first-contact maps and the success event may depend on that angle. [Physical height sampling](../../PlasmaLean/Design/DommaschkFirstMirrorHeightSampling.lean) · [Measured physical first mirrors](physical-first-mirror-values.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-168 |
| Kind | Probability law for first-contact slopes on a fixed field line |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-159, N-164 |
| Dependency requirement | Measurable first-contact maps on both signed clocks and a physical area bound. A change of height law also requires normalization and a bound on the density over the failed heights. |
| Produces | A certified probability under uniform height, a bound under a change of height law, and a pullback to a measurable sampling space. Exact bracket widths sharpen the conditional conclusions at the opposite section. |
| Status | Verified at the original phase-zero launch at $u=0.478$. Four opposite-section implications are verified conditional on an original through-passage to their exterior caps. |
| Lean evidence | `measurable_good_heights`, `probability_of_bad_density`, `probability_of_height_map`, `on_height_map`, `of_launch_width` and the five generated theorems below. |
| Audit evidence | Twelve reusable theorems and all five generated theorems use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## What is sampled

For one fixed trajectory, let $τ_+(h),τ_-(h)$ be the earliest outward times at which the physical strength reaches $h$. The clocks measure elapsed azimuth from the section, so their orientations differ. Let $G$ consist of those heights where both derivatives with respect to outward elapsed azimuth exceed $1/1250$. Each first-contact time is strictly increasing with the height. Its composition with the Borel-measurable derivative gives a measurable slope observation, even if the first-contact map jumps. Including the closed band into the real line preserves measurability. [First-mirror height distributions](../../PlasmaLean/Theory/Kinetic/FirstMirrorHeightDistribution.lean)

The band width is $Δ=1292367655761/2500000000000000$. Normalizing Lebesgue measure on the band gives a probability measure $μ$. The area estimate for two first-contact brackets of widths $w_+,w_-$ yields
$$
μ(G)\;≥\;1-\frac{w_++w_-}{1250Δ}.
$$
At the original phase-zero launch the signed ODE already reaches both caps. On the opposite section the complete ordered signs and regular position boxes are available on each of the following pairs of brackets. The stated implication requires a physical signed trajectory whose rows agree with these archives through both caps.

| Section | Radius | Each outward bracket | Maximum discarded height measure | Uniform-height probability lower bound | Physical scope |
| --- | ---: | --- | --- | --- | --- |
| $0$ | 0.478 | $(317/64,327/64)$ | $1/4000$ | $667367655761/1292367655761$ (51.6391%) | Established through the original birth |
| $π/2$ | 0.456 | $(320/64,328/64)$ | $1/5000$ | $792367655761/1292367655761$ (61.3113%) | Requires the two-sided through-passage |
| $π/2$ | 0.464 | $(321/64,329/64)$ | $1/5000$ | $792367655761/1292367655761$ (61.3113%) | Requires the two-sided through-passage |
| $π/2$ | 0.509 | $(326/64,335/64)$ | $9/40000$ | $243289218587/430789218587$ (56.4752%) | Requires the two-sided through-passage |
| $π/2$ | 0.517 | $(326/64,336/64)$ | $1/4000$ | $667367655761/1292367655761$ (51.6391%) | Requires the two-sided through-passage |

## Changing the height law

Suppose $μ(G)≥p$ and $ν$ is another probability with density $ρ$ relative to $μ$. If $ρ≤C$ almost everywhere on $G^c$, then $ν(G)≥\max(0,1-C(1-p))$. This follows by integrating the density on the failed heights. A bound on $ρ$ on the successful heights is unnecessary. At the grounded phase-zero launch a factor of two gives the exact lower bound $42367655761/1292367655761$, or 3.27829% rounded down.

If a preselected measured sample space $(X,λ)$ supplies heights by a measurable rule $H$, and $H_*λ=μ$ or $ν$, the corresponding lower bound holds for $λ(H^{-1}(G))$. Here all sampled heights refer to the same physical line. For an uncontrolled singular law, an atom at a failed height assigns zero probability to success. An application to a thermal birth population would also require its joint law of lines and heights, its energy and pitch distribution, and the dynamical excursion and duration entering C2. [Measured-family and change-of-law theorems](../../PlasmaLean/Theory/Kinetic/FirstMirrorHeightDistribution.lean)

## Reproduction

First produce the five N-164 receipts using the commands in that note. The following commands use one Lean worker. The opposite-section mode checks the exact cap rows, the preceding passage implication and its quantitative width. The original-birth mode requires a completed physical passage with the original interpolated position. A test passing a conditional opposite receipt to original-birth mode was rejected before compilation. [Sampling verifier](../../scripts/dommaschk_kam/verify_physical_mirror_sampling.py) · [N-164 receipts](physical-first-mirror-values.md)

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkFirstMirrorHeightSampling
.venv-ws/bin/python scripts/dommaschk_kam/verify_physical_mirror_sampling.py \
  --area /tmp/plasma-physical-area-q0r478.json --output /tmp/plasma-physical-sampling-q0r478.json
for label in q1r456 q1r464 q1r509 q1r517
do
  .venv-ws/bin/python scripts/dommaschk_kam/verify_physical_mirror_sampling.py \
    --from-passage --area "/tmp/plasma-physical-area-$label-full.json" \
    --output "/tmp/plasma-physical-sampling-$label-full.json"
done
```

| Label | Theorem | Proof key |
| --- | --- | --- |
| q0r478 | `DommaschkFirstMirrorSamplingQ0R478On391_328_48_16_48_16_8_5.original_birth_probability` | `5b5e0467f9babcaabc565b8c2f7d346b5bb19fde523d6ffe9e580252e2600259` |
| q1r456 | `DommaschkFirstMirrorSamplingQ1R456AtCaps.probability_from_passage` | `90c832a7531c3300f6f96b19528cb2eb5d1434936cc2c1b92c186a4edf991abb` |
| q1r464 | `DommaschkFirstMirrorSamplingQ1R464AtCaps.probability_from_passage` | `d5850aac4ef9096af68df35748559117e5e9b6d96ac074b2b32268104b99ebf9` |
| q1r509 | `DommaschkFirstMirrorSamplingQ1R509AtCaps.probability_from_passage` | `dbfa00c9a11ddd7cd0ff187edbf23f0800100c4d76eb63597d826facf5002b49` |
| q1r517 | `DommaschkFirstMirrorSamplingQ1R517AtCaps.probability_from_passage` | `4c6219142fe7cf8185c9d6495d435591fef7de83d7694cf53ad4e00e57a30324` |

The grounded original-birth replay took 20.46 seconds and peaked at 23.74 GiB. Each opposite conditional replay took under four seconds and peaked below 4.80 GiB. The source and compiled products for each replay are content-addressed.
