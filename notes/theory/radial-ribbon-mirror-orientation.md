# Outward orientation of both mirror collars across the radial bracket

At the upper archive height, all four phase-zero radial ribbons have **strictly increasing squared field strength on both outward clocks** throughout $[317/64,331/64]$. For every true field solution inside each original signed position tube, the derivative with respect to outward elapsed azimuth exceeds $1/16384$. Lean checked all 112 signed tubes in this collar, including the 70 tubes which the original screen marked as possible upper-height contacts. The strict estimate covers slab seams when the joined ODE gives the ordinary derivative there. The first eight signed position slabs at each tile are also strictly below the upper height, including the common section at time zero. [Physical derivative theorem](../../PlasmaLean/Design/DommaschkRibbonSlopeCover.lean) · [Original row attachment](../../scripts/dommaschk_kam/verify_radial_ribbon_orientation.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-172 |
| Kind | Certified continuum field estimate on the four widened radial ribbons |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-167, N-169 and the signed field-slope, reflected-clock and harmonic Horner libraries |
| Dependency requirement | Upper-height coverage of the true position tubes, including both clocks, plus an actual signed ODE passage to draw a conclusion about both first mirrors of the original birth. |
| Produces | Uniform positive squared-strength derivative on 112 signed original tubes, early strict signs, and a reusable theorem excluding grazing in a joined upper-height first well. |
| Status | The full collar and short eight-row signed histories are kernel verified. Additional incoming groups were independently verified to row 138 on every clock at this checkpoint. The full 317-row early sign and the through-mirror ODE from the original births were pending at this checkpoint. |
| Lean evidence | `DommaschkCompensatedMirrorSlope.numerator_eq`, `DommaschkRibbonSlopeCover.slope`, `DommaschkRibbonFirstMirrors.no_grazing`, `NoGrazing.well_slopes` and `NoGrazing.excludes_localMax`. |
| Audit evidence | The generic and concrete proof declarations use only the standard Lean axioms. The proof records authenticate the original packet and every generated Lean module. |
| Last updated | 25 November 2026 |

## Why the derivative calculation changed

Write the physical field-line equations as $dR/dφ=N/D$ and $dz/dφ=Z/D$. The toroidal component is $D/R^7$. The earlier expression for the derivative of $|B|^2$ subtracts quantities whose leading radial terms cancel. For tile zero, row 324, its separate interval estimates gave an unenclosed sign for the derivative numerator, approximately $[-0.0015052,0.0025708]$. Differentiating $D/R^7$ first identifies the polynomial $L=R\,∂_R D-7D$. Combining its like powers of $R-29/32$ exactly cancels the leading radial power. [Compensated derivative identity](../../PlasmaLean/Design/DommaschkCompensatedMirrorSlope.lean)

For the material derivative $M(P)=N\,∂_R P+Z\,∂_z P+D\,∂_φ P$, set $T=N L+R(Z\,∂_z D+D\,∂_φ D)$. The squared-strength derivative on the forward clock has numerator
$$
2\{R^2DT+R[NM(N)+ZM(Z)]\}-16N(N^2+Z^2)
$$
and denominator $R^{17}D$. Twelve exact Fourier tables represent $D,N,Z$ and the necessary spatial, angular and compensated derivatives. Each table's expansion equals its physical sparse polynomial in Lean. The time argument $2φ$ is the common doubled fundamental angle. Reflection converts the backward ODE to the same forward formula, including the change $z\mapsto-z$. [Exact Fourier and Taylor verifier](../../scripts/dommaschk_kam/verify_radial_ribbon_slopes.py)

Eight Taylor enclosures suffice. Each covers either tiles $0,1$ or tiles $2,3$ over four adjacent intervals of slab indices with boundaries $317,324,327,329,331$. Every original row keeps its own polynomial, output radius and angular subinterval. A coefficient comparison bounds the discrepancy from the common model after the affine change of clock. The smallest certified numerator surplus over $(1/16384)R^{17}D$ exceeds $0.0000317497$; every denominator is strictly positive. Thus all 70 candidate slabs and 42 neighboring slabs have the asserted orientation.

## Passage to first contacts

Let $y(t)$ be a signed QA2R field line, and let $f(t)=\lVert B(R(t),t,z(t))\rVert$. If it reaches both upper exterior caps, stays at positive radius, satisfies the true field-line ODE, remains below $h_U$ through $|t|≤317/64$, and tracks the certified slope collar, the first upper-height encounter on each clock lies strictly between $317/64$ and $331/64$. It is unique within that collar. At either first hit the outward derivative of the field strength itself is greater than $1/(32768h_U)$. All signed contacts inside the open cap interval have negative physical-time derivative on the left and positive physical-time derivative on the right. This rules out the local-maximum alternative in first-well continuation at a fixed height. A connected through-birth family and the endpoint action bracket enter separately in a prescribed-action application. [First-mirror theorem](../../PlasmaLean/Design/DommaschkRibbonFirstMirrors.lean) · [Well endpoint and local-maximum theorem](../../PlasmaLean/Design/DommaschkRibbonGrazingAlternative.lean)

The incoming checker subtracts $h_U R^7$ from $D$ in the original polynomial coefficients and bounds the signed gap $R^{16}(|B|^2-h_U^2)$. One model covers all four tiles and both clock directions in each group. The short result uses the actual input `Tracks forwardRows backwardRows 8 y`, so an eight-step physical passage directly supplies its hypotheses. [Incoming signs](../../scripts/dommaschk_kam/verify_radial_ribbon_incoming.py)

## Reproduction

The original four-ribbon archive has SHA-256 `c4f65ab5d7727fc5fdbae645c6924ecde6b474f521663a8b1b9de6be8d45a486`. Generate it and its canonical packet receipt as in N-169. All commands below are single-worker runs. Both temporal endpoints of each stored derivative row are included.

```sh
export OPENBLAS_NUM_THREADS=1 LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkRibbonGrazingAlternative
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
r=/tmp/plasma-n169-four-ribbons.json
packets=/tmp/plasma-n169-packets.json
"$py" "$dir/verify_radial_ribbon_slopes.py" --ribbon "$r" --output /tmp/plasma-n172-all-slopes.json
"$py" "$dir/verify_radial_ribbon_incoming.py" --ribbon "$r" --groups 0 --output /tmp/plasma-n172-first-gap.json
for k in 0 1 2 3
do
  "$py" "$dir/verify_radial_ribbon_orientation.py" --mode below --ribbon "$r" --packets "$packets" \
    --estimate /tmp/plasma-n172-first-gap.json --tile "$k" --start 0 --short-prefix 8 \
    --output "/tmp/plasma-n172-birthsign-$k.json"
  for start in 317 324 327 329
  do
    "$py" "$dir/verify_radial_ribbon_orientation.py" --mode slope --ribbon "$r" --packets "$packets" \
      --estimate /tmp/plasma-n172-all-slopes.json --tile "$k" --start "$start" \
      --output "/tmp/plasma-n172-tile-$k-rates-$start.json"
  done
done
```

The following keys identify the four physical eight-row history theorems. Each original packet list and its stored output radii are checked by Lean. The incoming shared upper-gap theorem used in these four bindings has key `3cc637dfd055987721f4312b798215bdda50956979255a54f24b0d72de407d73`.

| Physical tile | Short signed history proof key |
| ---: | --- |
| 0 | `9e1bbc6ce0c12b282645829e9cc76ef616476a3747541d026b843108c929a857` |
| 1 | `33aa969a12a29adbd26f043e43c5d892c6bd21496ebf8af0e63116ce49cf8a89` |
| 2 | `6f0469bec0e2dc3bdc7f744685c1a7539eb72b4fa097a5c5a2a26168c1a60884` |
| 3 | `a1e6521978ea0e00909cc008488d26667b5674636df7082abff818bbd873b366` |

The sixteen tracked slope theorems below each contain both clock orientations. They directly consume `Tracks forwardRows backwardRows 332 y`. The tile packet stores 340 rows in chronological order.

| Tile | Outward slab indices | Kernel-checked signed slope theorem key |
| ---: | --- | --- |
| 0 | 317–323 | `9d660f883e638200d9787cdce81cfa2a0f80878445f29adac9042f3f70ef704a` |
| 0 | 324–326 | `f603e08ea8d6dc74d5f222d09d5628f7286536f5c4ec42cad10714ecf6cf5c38` |
| 0 | 327–328 | `73bcbef4fd71d42ea950d40ee069b1a610728d9757df83008923af8759744b31` |
| 0 | 329–330 | `18d500f0f96799b6fa0870ce7634aee16b0f2b08eb8df5e5b0d885d46d5968d0` |
| 1 | 317–323 | `eb4fbf5430c32aa8b94d5ab9499a93ec5d1a1009f273da775a4d40793cd27127` |
| 1 | 324–326 | `12641270a437ef4295e01a6bf75b8c0b59bb900efad89758c922f4b46e9210f9` |
| 1 | 327–328 | `ae8abc5ddb9b7c6525316dfaaa6267133ba2366038328348a642299be5118af2` |
| 1 | 329–330 | `79a84bf4d0e1898bcd1a76f9cf9910eaf04aa361a2a5a407e29796d2c8c7545c` |
| 2 | 317–323 | `429ca86a59345b391043aaa10048e3fd0e3a42a20648590e9091926857ae2858` |
| 2 | 324–326 | `7ba61e5e1dc2ce58eb3102e701a7e0aa0dcf168c7d734d67a09528f0ba41e0f0` |
| 2 | 327–328 | `2e9f511eac60aa9ddf70f440e6e8e4a38d15a4160e72d0ab8eb66c044a8fb70c` |
| 2 | 329–330 | `3a2ccd4f23b1ea4bdfd9cfc0ec8cf011016e2d4cfa3135e3562769cfc478fd47` |
| 3 | 317–323 | `8ea38626070d523166f93a41b232000f649afff37581b05c56d24761815b1467` |
| 3 | 324–326 | `59a74c2bbd66dee72fc3b57eeb36e5661ca1337fe7ccda1a8d383890aab045bc` |
| 3 | 327–328 | `3b662df6802f49fb596f131dd808fc3ce31062efd22aece6e710bb70f961e81b` |
| 3 | 329–330 | `e77e15340089799063e7b35e678d6600f839fd2c1073933192c4d0c9d469dc92` |
