# Excluding earlier mirrors at the second phase-zero launch

At launch radius $239/500$, the physical QA2R field has magnitude strictly below $h_L=5297961656084411/5000000000000000$ on **every point of both signed physical output tubes** for all 317 closed slabs from the section to $317/64$. The backward clock is outward displacement, so that branch evaluates the field at azimuth $-t$. The result covers 634 directed slabs, including their common endpoints. [Ordered exclusion verifier](../../scripts/dommaschk_kam/verify_grouped_mirror_exclusion.py)

The signed physical chain from the actual nested-torus birth gives a second conclusion. For every admitted phase, the birth's physical approach reaches one section field line, and that same line stays below $h_L$ on the closed signed angular interval $[-1,1]$. This proof identifies the archived incoming state and the actual 64 rows in each direction. [Birth-to-submirror verifier](../../scripts/dommaschk_kam/verify_secondary_submirror_birth.py)

| Result | Audited proof key |
| --- | --- |
| Ordered 317-row exclusion, both directions | `5c345460e6954cd93314245beaabae3c365205cff01f4beb22d720f0e2d0b738` |
| Physical chains, 64 slabs each way | `292dba86aec96f2f812d81b305d239566f373941292ca7062f52c5fa91473154` |
| Matching 64-row signed exclusion lists | `71892ea6a26f2936ac2ff70732ea8648163db63da554eec006da2b124acd4d4c` |
| Actual birth and submirror segment, `DommaschkQ0R478SubmirrorBirth064.from_birth` | `d5dbcaa27b47b334cd643cb146b53b08433e212e27b5cd910a4f1e76a9d148bd` |

## A shared time coordinate

For a group containing rows $a,\ldots,b-1$, define $w=(128t-a-b)/(b-a)$. On row $j$ the original normalized clock is $s=128t-2j-1$, giving

\[
w=\frac{2j+1-a-b}{b-a}+\frac{s}{b-a}.
\]

The centre row proposes polynomials in $w$ for the radius, height, cosine and sine. On every constituent row, Lean substitutes the exact affine expression for $w$, subtracts the original polynomial in $s$, and charges the sum of the absolute coefficient differences plus the row's original error. Each signed row keeps its own outgoing coordinate error. The resulting polynomials enclose all four physical values at the same azimuthal displacement. This preserves correlations that separate coordinate and angle intervals lose near the mirror. [Clock and enclosure theorem](../../PlasmaLean/Design/DommaschkGroupedMirrorModels.lean)

One exact evaluation of the three sparse field polynomials and the factored gap $R^{16}(|B|^2-h_L^2)$ serves a whole group. Twenty groups cover rows 0 through 315. On row 316, one time slab still needs two radial pieces, which jointly cover the complete output tube. Thus 22 grouped field evaluations suffice for the 634 directed slabs. Both branches use the same physical norm after the known section-zero reflection. N-115 brackets the lower contact just beyond this exclusion interval; a through-birth first contact requires the trajectory to reach the crossing row. [Local crossing and slope certificates](secondary-qa2r-mirror-brackets.md)

## Archived group proofs

Each key checks all outgoing boxes in both directions for the inclusive row range shown.

| Rows | Field evaluations | Complete signed row-group key |
| --- | --- | --- |
| 0–18 | 1 | `98b46cc94357c559468f472d4672b5db47d431466432b5a1b3531b9ebb369637` |
| 19–38 | 1 | `def4bc9f79c8be6f963a9ffb61be7b42aa23ae2732c79367f341e0234c6e790f` |
| 39–58 | 1 | `2f27f54ae3cff42c1daa019378b804004638bdc48b967f62121166c324e09731` |
| 59–78 | 1 | `8b3db8bc35d8ace4fba745c741c1c3931a62509edea5667f2beb92b16906ac28` |
| 79–97 | 1 | `5ce659a74e3679b263c17c3f3127a0b5d935837481de08e079b265390404a933` |
| 98–117 | 1 | `1b35160b9971ad9f19a33e08cc71160da94c71dc8adecf5916136775a4c2ea51` |
| 118–137 | 1 | `d878cf9509a692843a5c74bc7889b8af689f00419b49cd65e8be57f0becd0834` |
| 138–157 | 1 | `310746a5fee81b6a72a07b1e9877bfe264c49800b63a30f456e4b515bd579116` |
| 158–176 | 1 | `f8f1cb3ead693cfb2a44a0bcc4ae12029a6e7d7aca9e9fa069d416d8c9dcf222` |
| 177–196 | 1 | `a285a862146ab42d00f1a564f6872c2611e52d53e384bef2d49a713e9feb1902` |
| 197–216 | 1 | `61ae36b70b362d40f08815bbd18b15372387e2f4d5c52ef68a8e4a3ad57aa720` |
| 217–236 | 1 | `3e31f74e98dc6e80aad554148831ea092bb9360c56bacb8347f9ca3934a43378` |
| 237–256 | 1 | `c81cdd63a3e0ffa0b1fbb052eeb016a6154de2e8e58d44da7a3835613741d07a` |
| 257–276 | 1 | `ce6c408ded1abae54bfd7de095fabf17f9823d902a9aed6aed16390693cd7183` |
| 277–296 | 1 | `2ef134e98df794566bbd912fbbbc53364cea91bfa38b40148b696a96f48be4c4` |
| 297–306 | 1 | `f1c9f354223c14cc6cbb23377c854074ae2c9c1740287f9765bbc0a391c85de1` |
| 307–311 | 1 | `46e7c4f662ad15a63ee7154532479de8117794f7dcd8fc916d78b0c1987f31de` |
| 312–313 | 1 | `d39d67f0e381951fb3a62fb19625542d00a08f9fd5e12efd0d6c873593b8e411` |
| 314 | 1 | `7a210c4a33c3d599678a192ef9a35aa940c5441695dd72286ab84941c0486cfa` |
| 315 | 1 | `96070dab12bb5b766e2ca43060ee52e5dfae523588b8b1aaaa69614c301322ce` |
| 316 | 2 | `658b7091c219d18fa76aa880b43abf977d2770ffb2c7b749ea1c746a424de460` |

## Reproduction

```sh
lake build PlasmaLean.Design.DommaschkGroupedMirrorModels PlasmaLean.Design.DommaschkEndpointMirrorBranch PlasmaLean.Design.DommaschkStoredPowers
for i in $(seq -w 0 39); do lake build "PlasmaLean.Design.DommaschkHarmonicBlock$i"; done
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_mirror_exclusion.py --workers 4 --output /tmp/plasma-q0r478-grouped-exclusion.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_mirror_exclusion.py --prefix-length 64 --output /tmp/plasma-q0r478-early064.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_submirror_birth.py --signed .lake/secondary-trace-campaign/q0r478/prefixes/064.json --exclusion /tmp/plasma-q0r478-early064.json --output /tmp/plasma-q0r478-submirror-birth064.json
```

The q0r478 input packet has SHA-256 `07763b1926fb24bb93889e651ced079f4871c59c72f443f6b7f2392fc5eb6f83`. Each ordered manifest records every participating group key. The signed physical campaign supplies the separately authenticated propagation manifest at the indicated length. [Physical campaign driver](../../scripts/dommaschk_kam/verify_endpoint_trace_campaign.py) · [Input packet](../../scripts/dommaschk_kam/results/bounce_frame_q0_u478.json.gz)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-121 |
| Kind | Complete signed submirror exclusion with physical birth application |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-84, N-91, N-102, N-115 |
| Dependency requirement | Exact QA2R field, genuine harmonic clock, archived moving spatial tubes, actual matched signed chains for the through-birth statement |
| Produces | 317 consecutive below-height bounds each way and an actual two-sided submirror segment on every admitted birth path |
| Status | Complete ordered exclusion through $317/64$ on both signed tube lists. Physical birth and submirror segment proved through $[-1,1]$. |
| Lean evidence | `DommaschkGroupedMirrorModels.Covers.below`, `DommaschkQ0R478SubmirrorPrefix317.{fwd,back}_below`, `DommaschkQ0R478SubmirrorBirth064.from_birth` |
| Audit evidence | The physical and aggregate theorems use only `propext`, `Classical.choice` and `Quot.sound`. Lean rejected a negative test that changed row zero's group-clock offset from $-18/19$ to zero. |
| Last updated | 25 November 2026 |
